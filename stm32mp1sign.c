// SPDX-License-Identifier: GPL-2.0+ OR BSD-3-Clause
/*
 * Copyright (C) 2022, Christian Melki
 *
 * Functional contribution list:
 * Conny Sjaunja 2023, ECDSA verification.
 *
 * Version history:
 * 1.0: First release.
 * 1.1: Some polishing.
 * 1.2: Added verification.
 * 1.3: Add simple pubkey hash file creation.
 */

#define _DEFAULT_SOURCE
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <getopt.h>
#include <errno.h>
#include <endian.h>
#include <libgen.h>

#include <sys/mman.h>
#include <sys/random.h>
#include <fcntl.h>

/* Usage of deprecated functions.
 * Want this to build with older openssl.
 * Don't require 3.0+ functions.
 */
#define OPENSSL_API_COMPAT 0x10101000L
#include <openssl/opensslv.h>
#include <openssl/ecdsa.h>
#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/bn.h>
#include <openssl/obj_mac.h>

#include "config.h"

#define UNUSED                          __attribute__((unused))
#define HEADER_MAGIC                    "STM2"
/* The ec pubkeys for allowed curves are 65 bytes.
 * 1 byte describing format and 2*32 byte,
 * x concatenated y points in an ecsig struct.
 */
#define EC_POINT_UNCOMPRESSED_LEN       65
/* The CPU hashes header from offset 0x48,
 * ie. from member header_version and all of the data.
 */
#define STM32_HASH_OFFSET               offsetof(struct stm32_header_v1, header_version)

/* The stm32 header is often defined to be 0x100 bytes.
 * However, some implementations carry a padding of
 * uint32_t x[83/4] (?!?).
 * Other definitions do uint8_t x[83] (like this one).
 * Also add packed, which seems to be missing in
 * a lot of implementations in the wild.
 */

static uint8_t hashes[8 * 32] = { 0 };

struct __attribute((packed)) stm32_header_v1 {
        uint32_t magic_number;
        uint8_t image_signature[64];
        uint32_t image_checksum;
        uint8_t  header_version[4];
        uint32_t image_length;
        uint32_t image_entry_point;
        uint32_t reserved1;
        uint32_t load_address;
        uint32_t reserved2;
        uint32_t version_number;

        /* V1.0 specific content */
        uint32_t option_flags;
        uint32_t ecdsa_algorithm;
        uint8_t ecdsa_public_key[64];
        uint8_t padding[83];
        uint8_t binary_type;
};

struct __attribute((packed)) stm32_header_v2 {
        uint32_t magic_number;
        uint8_t image_signature[64];
        uint32_t image_checksum;
        uint8_t  header_version[4];
        uint32_t image_length;
        uint32_t image_entry_point;
        uint32_t reserved1;
        uint32_t load_address;
        uint32_t reserved2;
        uint32_t version_number;

        /* V2.0 specific content */
        uint32_t extension_flags;
        uint32_t extension_headers_length;
        uint32_t binary_type;
        uint8_t padding[16];

        uint32_t extension_header_type;
        uint32_t extension_header_length;
        uint32_t public_key_index;
        uint32_t public_key_count;
        uint32_t public_key_algo;
        uint8_t ecdsa_public_key[64];
        uint8_t ecdsa_public_key_hash[8 * 32];

        uint32_t extension_header_type1;
        uint32_t extension_header_length1;
        uint8_t extension_padding[36];
};

static void
usage(char *argv[])
{
        printf("%s usage:\n", argv[0]);
        printf("---------------------\n");
        printf("%s --image <file> --key <file> --sign [--password <string>] [--hashes pkh01.bin:..:pkh07.bin]\n", argv[0]);
        printf("%s --image <file> --key <file> --verify\n", argv[0]);
        printf("%s --help\n", argv[0]);
        printf("where:\n");
        printf("--image       ; Path to stm32image file.\n");
        printf("--key         ; Path to the key used.\n");
        printf("              ; The only allowed EC curves are: prime256v1, brainpoolP256r1\n");
        printf("              ; Contains private and public key when signing.\n");
        printf("              ; Contains the public key when verifying.\n");
        printf("--sign        ; Sign the stm32image.\n");
        printf("--verify      ; Verify the stm32image.\n");
        printf("--password    ; Not mandatory. Contains private key password. Used when signing.\n");
        printf("              ; If not used, program will ask interactively.\n");
        printf("--pubhash     ; Not mandatory. If used then the raw ec point hash of the public key\n");
        printf("              ; will be overwritten to the current dir + pubkey.hash filename.\n");
        printf("--hashes      ; Mandatory for STM32MP2 image, list of publicKeyHash0*.bin separate by colon.\n");
        printf("--version     ; %s version.\n", argv[0]);
        printf("--help        ; This help.\n");
}

static unsigned char *
stm32image_load(int fd, off_t *len, bool v2)
{
        off_t hlen = v2 ? sizeof(struct stm32_header_v2) : sizeof(struct stm32_header_v1);
        unsigned char padbytes[32] = { 0 };
        unsigned char *data;
        ssize_t ret, pad = 0;

        if (fd < 0 || !len) {
                fprintf(stderr, "Invalid input.\n");
                goto err_out;
        }

        if ((*len = lseek(fd, 0, SEEK_END)) == (off_t)-1) {
                fprintf(stderr, "Cannot seek to end.\n");
                goto err_out;
        }

        if (*len <= hlen) {
                fprintf(stderr, "Image file too small for stm32 header.\n");
                goto err_out;
        }

        if (v2 && (*len % 32)) {
                /* Image v2 must be padded to 32 Bytes */
                pad = 32 - (*len % 32);
                ret = write(fd, padbytes, pad);
                if (ret != pad) {
                        fprintf(stderr, "Image file padding to 32 Bytes failed.\n");
                        goto err_out;
                }
                *len += pad;
        }

        if (lseek(fd, 0, SEEK_SET) == (off_t)-1) {
                fprintf(stderr, "Cannot seek to start.\n");
                goto err_out;
        }
        if ((data = mmap(NULL, *len, PROT_READ | PROT_WRITE,
                         MAP_SHARED | MAP_POPULATE, fd, 0)) == MAP_FAILED) {
                fprintf(stderr, "mmap failed: %s\n", strerror(errno));
                goto err_out;
        }
        /* Not overly rigorous checks.
         * Assuming header was generated by something sane already.
         */
        if (memcmp(data, HEADER_MAGIC, strlen(HEADER_MAGIC))) {
                fprintf(stderr, "Invalid stm32 header magic.\n");
                goto err_out;
        }

        return data;

 err_out:
        if (len) *len = 0;
        return NULL;
}

static int
openssl_pw_cb(char *buf, int size, int rwflag UNUSED, void *u UNUSED)
{
        int len;
        char *passwd;

        passwd = getpass("stm32mp1sign. Privkey password: ");
        len = strlen(passwd);
        if (len <= 0 || len > size) {
                return 0;
        }
        memcpy(buf, passwd, len);

        return len;
}

static EC_KEY *
openssl_load_key(const char *key_path, char *pw, bool privkey)
{
        BIO *bio_key = NULL;
        EVP_PKEY *key = NULL;
        EC_KEY *eckey = NULL;

        if (!key_path || !key_path[0]) {
                fprintf(stderr, "Invalid input.\n");
                goto err_out;
        }

        if (!(bio_key = BIO_new_file(key_path, "r"))) {
                fprintf(stderr, "Unable to load key %s.\n", key_path);
                goto err_out;
        }
        if (privkey) {
                key = PEM_read_bio_PrivateKey(bio_key, NULL,
                                              pw ? NULL : openssl_pw_cb,
                                              pw ? pw : NULL);
        } else {
                key = PEM_read_bio_PUBKEY(bio_key, NULL,
                                          NULL,
                                          NULL);
        }
        if (!key) {
                fprintf(stderr, "Unable to load key %s.\n",
                        key_path);
                goto err_out;
        }
        if (!(eckey = EVP_PKEY_get1_EC_KEY(key))) {
                fprintf(stderr, "Unable to get EC key.\n");
                goto err_out;
        }

        if (key) EVP_PKEY_free(key);
        if (bio_key) BIO_free(bio_key);
        return eckey;

 err_out:
        if (key) EVP_PKEY_free(key);
        if (bio_key) BIO_free(bio_key);
        return NULL;
}

static uint8_t *
openssl_get_pubkey(EC_KEY *eckey, size_t *len, int *alg)
{
        int nid = 0;
        BN_CTX *ctx = NULL;
        const EC_POINT *public_key = NULL;
        const EC_GROUP *group = NULL;
        uint8_t *buffer = NULL;

        if (!eckey || !len | !alg) {
                fprintf(stderr, "Invalid input.\n");
                goto err_out;
        }

        if (!(public_key = EC_KEY_get0_public_key(eckey))) {
                fprintf(stderr, "Unable to get EC pubkey.\n");
                goto err_out;
        }
        if (!(group = EC_KEY_get0_group(eckey))) {
                fprintf(stderr, "Unable to get EC group.\n");
                goto err_out;
        }
        if (!EC_GROUP_get_asn1_flag(group)) {
                fprintf(stderr, "Unable to get EC parameters.\n");
                goto err_out;
        }
        /* Only allow these curves */
        nid = EC_GROUP_get_curve_name(group);
        if (nid == NID_X9_62_prime256v1) {
                *alg = 1;
        } else if (nid == NID_brainpoolP256r1) {
                *alg = 2;
        } else {
                fprintf(stderr, "Invalid EC curve in use.\n");
                goto err_out;
        }
        if (!(ctx = BN_CTX_new())) {
                fprintf(stderr, "Unable to allocate bignum context.\n");
                goto err_out;
        }
        /* Use point2oct twice.
         * Get length, allocate storage, repeat to get contents.
         */
        if (!(*len = EC_POINT_point2oct(group, public_key,
                                        EC_KEY_get_conv_form(eckey), NULL,
                                        0, ctx))) {
                fprintf(stderr, "Unable to get EC pubkey length.\n");
                goto err_out;
        }
        if (!(buffer = OPENSSL_malloc(*len))) {
                fprintf(stderr, "Unable to allocate pubkey buffer.\n");
                goto err_out;
        }
        if (!(*len = EC_POINT_point2oct(group, public_key,
                                        EC_KEY_get_conv_form(eckey), buffer,
                                        *len, ctx))) {
                fprintf(stderr, "Unable to get EC pubkey length.\n");
                goto err_out;
        }

        if (ctx) BN_CTX_free(ctx);
        return buffer;

 err_out:
        if (ctx) BN_CTX_free(ctx);
        if (len) *len = 0;
        if (alg) *alg = 0;
        return NULL;
}

static ECDSA_SIG *
openssl_do_ecdsa_sha256_sign(EC_KEY *eckey, bool v2,
                             unsigned char *data, unsigned long datalen)
{
        unsigned char md[SHA256_DIGEST_LENGTH];
        ECDSA_SIG *ecsig = NULL;
        SHA256_CTX c;
        int ret;

        if (!eckey || !data || !datalen) {
                fprintf(stderr, "Invalid input.\n");
                goto err_out;
        }

        ret = SHA256_Init(&c);
        if (!ret) {
                fprintf(stderr, "Failed to initialize SHA256.\n");
                goto err_out;
        }

        if (v2) {
                /*
                 * Handle special hole in v2 image base header, see
                 * comment below regarding ST wiki explains this in
                 * https://wiki.st.com/stm32mpu/wiki/STM32_header_for_binary_files#On_STM32MP23x_lines_and_STM32MP25x_lines
                 */
                ret = SHA256_Update(&c, data, 0x30);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 base header.\n");
                        goto err_out;
                }

                ret = SHA256_Update(&c, data + 0x38, datalen - 0x30);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 rest.\n");
                        goto err_out;
                }
        } else {
                ret = SHA256_Update(&c, data, datalen);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 data.\n");
                        goto err_out;
                }
        }

        ret = SHA256_Final(md, &c);
        if (!ret) {
                fprintf(stderr, "Failed to finalize SHA256.\n");
                goto err_out;
        }

        if (!(ecsig = ECDSA_do_sign(md, SHA256_DIGEST_LENGTH, eckey))) {
                fprintf(stderr, "Unable to generate ECDSA signature.\n");
                goto err_out;
        }

        return ecsig;

 err_out:
        return NULL;
}

static ECDSA_SIG *
openssl_do_ecdsa_sha256_verify(ECDSA_SIG *ecsig, EC_KEY *eckey, bool v2,
                               unsigned char *data, unsigned long datalen)
{
        unsigned char md[SHA256_DIGEST_LENGTH];
        SHA256_CTX c;
        int ret;

        if (!ecsig || !eckey || !data || !datalen) {
                fprintf(stderr, "Invalid input.\n");
                goto err_out;
        }

        ret = SHA256_Init(&c);
        if (!ret) {
                fprintf(stderr, "Failed to initialize SHA256.\n");
                goto err_out;
        }

        if (v2) {
                /*
                 * Handle special hole in v2 image base header, see
                 * comment below regarding ST wiki explains this in
                 * https://wiki.st.com/stm32mpu/wiki/STM32_header_for_binary_files#On_STM32MP23x_lines_and_STM32MP25x_lines
                 */
                ret = SHA256_Update(&c, data, 0x30);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 base header.\n");
                        goto err_out;
                }

                ret = SHA256_Update(&c, data + 0x38, datalen - 0x30);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 rest.\n");
                        goto err_out;
                }
        } else {
                ret = SHA256_Update(&c, data, datalen);
                if (!ret) {
                        fprintf(stderr, "Failed to SHA256 data.\n");
                        goto err_out;
                }
        }

        ret = SHA256_Final(md, &c);
        if (!ret) {
                fprintf(stderr, "Failed to finalize SHA256.\n");
                goto err_out;
        }

        if (!(ECDSA_do_verify(md, SHA256_DIGEST_LENGTH, ecsig, eckey))) {
                fprintf(stderr, "Unable to verify ECDSA signature.\n");
                goto err_out;
        }

        return ecsig;

 err_out:
        return NULL;
}

int
main(int argc, char *argv[])
{
        struct stm32_header_v1 *h = NULL;
        struct stm32_header_v2 *h2 = NULL;
        FILE *fp = NULL;
        unsigned char *p;
        char *key_path = NULL;
        char *password = NULL;
        EC_KEY *eckey = NULL;
        ECDSA_SIG *ecsig = NULL;
        unsigned char *data = NULL;
        off_t datalen, signlen;
        uint8_t *buf = NULL;
        size_t len;
        int alg, c, fd = -1;
        bool sign = false, verify = false, pubhash = false;
        int tokfd, tokc = 0;
        int v2 = 0;

        static struct option options[] = {
                {"image", required_argument, 0, 'i'},
                {"key", required_argument, 0, 'k'},
                {"sign", no_argument, 0, 's'},
                {"verify", no_argument, 0, 'v'},
                {"password", required_argument, 0, 'p'},
                {"pubhash", no_argument, 0, 'x'},
                {"hashes", required_argument, 0, 'H'},
                {"version", no_argument, 0, 'V'},
                {"help", no_argument, 0, 'h'},
                {0, 0, 0, 0}
        };

        /* Prevent pages from reaching swap.
         * Contains sensitive data.
         */
        if (mlockall(MCL_CURRENT | MCL_FUTURE)) {
                fprintf(stderr,
                        "Warn: Failed protecting memory from being swapped.\n");
        }
        while (1) {
                c = getopt_long(argc, argv, "i:svk:p:xhV", options, NULL);
                if (c == -1)
                        break;
                switch (c) {
                case 'i':
                        fd = open(optarg, O_RDWR);
                        if (fd < 0) {
                                fprintf(stderr,
                                        "Error: Cannot open %s: %s\n",
                                        optarg, strerror(errno));
                                goto err_out;
                        }
                        break;
                case 'k':
                        key_path = strdup(optarg);
                        break;
                case 's':
                        sign = true;
                        break;
                case 'v':
                        verify = true;
                        break;
                case 'p':
                        password = strdup(optarg);
                        break;
                case 'x':
                        pubhash = true;
                        break;
                case 'H':
                        for (char *tok = strtok(strdup(optarg), ":"); tok != NULL; tok = strtok(NULL, ":")) {
                                tokfd = open(tok, O_RDONLY);
                                if (!tokfd) {
                                        fprintf(stderr,
                                                "Error: Cannot open %s: %s\n",
                                                tok, strerror(errno));
                                        usage(argv);
                                        goto err_out;
                                }
                                int ret = read(tokfd, &(hashes[tokc]), 32);
                                if (ret != 32) {
                                        fprintf(stderr,
                                                "Error: Cannot read %s: %s\n",
                                                tok, strerror(errno));
                                        usage(argv);
                                        goto err_out;
                                }
                                tokc += 32;
                                close(tokfd);
                        }
                        v2 = 1;
                        break;
                case 'V':
                        fprintf(stderr, "Version: %s\n", PACKAGE_VERSION);
                        goto err_out;
                        break;
                case 'h':
                        usage(argv);
                        goto err_out;
                        break;
                default:
                        fprintf(stderr, "%s: unknown option\n", argv[0]);
                        usage(argv);
                        goto err_out;
                        break;
                }
        }

        if (sign == verify) {
                fprintf(stderr, "%s: Op must be either sign or verify.\n",
                        argv[0]);
                usage(argv);
                goto err_out;
        }

        if (fd < 0) {
                fprintf(stderr, "%s: Missing stm32 image file.\n",
                        argv[0]);
                usage(argv);
                goto err_out;
        }

        if (!key_path) {
                fprintf(stderr, "%s: Missing key path or password.\n",
                        argv[0]);
                usage(argv);
                goto err_out;
        }

        /* Load and validate image magic. */
        if (!(data = stm32image_load(fd, &datalen, v2))) {
                goto err_out;
        }

        /* Load key.
         * Contains both priv and pubkey if signing.
         * Contains only pubkey if verifying.
         */
        if (!(eckey = openssl_load_key(key_path, password, sign))) {
                goto err_out;
        }
        /* Slap the header over the data so we can modify it.
         * Don't forget header endians.
         */
        h = (struct stm32_header_v1 *)data;

        /*
         * When verifying the signature, read out the image version out
         * of the image, instead of depending on supplied public key count.
         */
        if (verify && (h->header_version[1] == 2))
                v2 = 1;

        /*
         * The ST wiki explains this in
         * https://wiki.st.com/stm32mpu/wiki/STM32_header_for_binary_files#On_STM32MP23x_lines_and_STM32MP25x_lines
         * "
         * Signature is calculated from first byte of header
         * version field to last byte of image given by image
         * length field, excluding the last bytes following
         * the padding field.
         * "
         * The "... excluding the last bytes ..." part means
         * these 8 bytes, which are 8 out of 16 bytes of the
         * "Reserved padding bytes" at the end of base header.
         * Why is this done in such a complicated manner is
         * unclear.
         */
        signlen = datalen;
        if (v2)
                signlen -= 8;

        /* sign and verify already checked to be mutually exclusive */
        if (sign) {
                /* Get raw pubkey from key. */
                if (!(buf = openssl_get_pubkey(eckey, &len, &alg))) {
                        goto err_out;
                }
                if (buf[0] != POINT_CONVERSION_UNCOMPRESSED ||
                    len != EC_POINT_UNCOMPRESSED_LEN) {
                        fprintf(stderr, "EC pubkey invalid length.\n");
                        goto err_out;
                }
                /* Copy raw pubkey to header.
                 * First byte is the type declaration. Skip it.
                 * Raw bignum. Two points on curve. X concatenated with Y.
                 */
                if (v2) {
                        h2 = (struct stm32_header_v2 *)data;

                        h2->image_length = datalen - sizeof(struct stm32_header_v2);

                        memcpy(h2->ecdsa_public_key, &buf[1], len - 1);
                        memcpy(h2->ecdsa_public_key_hash, hashes, 32 * 8);

                        h2->extension_flags = 0x80000001;
                        h2->extension_headers_length = 0x180;
                        h2->binary_type = 0x10;

                        h2->extension_header_type = htobe32(0x53540002);
                        h2->extension_header_length = 0x154;
                        h2->public_key_index = 0; /* Should be configurable */
                        h2->public_key_count = 8;
                        /* Algorithm:
                         * 1: prime256v1
                         * 2: brainpoolP256r1
                         */
                        h2->public_key_algo = htole32(alg);

                        uint8_t extension_padding[36] = { 0 };
                        ssize_t rnd = getrandom(extension_padding, sizeof(extension_padding), 0);
                        if (rnd != sizeof(extension_padding)) {
                                fprintf(stderr, "Unable to generate random padding.\n");
                                goto err_out;
                        }

                        h2->extension_header_type1 = htobe32(0x5354ffff);
                        h2->extension_header_length1 = 0x2c;
                        memcpy(h2->extension_padding, extension_padding, 36);
                } else {
                        h->image_length = datalen - sizeof(struct stm32_header_v1);

                        /* option:
                         * 0: signed.
                         * 1: not signed.
                         */
                        h->option_flags = htole32(1);
                        /* Algorithm:
                         * 1: prime256v1
                         * 2: brainpoolP256r1
                         */
                        h->ecdsa_algorithm = htole32(alg);
                        /* Do ECDSA signature with sha256
                         * from correct offset in header to end of data.
                         */
                }
                if (!(ecsig =
                      openssl_do_ecdsa_sha256_sign(eckey, v2,
                                                   &data[STM32_HASH_OFFSET],
                                                   signlen - STM32_HASH_OFFSET))) {
                        goto err_out;
                }
                /* Copy signature to header.
                 * Raw bignum. Two numbers. R concatenated with S.
                 */
                BN_bn2bin(ECDSA_SIG_get0_r(ecsig),
                          &((h->image_signature)[0]));
                BN_bn2bin(ECDSA_SIG_get0_s(ecsig),
                          &((h->image_signature)[32]));
        }
        if (verify) {
                if (!(ecsig = ECDSA_SIG_new())) {
                        fprintf(stderr, "Unable to allocate a ecsig structure.\n");
                        goto err_out;
                }
                /* Get signature from header
                 * Raw bignum. Two numbers. R concatenated with S.
                 */
                ECDSA_SIG_set0(ecsig,
                               BN_bin2bn(&((h->image_signature)[0]), 32, NULL),
                               BN_bin2bn(&((h->image_signature)[32]), 32, NULL));
                /* Do ECDSA verification with sha256
                 * from correct offset in header to end of data.
                 */
                if (!(ecsig =
                      openssl_do_ecdsa_sha256_verify(ecsig, eckey, v2,
                                                     &data[STM32_HASH_OFFSET],
                                                     signlen - STM32_HASH_OFFSET))) {
                        goto err_out;
                }
        }
        /* Pubkeys are always available, regardless of operation */
        if (pubhash) {
                if (!(p = SHA256(h->ecdsa_public_key,
                                 EC_POINT_UNCOMPRESSED_LEN - 1, NULL))) {
                        fprintf(stderr, "Unable to calculate sha256 of raw pubkey.\n");
                        goto err_out;
                }
                if (!(fp = fopen("./pubkey.hash", "w+"))) {
                        fprintf(stderr, "Unable to open pubkey hash file.\n");
                        goto err_out;
                }
                if (fwrite(p, 1, SHA256_DIGEST_LENGTH, fp) !=
                    SHA256_DIGEST_LENGTH) {
                        fprintf(stderr, "Unable to write pubkey hash.\n");
                        goto err_out;
                }
        }
        if (ecsig) ECDSA_SIG_free(ecsig);
        if (buf) OPENSSL_free(buf);
        if (eckey) EC_KEY_free(eckey);
        if (data) munmap(data, datalen);
        if (password) {
                memset(password, 0, strlen(password));
                free(password);
        }
        if (key_path) free(key_path);
        if (fp) fclose(fp);
        munlockall();
        exit(EXIT_SUCCESS);

 err_out:
        if (ecsig) ECDSA_SIG_free(ecsig);
        if (buf) OPENSSL_free(buf);
        if (eckey) EC_KEY_free(eckey);
        if (data) munmap(data, datalen);
        if (password) {
                memset(password, 0, strlen(password));
                free(password);
        }
        if (key_path) free(key_path);
        if (fp) fclose(fp);
        munlockall();
        exit(EXIT_FAILURE);
}
