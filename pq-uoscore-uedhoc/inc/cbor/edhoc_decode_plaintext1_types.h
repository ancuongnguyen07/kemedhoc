/*
 * Generated using zcbor version 0.8.99
 * https://github.com/NordicSemiconductor/zcbor
 * Generated with a --default-max-qty of 3
 */

#ifndef EDHOC_DECODE_PLAINTEXT1_TYPES_H__
#define EDHOC_DECODE_PLAINTEXT1_TYPES_H__

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <zcbor_common.h>

#include "edhoc_decode_plaintext3_types.h"

#ifdef __cplusplus
extern "C" {
#endif

/** Which value for --default-max-qty this file was created with.
 *
 *  The define is used in the other generated file to do a build-time
 *  compatibility check.
 *
 *  See `zcbor --help` for more information about --default-max-qty
 */
#define DEFAULT_MAX_QTY 3

struct ptxt1 {
    union {
        struct map3 ptxt1_ID_CRED_I_map1_m;
        struct zcbor_string ptxt1_ID_CRED_I_bstr;
        int32_t ptxt1_ID_CRED_I_int;
    };
    enum {
        ptxt1_ID_CRED_I_map1_m_c,
        ptxt1_ID_CRED_I_bstr_c,
        ptxt1_ID_CRED_I_int_c,
    } ptxt1_ID_CRED_I_choice;
    struct zcbor_string ptxt1_EAD_1;
    bool ptxt1_EAD_1_present;
};

#ifdef __cplusplus
}
#endif

#endif /* EDHOC_DECODE_PLAINTEXT1_TYPES_H__ */