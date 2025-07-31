/*
 * Generated using zcbor version 0.8.99
 * https://github.com/NordicSemiconductor/zcbor
 * Generated with a --default-max-qty of 3
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include "zcbor_decode.h"
#include "cbor/edhoc_decode_plaintext1.h"
#include "cbor/edhoc_decode_plaintext3.h"
#include "zcbor_print.h"

#if DEFAULT_MAX_QTY != 3
#error "The type file was generated with a different default_max_qty than this file"
#endif


bool decode_ptxt1(zcbor_state_t *state, struct ptxt1 *result) {
    zcbor_log("%s\r\n", __func__);
    bool int_res;

    bool tmp_result = (((((zcbor_union_start_code(state) && (int_res = ((((decode_map3(state, (&(*result).ptxt1_ID_CRED_I_map1_m)))) && (((*result).ptxt1_ID_CRED_I_choice = ptxt1_ID_CRED_I_map1_m_c), true))
	|| (zcbor_union_elem_code(state) && (((zcbor_bstr_decode(state, (&(*result).ptxt1_ID_CRED_I_bstr)))) && (((*result).ptxt1_ID_CRED_I_choice = ptxt1_ID_CRED_I_bstr_c), true)))
	|| (((zcbor_int32_decode(state, (&(*result).ptxt1_ID_CRED_I_int)))) && (((*result).ptxt1_ID_CRED_I_choice = ptxt1_ID_CRED_I_int_c), true))), zcbor_union_end_code(state), int_res)))
	&& ((*result).ptxt1_EAD_1_present = ((zcbor_bstr_decode(state, (&(*result).ptxt1_EAD_1)))), 1))));

    if (!tmp_result) {
        printf("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
        zcbor_trace_file(state);
		zcbor_log("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
    } else {
        zcbor_log("%s success\r\n", __func__);
    }

    return tmp_result;
}

int cbor_decode_ptxt1(
        const uint8_t *payload, size_t payload_len,
        struct ptxt1 *result,
        size_t *payload_len_out
) {
    zcbor_state_t states[6];

    return zcbor_entry_function(payload, payload_len, (void *)result, payload_len_out, states,
		(zcbor_decoder_t *)decode_ptxt1, sizeof(states) / sizeof(zcbor_state_t), 2);
}