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
#include "cbor/edhoc_decode_message_1.h"
#include "edhoc/edhoc_method_type.h"
#include "zcbor_print.h"

#if DEFAULT_MAX_QTY != 3
#error "The type file was generated with a different default_max_qty than this file"
#endif

static bool decode_message_1(zcbor_state_t *state, struct message_1 *result);
static bool decode_message_1_kem_kem(zcbor_state_t *state, struct message_1_kem *result);
static bool decode_message_1_method(zcbor_state_t *state, int32_t *method);

static bool decode_message_1(
		zcbor_state_t *state, struct message_1 *result)
{
	zcbor_log("%s\r\n", __func__);
	bool int_res;

	/*
	Order of decoding:
		- METHOD
		- SUITE
		- G_X
		- C_I
		- (Optional) EAD_1
	*/

	bool tmp_result = (((
		((zcbor_int32_decode(state, (&(*result).message_1_METHOD))))
		&& ((zcbor_union_start_code(state) && (int_res = ((((zcbor_list_start_decode(state) && ((zcbor_multi_decode(2, 10, &(*result).SUITES_I_suite_l_suite_count, (zcbor_decoder_t *)zcbor_int32_decode, state, (&(*result).SUITES_I_suite_l_suite), sizeof(int32_t))) || (zcbor_list_map_end_force_decode(state), false)) && zcbor_list_end_decode(state))) && (((*result).message_1_SUITES_I_choice = SUITES_I_suite_l_c), true))
		|| (zcbor_union_elem_code(state) && (((zcbor_int32_decode(state, (&(*result).message_1_SUITES_I_int)))) && (((*result).message_1_SUITES_I_choice = message_1_SUITES_I_int_c), true)))), zcbor_union_end_code(state), int_res)))
		&& ((zcbor_bstr_decode(state, (&(*result).message_1_G_X))))
		&& ((zcbor_union_start_code(state) && (int_res = ((((zcbor_int32_decode(state, (&(*result).message_1_C_I_int)))) && (((*result).message_1_C_I_choice = message_1_C_I_int_c), true))
		|| (((zcbor_bstr_decode(state, (&(*result).message_1_C_I_bstr)))) && (((*result).message_1_C_I_choice = message_1_C_I_bstr_c), true))), zcbor_union_end_code(state), int_res)))
		&& ((*result).message_1_ead_1_present = ((zcbor_bstr_decode(state, (&(*result).message_1_ead_1)))), 1) // Optional EAD_1 field
	)));

	if (!tmp_result) {
		printf("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
		zcbor_trace_file(state);
		zcbor_log("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
	} else {
		zcbor_log("%s success\r\n", __func__);
	}

	return tmp_result;
}

static bool decode_message_1_kem_kem(zcbor_state_t *state, struct message_1_kem *result) {
	zcbor_log("%s\r\n", __func__);
	bool int_res;

	/*
	Order of decoding:
		- METHOD
		- SUITE
		- G_X
		- C_I
		- CT_AUTH_R
		- ENC_AUTH_R
		- (Optional) EAD_1
	*/

	bool method_decode_result = ((zcbor_int32_decode(state, (&(*result).msg_1->message_1_METHOD))));
	if (!method_decode_result){
		printf("Failed to decode METHOD\n");
		printf("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
		zcbor_trace_file(state);
		zcbor_log("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
		return false;
	}

	bool tmp_result = false;

	if ((enum method_type) (*result).msg_1->message_1_METHOD == INITIATOR_KEM_RESPONDER_KEM) {
		tmp_result = (((
			// ((zcbor_int32_decode(state, (&(*result).msg_1->message_1_METHOD))))
			((zcbor_union_start_code(state) && (int_res = ((((zcbor_list_start_decode(state) && ((zcbor_multi_decode(2, 10, &(*result).msg_1->SUITES_I_suite_l_suite_count, (zcbor_decoder_t *)zcbor_int32_decode, state, (&(*result).msg_1->SUITES_I_suite_l_suite), sizeof(int32_t))) || (zcbor_list_map_end_force_decode(state), false)) && zcbor_list_end_decode(state))) && (((*result).msg_1->message_1_SUITES_I_choice = SUITES_I_suite_l_c), true))
			|| (zcbor_union_elem_code(state) && (((zcbor_int32_decode(state, (&(*result).msg_1->message_1_SUITES_I_int)))) && (((*result).msg_1->message_1_SUITES_I_choice = message_1_SUITES_I_int_c), true)))), zcbor_union_end_code(state), int_res)))
			&& ((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_G_X))))
			&& ((zcbor_union_start_code(state) && (int_res = ((((zcbor_int32_decode(state, (&(*result).msg_1->message_1_C_I_int)))) && (((*result).msg_1->message_1_C_I_choice = message_1_C_I_int_c), true))
			|| (((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_C_I_bstr)))) && (((*result).msg_1->message_1_C_I_choice = message_1_C_I_bstr_c), true))), zcbor_union_end_code(state), int_res)))
			&& (zcbor_bstr_decode(state, (&(*result).ct_auth_r))) // KEM-KEM specific field
			&& (zcbor_bstr_decode(state, (&(*result).enc_auth_r))) // KEM-KEM specific field
			&& ((*result).msg_1->message_1_ead_1_present = ((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_ead_1)))), 1) // Optional EAD_1 field
		)));
	} else {
		tmp_result = (((
			// ((zcbor_int32_decode(state, (&(*result).msg_1->message_1_METHOD))))
			((zcbor_union_start_code(state) && (int_res = ((((zcbor_list_start_decode(state) && ((zcbor_multi_decode(2, 10, &(*result).msg_1->SUITES_I_suite_l_suite_count, (zcbor_decoder_t *)zcbor_int32_decode, state, (&(*result).msg_1->SUITES_I_suite_l_suite), sizeof(int32_t))) || (zcbor_list_map_end_force_decode(state), false)) && zcbor_list_end_decode(state))) && (((*result).msg_1->message_1_SUITES_I_choice = SUITES_I_suite_l_c), true))
			|| (zcbor_union_elem_code(state) && (((zcbor_int32_decode(state, (&(*result).msg_1->message_1_SUITES_I_int)))) && (((*result).msg_1->message_1_SUITES_I_choice = message_1_SUITES_I_int_c), true)))), zcbor_union_end_code(state), int_res)))
			&& ((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_G_X))))
			&& ((zcbor_union_start_code(state) && (int_res = ((((zcbor_int32_decode(state, (&(*result).msg_1->message_1_C_I_int)))) && (((*result).msg_1->message_1_C_I_choice = message_1_C_I_int_c), true))
			|| (((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_C_I_bstr)))) && (((*result).msg_1->message_1_C_I_choice = message_1_C_I_bstr_c), true))), zcbor_union_end_code(state), int_res)))
			// && (zcbor_bstr_decode(state, (&(*result).ct_auth_r))) // KEM-KEM specific field
			// && (zcbor_bstr_decode(state, (&(*result).enc_auth_r))) // KEM-KEM specific field
			&& ((*result).msg_1->message_1_ead_1_present = ((zcbor_bstr_decode(state, (&(*result).msg_1->message_1_ead_1)))), 1) // Optional EAD_1 field
		)));
	}
	

	if (!tmp_result) {
		printf("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
		zcbor_trace_file(state);
		zcbor_log("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
	} else {
		zcbor_log("%s success\r\n", __func__);
	}

	return tmp_result;
}

static bool decode_message_1_method(zcbor_state_t *state, int32_t *method) {
	zcbor_log("%s\r\n", __func__);

	bool rt = zcbor_int32_decode(state, method);
	if (!rt) {
		printf("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
		zcbor_trace_file(state);
		zcbor_log("%s error: %s\r\n", __func__, zcbor_error_str(zcbor_peek_error(state)));
	} else {
		zcbor_log("%s success\r\n", __func__);
	}

	return rt;
}

int cbor_decode_message_1_method(
		const uint8_t *payload, size_t payload_len,
		int32_t *method,
		size_t *payload_len_out
) {
	zcbor_state_t states[2];

	return zcbor_entry_function(payload, payload_len, (void *)method, payload_len_out, states,
		(zcbor_decoder_t *)decode_message_1_method, sizeof(states) / sizeof(zcbor_state_t), 2); 
}

int cbor_decode_message_1_kem_kem(
		const uint8_t *payload, size_t payload_len,
		struct message_1_kem *result,
		size_t *payload_len_out
) {
	zcbor_state_t states[4];

	return zcbor_entry_function(payload, payload_len, (void *)result, payload_len_out, states,
		(zcbor_decoder_t *)decode_message_1_kem_kem, sizeof(states) / sizeof(zcbor_state_t), 7);
}

int cbor_decode_message_1(
		const uint8_t *payload, size_t payload_len,
		struct message_1 *result,
		size_t *payload_len_out)
{
	zcbor_state_t states[4];

	return zcbor_entry_function(payload, payload_len, (void *)result, payload_len_out, states,
		(zcbor_decoder_t *)decode_message_1, sizeof(states) / sizeof(zcbor_state_t), 5);
}
