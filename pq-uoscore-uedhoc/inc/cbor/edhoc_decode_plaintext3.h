/*
 * Generated using zcbor version 0.8.99
 * https://github.com/NordicSemiconductor/zcbor
 * Generated with a --default-max-qty of 3
 */

#ifndef EDHOC_DECODE_PLAINTEXT3_H__
#define EDHOC_DECODE_PLAINTEXT3_H__

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include "cbor/edhoc_decode_plaintext3_types.h"

#ifdef __cplusplus
extern "C" {
#endif

#if DEFAULT_MAX_QTY != 3
#error "The type file was generated with a different default_max_qty than this file"
#endif

bool decode_repeated_map3_kid(zcbor_state_t *state, struct map3_kid_r *result);
bool decode_repeated_map3_x5bag(zcbor_state_t *state, struct map3_x5bag *result);
bool decode_repeated_map3_x5chain(zcbor_state_t *state, struct map3_x5chain *result);
bool decode_repeated_map3_x5t(zcbor_state_t *state, struct map3_x5t_r *result);
bool decode_repeated_map3_x5u(zcbor_state_t *state, struct map3_x5u *result);
bool decode_repeated_map3_c5b(zcbor_state_t *state, struct map3_c5b *result);
bool decode_repeated_map3_c5c(zcbor_state_t *state, struct map3_c5c *result);
bool decode_repeated_map3_c5t(zcbor_state_t *state, struct map3_c5t_r *result);
bool decode_repeated_map3_c5u(zcbor_state_t *state, struct map3_c5u *result);
bool decode_map3(zcbor_state_t *state, struct map3 *result);
bool decode_ptxt3(zcbor_state_t *state, struct ptxt3 *result);

int cbor_decode_ptxt3(
		const uint8_t *payload, size_t payload_len,
		struct ptxt3 *result,
		size_t *payload_len_out);


#ifdef __cplusplus
}
#endif

#endif /* EDHOC_DECODE_PLAINTEXT3_H__ */
