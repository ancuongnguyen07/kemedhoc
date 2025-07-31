/*
   Copyright (c) 2021 Fraunhofer AISEC. See the COPYRIGHT
   file at the top-level directory of this distribution.

   Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
   http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
   <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
   option. This file may not be copied, modified, or distributed
   except according to those terms.
*/
#ifndef PLAINTEXT_H
#define PLAINTEXT_H

#include <stdint.h>

#include "common/oscore_edhoc_error.h"

/**
 * @brief                       Decodes id_cred to kid.
 * 
 * @param[in] id_cred           ID_CRED_x
 * @param[out] kid              The result.
 * @retval                      Ok or error code.
 */
enum err id_cred2kid(const struct byte_array *id_cred, struct byte_array *kid);

/**
 * @brief                        Split the plaintext of message 1.
 * 
 * @param[in] ptxt               Pointer to the input plaintext.
 * @param[out] id_cred_i         Pointer to the output id_cred_i.
 * @retval                       Ok or error code.
 */
enum err plaintext1_split(struct byte_array *ptxt, struct byte_array *id_cred_i);

/**
 * @brief                        Split the plaintext of message 2.
 * 
 * @param[in] ptxt               Pointer to the input plaintext.
 * @param[out] c_r               Pointer to the output connection identifier c_r.
 * @param[out] id_cred_r         Pointer to the output credential of Responder id_cred_r.
 * @param[out] sig_or_mac        Pointer to the output Signature or MAC sig2/mac2.
 * @param[out] ead               Pointer to the output EAD2.
 */
enum err plaintext2_split(struct byte_array *ptxt, struct byte_array *c_r,
                        struct byte_array *id_cred_r,
                        struct byte_array *sig_or_mac,
                        struct byte_array *ead);

/**
 * @brief                        Split the plaintext of message 2.
 * 
 * @param[in] ptxt               Pointer to the input plaintext.
 * @param[out] id_cred_i         Pointer to the output credential of Initiator id_cred_i.
 * @param[out] sig_or_mac        Pointer to the output Signature or MAC sig3/mac3.
 * @param[out] ead               Pointer to the output EAD3.
 */
enum err plaintext3_split(struct byte_array *ptxt, struct byte_array *id_cred_i,
                        struct byte_array *sig_or_mac,
                        struct byte_array *ead);

#endif
