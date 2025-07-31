/*
   Copyright (c) 2021 Fraunhofer AISEC. See the COPYRIGHT
   file at the top-level directory of this distribution.

   Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
   http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
   <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
   option. This file may not be copied, modified, or distributed
   except according to those terms.
*/

#include "edhoc/buffer_sizes.h"
#include "edhoc_internal.h"

#include "common/memcpy_s.h"
#include "common/print_util.h"
#include "common/crypto_wrapper.h"
#include "common/oscore_edhoc_error.h"

#include "edhoc/hkdf_info.h"
#include "edhoc/messages.h"
#include "edhoc/okm.h"
#include "edhoc/plaintext.h"
#include "edhoc/prk.h"
#include "edhoc/retrieve_cred.h"
#include "edhoc/signature_or_mac_msg.h"
#include "edhoc/suites.h"
#include "edhoc/th.h"
#include "edhoc/txrx_wrapper.h"
#include "edhoc/ciphertext.h"
#include "edhoc/suites.h"
#include "edhoc/runtime_context.h"
#include "edhoc/bstr_encode_decode.h"
#include "edhoc/int_encode_decode.h"

#include "cbor/edhoc_decode_message_1.h"
#include "cbor/edhoc_encode_message_2.h"
#include "cbor/edhoc_decode_message_3.h"

#define CBOR_UINT_SINGLE_BYTE_UINT_MAX_VALUE (0x17)
#define CBOR_UINT_MULTI_BYTE_UINT_MAX_VALUE (0x17)
#define CBOR_BSTR_TYPE_MIN_VALUE (0x40)
#define CBOR_BSTR_TYPE_MAX_VALUE (0x57)


static inline enum err msg1_get_fields(const struct message_1 *m,
					enum method_type *method,
					struct byte_array *suites_i,
					struct byte_array *g_x,
					struct byte_array *c_i,
					struct byte_array *ead1) {

	uint32_t i;

	/*METHOD*/
	if ((m->message_1_METHOD > INITIATOR_KEM_RESPONDER_KEM) ||
	    (m->message_1_METHOD < INITIATOR_SK_RESPONDER_SK)) {
		return wrong_parameter;
	}
	*method = (enum method_type)m->message_1_METHOD;
	PRINTF("msg1 METHOD: %d\n", (int)*method);

	/*SUITES_I*/
	if (m->message_1_SUITES_I_choice == message_1_SUITES_I_int_c) {
		/*the initiator supports only one suite*/
		suites_i->ptr[0] = (uint8_t)m->message_1_SUITES_I_int;
		suites_i->len = 1;
	} else {
		if (0 == m->SUITES_I_suite_l_suite_count) {
			return suites_i_list_empty;
		}

		/*the initiator supports more than one suite*/
		if (m->SUITES_I_suite_l_suite_count > suites_i->len) {
			return suites_i_list_to_long;
		}

		for (i = 0; i < m->SUITES_I_suite_l_suite_count; i++) {
			suites_i->ptr[i] = (uint8_t)m->SUITES_I_suite_l_suite[i];
		}
		suites_i->len = (uint32_t)m->SUITES_I_suite_l_suite_count;
	}
	if (suites_i->len == 0) {
		return unsupported_cipher_suite;
	}
	PRINT_ARRAY("msg1 SUITES_I", suites_i->ptr, suites_i->len);

	/*G_X*/
	TRY(_memcpy_s(g_x->ptr, g_x->len, m->message_1_G_X.value,
		      (uint32_t)m->message_1_G_X.len));
	g_x->len = (uint32_t)m->message_1_G_X.len;
	PRINT_ARRAY("msg1 G_X", g_x->ptr, g_x->len);

	/*C_I*/
	if (m->message_1_C_I_choice == message_1_C_I_int_c) {
		c_i->ptr[0] = (uint8_t)m->message_1_C_I_int;
		c_i->len = 1;
	} else {
		TRY(_memcpy_s(c_i->ptr, c_i->len, m->message_1_C_I_bstr.value,
			      (uint32_t)m->message_1_C_I_bstr.len));
		c_i->len = (uint32_t)m->message_1_C_I_bstr.len;
	}
	PRINT_ARRAY("msg1 C_I_raw", c_i->ptr, c_i->len);

	/*ead_1*/
	if (m->message_1_ead_1_present) {
		TRY(_memcpy_s(ead1->ptr, ead1->len, m->message_1_ead_1.value,
			      (uint32_t)m->message_1_ead_1.len));
		ead1->len = (uint32_t)m->message_1_ead_1.len;
		PRINT_ARRAY("msg1 ead_1", ead1->ptr, ead1->len);
	}

	return ok;

}

/**
 * @brief   			Parses message 1.
 * @param[in] msg1 		Message 1.
 * @param[out] method 		EDHOC method.
 * @param[out] suites_i 	Cipher suites suported by the initiator
 * @param[out] g_x 		Public ephemeral key of the initiator.
 * @param[out] c_i 		Connection identifier of the initiator.
 * @param[out] ead1 		External authorized data 1.
 * @retval 			Ok or error code.
 */
static inline enum err
msg1_parse(struct byte_array *msg1, enum method_type *method,
	   	struct byte_array *suites_i, struct byte_array *g_x,
	   	struct byte_array *c_i, struct byte_array *ead1)
{
	struct message_1 m;
	size_t decode_len = 0;

	TRY_EXPECT(cbor_decode_message_1(msg1->ptr, msg1->len, &m, &decode_len),
		   0);

	TRY(msg1_get_fields(&m, method, suites_i, g_x, c_i, ead1));
	
	return ok;
}

static enum err msg1_parse_kem_kem(
	struct byte_array *msg1, enum method_type *method,
	struct byte_array *suites_i, struct byte_array *g_x,
	struct byte_array *c_i, struct byte_array *ead1,
 	struct byte_array *ct_auth_r, struct byte_array *enc_auth_r) {
	
	struct message_1 m;
	struct message_1_kem msg1_kem;
	msg1_kem.msg_1 = &m;

	size_t decode_len = 0;
	TRY_EXPECT(cbor_decode_message_1_kem_kem(msg1->ptr, msg1->len, &msg1_kem, &decode_len), 0);
	TRY(msg1_get_fields(msg1_kem.msg_1, method, suites_i, g_x, c_i, ead1));

	if (*method == INITIATOR_KEM_RESPONDER_KEM) {
		// Two values below only for KEM-KEM method
		/*ct_auth_r*/
		TRY(_memcpy_s(ct_auth_r->ptr, ct_auth_r->len, msg1_kem.ct_auth_r.value,
				(uint32_t) msg1_kem.ct_auth_r.len));
		ct_auth_r->len = (uint32_t) msg1_kem.ct_auth_r.len;
		PRINT_ARRAY("ct_auth_r", ct_auth_r->ptr, ct_auth_r->len);

		/*enc_auth_r/ciphertext1*/
		TRY(_memcpy_s(enc_auth_r->ptr, enc_auth_r->len, msg1_kem.enc_auth_r.value,
				(uint32_t) msg1_kem.enc_auth_r.len));
		enc_auth_r->len = (uint32_t) msg1_kem.enc_auth_r.len;
		PRINT_ARRAY("ciphertext 1", enc_auth_r->ptr, enc_auth_r->len);
	} else {
		ct_auth_r->ptr = NULL;
		ct_auth_r->len = 0;
		enc_auth_r->ptr = NULL;
		enc_auth_r->len = 0;
	}

	return ok;
 }

/**
 * @brief   			Checks if the selected cipher suite 
 * 				(the first in the list received from the 
 * 				initiator) is supported.
 * @param selected 		The selected suite.
 * @param[in] suites_r 		The list of suported cipher suites.
 * @retval  			True if supported.
 */
static inline bool selected_suite_is_supported(uint8_t selected,
					       struct byte_array *suites_r)
{
	for (uint32_t i = 0; i < suites_r->len; i++) {
		if (suites_r->ptr[i] == selected)
			PRINTF("Suite %d will be used in this EDHOC run.\n",
			       selected);
		return true;
	}
	return false;
}

/**
 * @brief   			Encodes message 2.
 * @param[in] g_y 		Public ephemeral DH key of the responder. 
 * @param[in] c_r 		Connection identifier of the responder.
 * @param[in] ciphertext_2 	The ciphertext.
 * @param[out] msg2 		The encoded message.
 * @retval  			Ok or error code.
 */
static inline enum err msg2_encode(enum method_type method,
				   const struct byte_array *g_y,
				   struct byte_array *c_r,
				   const struct byte_array *ciphertext_2,
				   const struct byte_array *ct_auth_i,
				   struct byte_array *msg2)
{
	uint32_t msg_2_len = g_y->len + ciphertext_2->len;
	if (method == INITIATOR_KEM_RESPONDER_KEM) {
		msg_2_len += ct_auth_i->len;
	}
	BYTE_ARRAY_NEW(g_y_ciphertext_2_ct_auth_i, G_Y_CIPHERTEXT_2 + CT_AUTH_I_SIZE,
		       msg_2_len);

	memcpy(g_y_ciphertext_2_ct_auth_i.ptr, g_y->ptr, g_y->len);
	memcpy(g_y_ciphertext_2_ct_auth_i.ptr + g_y->len, ciphertext_2->ptr,
	       ciphertext_2->len);

	if (method == INITIATOR_KEM_RESPONDER_KEM) {
		// KEM-KEM specific operation
		memcpy(g_y_ciphertext_2_ct_auth_i.ptr + g_y->len + ciphertext_2->len, ct_auth_i->ptr, ct_auth_i->len);
	}

	TRY(encode_bstr(&g_y_ciphertext_2_ct_auth_i, msg2));

	PRINT_ARRAY("message_2 (CBOR Sequence)", msg2->ptr, msg2->len);
	return ok;
}

enum err msg2_gen(struct edhoc_responder_context *c, struct runtime_context *rc,
			struct cred_array *cred_i_array, struct byte_array *c_i)
{
	PRINT_ARRAY("message_1 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);

	BYTE_ARRAY_NEW(suites_i, SUITES_I_SIZE, SUITES_I_SIZE);
	BYTE_ARRAY_NEW(g_x, G_X_SIZE, G_X_SIZE);

	// Two below values are used only in KEM-KEM method
	BYTE_ARRAY_NEW(ct_auth_r, CT_AUTH_R_SIZE, CT_AUTH_R_SIZE);
	BYTE_ARRAY_NEW(ctxt1, CIPHERTEXT1_SIZE, CIPHERTEXT1_SIZE);

	/* Decode message 1 */
	size_t decode_method_len = 0;

	TRY(msg1_parse_kem_kem(&rc->msg, &rc->method, &suites_i, &g_x, c_i, &rc->ead, &ct_auth_r, &ctxt1));


	// TODO this may be a vulnerability in case suites_i.len is zero
	// Cuong: I already made zero-length check in `msg1_parse`
	if (!(selected_suite_is_supported(suites_i.ptr[suites_i.len - 1],
					  &c->suites_r))) {
		// TODO implement here the sending of an error message
		return error_message_sent;
	}

	/*get cipher suite*/
	TRY(get_suite((enum suite_label)suites_i.ptr[suites_i.len - 1],
		      &rc->suite));

	bool static_dh_r;
	authentication_type_get(rc->method, &rc->static_dh_i, &static_dh_r);

	printf("Responder Authentication method: %d\n", rc->method);
	// get the key exchange algorithm: ECDH, KEM, or NIKE
	const enum ecdh_alg ke_alg = rc->suite.edhoc_ecdh;
	

	/*Calculate the shared secret G_XY*/
	// struct byte_array g_xy;
	// FORTUNATELY, shared secret sizes of ECDH and KEM are equal, both are 32 bytes 
	BYTE_ARRAY_NEW(g_xy, ECDH_SECRET_SIZE, ECDH_SECRET_SIZE);
	// If KEM is used then
	switch (ke_alg)
	{
	// ML-KEM
	case ML_KEM_512:
	case ML_KEM_768: {
		/* Initiate a buffer for KEM ciphertext (c->g_y) was already did at application code/sample */
		// Do KEM Encapsulation with the given public key from Initiator (g_x)
		if (static_dh_r) {
			return kem_unsupport_static_dh_auth;
		}
		
		uint32_t desired_len = get_kem_ctxt_len(ke_alg);
		if (desired_len > c->g_y.len) {
			return buffer_to_small;
		}
		else {
			c->g_y.len = desired_len;
		}

		TRY(kem_encap(ke_alg, &g_x, &c->g_y, g_xy.ptr));
		PRINT_ARRAY("G_XY (KEM shared secret)", g_xy.ptr, g_xy.len);
		break;
	}
	// ECDH
	case P256:
	case X25519: {// P256 or X25519
		// modify g_y buffer to have a valid length for the chosen cipher suite
		uint32_t desired_len = get_ecdh_pk_len(ke_alg);
		if (desired_len > c->g_y.len) {
			return buffer_to_small;
		}
		else {
			c->g_y.len = desired_len;
		}

		uint32_t seed;
		FILE *fp;
		fp = fopen("/dev/urandom", "r");
		uint64_t seed_len =
			fread((uint8_t *)&seed, 1, sizeof(seed), fp);
		fclose(fp);


		/// NOTE! set fixed `seed` here for reproducible text vectors
		seed = 1;
		// PRINT_ARRAY("seed", (uint8_t *)&seed, seed_len);

		// TRY(ephemeral_dh_key_gen(rc->suite.suite_label, seed, &c->y, &c->g_y));
		/*Set fixed Y and G_Y for reproducible testing
		already set up from caller main.cpp*/

		PRINT_ARRAY("Y", c->y.ptr, c->y.len);
		PRINT_ARRAY("G_Y", c->g_y.ptr, c->g_y.len);

		TRY(shared_secret_derive(rc->suite.edhoc_ecdh, &c->y, &g_x, g_xy.ptr));
		PRINT_ARRAY("G_XY (ECDH shared secret) ", g_xy.ptr, g_xy.len);
		break;
	}
	default:
		return unsupported_ecdh_curve;
	}
	// If DH is used then
	/*calculate the DH shared secret*/
	// BYTE_ARRAY_NEW(g_xy, ECDH_SECRET_SIZE, ECDH_SECRET_SIZE);
	// TRY(shared_secret_derive(rc->suite.edhoc_ecdh, &c->y, &g_x, g_xy.ptr));
	// PRINT_ARRAY("G_XY (ECDH shared secret) ", g_xy.ptr, g_xy.len);

	/******************* create and send message 2*************************/
	/*compute TH2*/
	BYTE_ARRAY_NEW(th2, HASH_SIZE, get_hash_len(rc->suite.edhoc_hash));
	TRY(hash(rc->suite.edhoc_hash, &rc->msg, &rc->msg1_hash));
	TRY(th2_calculate(rc->suite.edhoc_hash, &rc->msg1_hash, &c->g_y, &th2));
	PRINT_ARRAY("TH2", th2.ptr, th2.len);

	/* Do KEM authentication, ONLY for KEM-KEM method*/
	BYTE_ARRAY_NEW(k_auth_r, ECDH_SECRET_SIZE, ECDH_SECRET_SIZE);
	BYTE_ARRAY_NEW(ct_auth_i, CT_AUTH_I_SIZE, CT_AUTH_I_SIZE);
	BYTE_ARRAY_NEW(ptxt1, PLAINTEXT1_SIZE + get_aead_mac_len(rc->suite.edhoc_aead), ctxt1.len);

	if (rc->method == INITIATOR_KEM_RESPONDER_KEM) {
		// Decap ct_auth_r to obtain k_auth_r
		TRY(kem_decap(ke_alg, &c->sk_kem_r, &ct_auth_r, k_auth_r.ptr));
		// Decrypt enc_auth_r to get id_cred_i. In other words,
		// decrypt ciphertext1 and obtain id_cred_i
		BYTE_ARRAY_NEW(id_cred_i, ID_CRED_I_SIZE, ID_CRED_I_SIZE);
		// calculate TH1
		TRY(th1_calculate(rc->suite.edhoc_hash, &k_auth_r, &rc->th1));
		TRY(ciphertext_decrypt_split(CIPHERTEXT1, &rc->suite, &NULL_ARRAY, &id_cred_i,
			&NULL_ARRAY, &rc->ead, &k_auth_r,
			&rc->th1, &ctxt1, &ptxt1));

		/*check the authenticity of the initiator*/
		BYTE_ARRAY_NEW(cred_i, CRED_I_SIZE, CRED_I_SIZE);
		BYTE_ARRAY_NEW(pk_i, PK_SIZE, PK_SIZE);
		BYTE_ARRAY_NEW(g_i, G_I_SIZE, G_I_SIZE);

		TRY(retrieve_cred(rc->static_dh_i, cred_i_array, &id_cred_i, &cred_i,
				&pk_i, &g_i));

		printf("KEM-KEM authentication, check the authencity of initiator in msg_1\n");
		PRINT_ARRAY("CRED_I", cred_i.ptr, cred_i.len);
		PRINT_ARRAY("pk_i", pk_i.ptr, pk_i.len);
		PRINT_ARRAY("g_i", g_i.ptr, g_i.len);

		// Encap to get ct_auth_i and k_auth_i
		TRY(kem_encap(ke_alg, &cred_i_array->ptr->pk_kem, &ct_auth_i, c->k_auth_i.ptr));
	}

	/*derive prk_2e*/
	BYTE_ARRAY_NEW(PRK_2e, PRK_SIZE, PRK_SIZE);
	TRY(hkdf_extract(rc->suite.edhoc_hash, &th2, &g_xy, PRK_2e.ptr));
	PRINT_ARRAY("PRK_2e", PRK_2e.ptr, PRK_2e.len);

	/*derive prk_3e2m*/
	TRY(prk_derive(rc->method, rc->static_dh_i, rc->suite, SALT_3e2m, &th2, &PRK_2e, &g_x,
		       &c->r, &k_auth_r, rc->prk_3e2m.ptr));
	PRINT_ARRAY("PRK_3e2m", rc->prk_3e2m.ptr, rc->prk_3e2m.len);

	/*compute signature_or_MAC_2*/
	BYTE_ARRAY_NEW(sign_or_mac_2, SIGNATURE_SIZE,
		       get_signature_len(rc->suite.edhoc_sign));


	if (static_dh_r) {printf("Responder use static DH key!!!!!\n");}
	TRY(signature_or_mac(GENERATE, static_dh_r, &rc->suite, &c->sk_r,
			     &c->pk_r, &rc->prk_3e2m, &c->c_r, &th2,
			     &c->id_cred_r, &c->cred_r, &c->ead_2, MAC_2,
			     &sign_or_mac_2));

	/*compute ciphertext_2*/
	BYTE_ARRAY_NEW(plaintext_2, PLAINTEXT2_SIZE,
		       AS_BSTR_SIZE(c->c_r.len) + c->id_cred_r.len +
			       AS_BSTR_SIZE(sign_or_mac_2.len) + c->ead_2.len);
	BYTE_ARRAY_NEW(ciphertext_2, CIPHERTEXT2_SIZE, plaintext_2.len);

	TRY(ciphertext_gen(CIPHERTEXT2, &rc->suite, &c->c_r, &c->id_cred_r,
			   &sign_or_mac_2, &c->ead_2, &PRK_2e, &th2,
			   &ciphertext_2, &plaintext_2));

	/* Clear the message buffer. */
	memset(rc->msg.ptr, 0, rc->msg.len);
	rc->msg.len = sizeof(rc->msg_buf);
	/*message 2 create*/
	TRY(msg2_encode(rc->method, &c->g_y, &c->c_r, &ciphertext_2, &ct_auth_i, &rc->msg));

	TRY(th34_calculate(rc->suite.edhoc_hash, &th2, &plaintext_2, &c->cred_r,
			   &rc->th3));

	return ok;
}

enum err msg3_process(struct edhoc_responder_context *c,
		      struct runtime_context *rc,
		      struct cred_array *cred_i_array,
		      struct byte_array *prk_out,
		      struct byte_array *initiator_pk)
{
	BYTE_ARRAY_NEW(ctxt3, CIPHERTEXT3_SIZE + MAC_SIZE * 2, rc->msg.len);
	TRY(decode_bstr(&rc->msg, &ctxt3));
	PRINT_ARRAY("CIPHERTEXT_3", ctxt3.ptr, ctxt3.len);

	BYTE_ARRAY_NEW(id_cred_i, ID_CRED_I_SIZE, ID_CRED_I_SIZE);
	BYTE_ARRAY_NEW(sign_or_mac, SIG_OR_MAC_SIZE, SIG_OR_MAC_SIZE);

	PRINTF("PLAINTEXT3_SIZE: %d\n", PLAINTEXT3_SIZE);
	PRINTF("ctxt3.len: %d\n", ctxt3.len);
#if defined(_WIN32)
	BYTE_ARRAY_NEW(ptxt3,
		       PLAINTEXT3_SIZE + 16, // 16 is max aead mac length
		       ctxt3.len);
#else
	BYTE_ARRAY_NEW(ptxt3,
		       PLAINTEXT3_SIZE + get_aead_mac_len(rc->suite.edhoc_aead) + 17,
		       ctxt3.len);
#endif

	TRY(ciphertext_decrypt_split(CIPHERTEXT3, &rc->suite, NULL, &id_cred_i,
				     &sign_or_mac, &rc->ead, &rc->prk_3e2m,
				     &rc->th3, &ctxt3, &ptxt3));

	/*check the authenticity of the initiator*/
	BYTE_ARRAY_NEW(cred_i, CRED_I_SIZE, CRED_I_SIZE);
	BYTE_ARRAY_NEW(pk, PK_SIZE, PK_SIZE);
	BYTE_ARRAY_NEW(g_i, G_I_SIZE, G_I_SIZE);

	TRY(retrieve_cred(rc->static_dh_i, cred_i_array, &id_cred_i, &cred_i,
			  &pk, &g_i));
	PRINT_ARRAY("CRED_I", cred_i.ptr, cred_i.len);
	PRINT_ARRAY("pk", pk.ptr, pk.len);
	PRINT_ARRAY("g_i", g_i.ptr, g_i.len);

	/* Export public key. */
	if ((NULL != initiator_pk) && (NULL != initiator_pk->ptr)) {
		_memcpy_s(initiator_pk->ptr, initiator_pk->len, pk.ptr, pk.len);
		initiator_pk->len = pk.len;
	}

	/*derive prk_4e3m*/
	TRY(prk_derive(rc->method, rc->static_dh_i, rc->suite, SALT_4e3m, &rc->th3,
		       &rc->prk_3e2m, &g_i, &c->y, &c->k_auth_i, rc->prk_4e3m.ptr));
	PRINT_ARRAY("prk_4e3m", rc->prk_4e3m.ptr, rc->prk_4e3m.len);

	TRY(signature_or_mac(VERIFY, rc->static_dh_i, &rc->suite, NULL, &pk,
			     &rc->prk_4e3m, &NULL_ARRAY, &rc->th3, &id_cred_i,
			     &cred_i, &rc->ead, MAC_3, &sign_or_mac));

	/*TH4*/
	// ptxt3.len = ptxt3.len - get_aead_mac_len(rc->suite.edhoc_aead);
	TRY(th34_calculate(rc->suite.edhoc_hash, &rc->th3, &ptxt3, &cred_i,
			   &rc->th4));

	/*PRK_out*/
	TRY(edhoc_kdf(rc->suite.edhoc_hash, &rc->prk_4e3m, PRK_out, &rc->th4,
		      prk_out));
	return ok;
}

#ifdef MESSAGE_4
enum err msg4_gen(struct edhoc_responder_context *c, struct runtime_context *rc)
{
	/*Ciphertext 4 calculate*/
	BYTE_ARRAY_NEW(ctxt4, CIPHERTEXT4_SIZE, CIPHERTEXT4_SIZE);
#if PLAINTEXT4_SIZE != 0
	BYTE_ARRAY_NEW(ptxt4, PLAINTEXT4_SIZE, PLAINTEXT4_SIZE);
#else
	struct byte_array ptxt4 = BYTE_ARRAY_INIT(NULL, 0);
#endif

	TRY(ciphertext_gen(CIPHERTEXT4, &rc->suite, &NULL_ARRAY, &NULL_ARRAY,
			   &NULL_ARRAY, &c->ead_4, &rc->prk_4e3m, &rc->th4,
			   &ctxt4, &ptxt4));

	TRY(encode_bstr(&ctxt4, &rc->msg));

	PRINT_ARRAY("message_4 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);
	return ok;
}
#endif // MESSAGE_4

enum err edhoc_responder_run_extended(
	struct edhoc_responder_context *c, struct cred_array *cred_i_array,
	struct byte_array *err_msg, struct byte_array *prk_out,
	struct byte_array *initiator_pub_key, struct byte_array *c_i_bytes,
	enum err (*tx)(void *sock, struct byte_array *data),
	enum err (*rx)(void *sock, struct byte_array *data),
	enum err (*ead_process)(void *params, struct byte_array *ead13))
{
	struct runtime_context rc = { 0 };
	runtime_context_init(&rc);

	/*receive message 1*/
	PRINT_MSG("waiting to receive message 1...\n");
	TRY(rx(c->sock, &rc.msg));

	/*create and send message 2*/
	TRY(msg2_gen(c, &rc, cred_i_array ,c_i_bytes));
	TRY(ead_process(c->params_ead_process, &rc.ead));
	TRY(tx(c->sock, &rc.msg));

	/*receive message 3*/
	PRINT_MSG("waiting to receive message 3...\n");
	rc.msg.len = sizeof(rc.msg_buf);
	TRY(rx(c->sock, &rc.msg));
	TRY(msg3_process(c, &rc, cred_i_array, prk_out, initiator_pub_key));
	TRY(ead_process(c->params_ead_process, &rc.ead));

	/*create and send message 4*/
#ifdef MESSAGE_4
	TRY(msg4_gen(c, &rc));
	TRY(tx(c->sock, &rc.msg));
#endif // MESSAGE_4
	return ok;
}

enum err edhoc_responder_run(
	struct edhoc_responder_context *c, struct cred_array *cred_i_array,
	struct byte_array *err_msg, struct byte_array *prk_out,
	enum err (*tx)(void *sock, struct byte_array *data),
	enum err (*rx)(void *sock, struct byte_array *data),
	enum err (*ead_process)(void *params, struct byte_array *ead13))
{
	BYTE_ARRAY_NEW(c_i, C_I_SIZE, C_I_SIZE);
	return edhoc_responder_run_extended(c, cred_i_array, err_msg, prk_out,
					    &NULL_ARRAY, &c_i, tx, rx,
					    ead_process);
}
