/*
   Copyright (c) 2021 Fraunhofer AISEC. See the COPYRIGHT
   file at the top-level directory of this distribution.

   Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
   http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
   <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
   option. This file may not be copied, modified, or distributed
   except according to those terms.
*/

#include <stdbool.h>
#include "edhoc_internal.h"

#include "common/crypto_wrapper.h"
#include "common/oscore_edhoc_error.h"
#include "common/memcpy_s.h"
#include "common/print_util.h"

#include "edhoc/buffer_sizes.h"
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
#include "edhoc/runtime_context.h"
#include "edhoc/bstr_encode_decode.h"
#include "edhoc/int_encode_decode.h"

#include "cbor/edhoc_encode_message_1.h"
#include "cbor/edhoc_decode_message_2.h"
#include "cbor/edhoc_encode_message_3.h"

/** 
 * @brief   			Parses message 2.
 * @param c 			Initiator context.
 * @param[in] msg2 		Message 2. 
 * @param[out] g_y		G_Y ephemeral public key of the responder.
 * @param[out] ciphertext2	Ciphertext 2.
 * @retval			Ok or error code.
 */
static inline enum err msg2_parse(enum method_type method,
					struct byte_array *msg2,
				  struct byte_array *g_y,
				  struct byte_array *ciphertext2,
				  struct byte_array *ct_auth_i)
{
	uint32_t msg_2_len = g_y->len + ciphertext2->len;
	if (method == INITIATOR_KEM_RESPONDER_KEM) {
		msg_2_len += ct_auth_i->len;
	}
	BYTE_ARRAY_NEW(g_y_ciphertext_2_ct_auth_i, G_Y_CIPHERTEXT_2 + CT_AUTH_I_SIZE,
					msg_2_len);
	TRY(decode_bstr(msg2, &g_y_ciphertext_2_ct_auth_i));

	TRY(_memcpy_s(g_y->ptr, g_y->len, g_y_ciphertext_2_ct_auth_i.ptr, g_y->len));
	PRINT_ARRAY("G_y", g_y->ptr, g_y->len);

	TRY(_memcpy_s(ciphertext2->ptr, ciphertext2->len,
		g_y_ciphertext_2_ct_auth_i.ptr + g_y->len,
		g_y_ciphertext_2_ct_auth_i.len - g_y->len - ct_auth_i->len));
	ciphertext2->len = g_y_ciphertext_2_ct_auth_i.len - g_y->len - ct_auth_i->len;
	PRINT_ARRAY("ciphertext2", ciphertext2->ptr, ciphertext2->len);

	if (method == INITIATOR_KEM_RESPONDER_KEM) {
		// KEM-KEM specific operation
		TRY(_memcpy_s(ct_auth_i->ptr, ct_auth_i->len, g_y_ciphertext_2_ct_auth_i.ptr + g_y->len + ciphertext2->len,
			g_y_ciphertext_2_ct_auth_i.len - g_y->len - ciphertext2->len));
		ct_auth_i->len = g_y_ciphertext_2_ct_auth_i.len - g_y->len - ciphertext2->len;
		PRINT_ARRAY("ct_auth_i", ct_auth_i->ptr, ct_auth_i->len);
	}

	return ok;
}

enum err msg1_gen(const struct edhoc_initiator_context *c,
		  struct runtime_context *rc, const struct cred_array *cred_r_array)
{
	struct message_1 m1;
	struct message_1_kem m1_kem;
	m1_kem.msg_1 = &m1;

	/*METHOD_CORR*/
	m1.message_1_METHOD = (int32_t)c->method;

	/*SUITES_I*/
	if (c->suites_i.len == 1) {
		/* only one suite, encode into int */
		m1.message_1_SUITES_I_choice = message_1_SUITES_I_int_c;
		m1.message_1_SUITES_I_int = c->suites_i.ptr[0];
	} else if (c->suites_i.len > 1) {
		/* more than one suites, encode into array */
		m1.message_1_SUITES_I_choice = SUITES_I_suite_l_c;
		m1.SUITES_I_suite_l_suite_count = c->suites_i.len;
		for (uint32_t i = 0; i < c->suites_i.len; i++) {
			m1.SUITES_I_suite_l_suite[i] = c->suites_i.ptr[i];
		}
	}

	/* G_X ephemeral public key */
	m1.message_1_G_X.value = c->g_x.ptr;
	m1.message_1_G_X.len = c->g_x.len;
	PRINT_ARRAY("G_X", c->g_x.ptr, c->g_x.len);

	/* C_I connection ID  of the initiator*/
	PRINT_ARRAY("C_I", c->c_i.ptr, c->c_i.len);
	if (c_x_is_encoded_int(&c->c_i)) {
		m1.message_1_C_I_choice = message_1_C_I_int_c;
		TRY(decode_int(&c->c_i, &m1.message_1_C_I_int));
	} else {
		m1.message_1_C_I_choice = message_1_C_I_bstr_c;
		m1.message_1_C_I_bstr.value = c->c_i.ptr;
		m1.message_1_C_I_bstr.len = c->c_i.len;
	}

	if (c->ead_1.len != 0) {
		/* ead_1 unprotected opaque auxiliary data */
		m1.message_1_ead_1.value = c->ead_1.ptr;
		m1.message_1_ead_1.len = c->ead_1.len;
		m1.message_1_ead_1_present = true;
		printf("EAD1 presents\n");
	} else {
		m1.message_1_ead_1_present = false;
	}

	TRY(get_suite((enum suite_label)c->suites_i.ptr[c->suites_i.len - 1],
		      &rc->suite));

// #ifdef PQC
	BYTE_ARRAY_NEW(ct_auth_r, CT_AUTH_R_SIZE, CT_AUTH_R_SIZE);
	BYTE_ARRAY_NEW(ptxt1, PLAINTEXT1_SIZE, c->id_cred_i.len + c->ead_1.len);
	BYTE_ARRAY_NEW(ctxt1, CIPHERTEXT1_SIZE + MAC_SIZE, AS_BSTR_SIZE(ptxt1.len) +
				get_aead_mac_len(rc->suite.edhoc_aead));

	// This rountine is specific for only the KEM-KEM authentication method
	if ((enum method_type) m1.message_1_METHOD == INITIATOR_KEM_RESPONDER_KEM) {
		// Purely KEM-KEM method, not yet standardized in RFC
		// looking for the static public key of the Responder
		const struct byte_array pk_r_kem = cred_r_array->ptr->pk_kem;
		PRINT_ARRAY("pk_r_kem", pk_r_kem.ptr, pk_r_kem.len);

		// (ct_auth_r, k_auth_r) = KEM.Encap(pk_r)
		// WARNING!!! Temporarily assign fixed
		TRY(kem_encap(rc->suite.edhoc_ecdh, &pk_r_kem, &ct_auth_r, c->k_auth_r.ptr));

		// enc_auth_r = aead(k_auth_r, id_cred_i)
		// just naively encrypt id_cred_i first
		// TH1 = H(k_auth_r)
		// a mature design will come later
		// BYTE_ARRAY_NEW(iv, AEAD_IV_SIZE, AEAD_IV_SIZE);
		TRY(th1_calculate(rc->suite.edhoc_hash, &c->k_auth_r, &rc->th1));

		TRY(ciphertext_gen(CIPHERTEXT1, &rc->suite, &NULL_ARRAY, &c->id_cred_i,
			&NULL_ARRAY, &NULL_ARRAY, &c->k_auth_r, &rc->th1,
			&ctxt1, &ptxt1));
		printf("CTXT1 computation done!\n");

		m1_kem.ct_auth_r.value = ct_auth_r.ptr;
		m1_kem.ct_auth_r.len = ct_auth_r.len;
		m1_kem.enc_auth_r.value = ctxt1.ptr;
		m1_kem.enc_auth_r.len = ctxt1.len;

		PRINT_ARRAY("ct_auth_r", m1_kem.ct_auth_r.value, m1_kem.ct_auth_r.len);
		PRINT_ARRAY("enc_auth_r", m1_kem.enc_auth_r.value, m1_kem.enc_auth_r.len);

		size_t payload_len_out;
		// use `m1_kem` struct here
		TRY_EXPECT(cbor_encode_message_1_kem_kem(rc->msg.ptr, rc->msg.len, &m1_kem,
			&payload_len_out), 0);
		rc->msg.len = (uint32_t)payload_len_out;

	} else {
		size_t payload_len_out;
		// PRINT_ARRAY("message", rc->msg.ptr, rc->msg.len);
		TRY_EXPECT(cbor_encode_message_1(rc->msg.ptr, rc->msg.len, &m1,
			&payload_len_out), 0);
		rc->msg.len = (uint32_t)payload_len_out;
	}
// #endif // PQC

	// size_t payload_len_out;
	// // PRINT_ARRAY("message", rc->msg.ptr, rc->msg.len);
	// TRY_EXPECT(cbor_encode_message_1(rc->msg.ptr, rc->msg.len, &m1,
	// 	&payload_len_out), 0);
	// rc->msg.len = (uint32_t)payload_len_out;

	PRINT_ARRAY("message_1 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);

	/* Calculate hash of msg1 for TH2. */
	TRY(hash(rc->suite.edhoc_hash, &rc->msg, &rc->msg1_hash));
	return ok;
}

static enum err msg2_process(const struct edhoc_initiator_context *c,
			     struct runtime_context *rc,
			     struct cred_array *cred_r_array,
			     struct byte_array *c_r, bool static_dh_i,
			     bool static_dh_r, struct byte_array *th3,
			     struct byte_array *PRK_3e2m)
{
	uint32_t g_y_len;
	enum ecdh_alg ke_alg = rc->suite.edhoc_ecdh;
	uint32_t g_xy_len = get_shared_secret_len(ke_alg);
	uint32_t ct_auth_i_len = 0;
	if (c->method == INITIATOR_KEM_RESPONDER_KEM) {
		ct_auth_i_len = get_kem_ctxt_len(ke_alg);
	}
	switch (ke_alg)
	{
	// ML-KEM
	case ML_KEM_512:
	case ML_KEM_768:
		// KEM ciphertext length
		if (rc->static_dh_i) {
			return kem_unsupport_static_dh_auth;
		}
		g_y_len = get_kem_ctxt_len(ke_alg);
		break;
	// ECDH
	case P256:
	case X25519:
		g_y_len = get_ecdh_pk_len(ke_alg);
		break;
	default:
		return unsupported_ecdh_curve;
	}

	// BYTE_ARRAY_NEW(g_y, G_Y_SIZE, get_ecdh_pk_len(rc->suite.edhoc_ecdh));
	BYTE_ARRAY_NEW(g_y, g_y_len, g_y_len);
	uint32_t ciphertext_len = rc->msg.len - g_y.len - ct_auth_i_len;
	ciphertext_len -= BSTR_ENCODING_OVERHEAD(ciphertext_len);
	BYTE_ARRAY_NEW(ciphertext, CIPHERTEXT2_SIZE, ciphertext_len);
	BYTE_ARRAY_NEW(plaintext, PLAINTEXT2_SIZE, ciphertext.len);
	PRINT_ARRAY("message_2 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);

	BYTE_ARRAY_NEW(ct_auth_i, CT_AUTH_I_SIZE, CT_AUTH_I_SIZE);

	if (c->method != INITIATOR_KEM_RESPONDER_KEM) {
		ct_auth_i.ptr = NULL;
		ct_auth_i.len = 0;
	}
	/*parse the message*/
	TRY(msg2_parse(c->method, &rc->msg, &g_y, &ciphertext, &ct_auth_i));

	/*calculate the shared secret G_XY*/
	// FORTUNATELY, shared secret sizes of ECDH and KEM are equal, both are 32 bytes 
	BYTE_ARRAY_NEW(g_xy, g_xy_len, g_xy_len);

	switch (ke_alg)
	{
	case ML_KEM_512:
	case ML_KEM_768:
		if (rc->static_dh_i) {
			return kem_unsupport_static_dh_auth;
		}
		TRY(kem_decap(ke_alg, &c->x, &g_y, g_xy.ptr));
		break;
	case P256:
	case X25519:
		TRY(shared_secret_derive(rc->suite.edhoc_ecdh, &c->x, &g_y, g_xy.ptr));
		break;
	default:
		return unsupported_ecdh_curve;
	}
	// TRY(shared_secret_derive(rc->suite.edhoc_ecdh, &c->x, &g_y, g_xy.ptr));
	PRINT_ARRAY("G_XY (ECDH shared secret) ", g_xy.ptr, g_xy.len);

	/*calculate th2*/
	BYTE_ARRAY_NEW(th2, HASH_SIZE, get_hash_len(rc->suite.edhoc_hash));

	TRY(th2_calculate(rc->suite.edhoc_hash, &rc->msg1_hash, &g_y, &th2));

	/*calculate PRK_2e*/
	BYTE_ARRAY_NEW(PRK_2e, PRK_SIZE, PRK_SIZE);
	TRY(hkdf_extract(rc->suite.edhoc_hash, &th2, &g_xy, PRK_2e.ptr));
	PRINT_ARRAY("PRK_2e", PRK_2e.ptr, PRK_2e.len);

	BYTE_ARRAY_NEW(sign_or_mac, SIG_OR_MAC_SIZE, SIG_OR_MAC_SIZE);
	BYTE_ARRAY_NEW(id_cred_r, ID_CRED_R_SIZE, ID_CRED_R_SIZE);

	plaintext.len = ciphertext.len;
	TRY(check_buffer_size(PLAINTEXT2_SIZE, plaintext.len));

	TRY(ciphertext_decrypt_split(CIPHERTEXT2, &rc->suite, c_r, &id_cred_r,
				     &sign_or_mac, &rc->ead, &PRK_2e, &th2,
				     &ciphertext, &plaintext));

	/*check the authenticity of the responder*/
	BYTE_ARRAY_NEW(cred_r, CRED_R_SIZE, CRED_R_SIZE);
	BYTE_ARRAY_NEW(pk, PK_SIZE, PK_SIZE);
	BYTE_ARRAY_NEW(g_r, G_R_SIZE, G_R_SIZE);
	TRY(retrieve_cred(static_dh_r, cred_r_array, &id_cred_r, &cred_r, &pk,
			  &g_r));
	PRINT_ARRAY("CRED_R", cred_r.ptr, cred_r.len);
	PRINT_ARRAY("pk", pk.ptr, pk.len);
	PRINT_ARRAY("g_r", g_r.ptr, g_r.len);

	/*derive prk_3e2m*/
	TRY(prk_derive(c->method, static_dh_r, rc->suite, SALT_3e2m, &th2, &PRK_2e, &g_r,
		       &c->x, &c->k_auth_r, PRK_3e2m->ptr));
	PRINT_ARRAY("prk_3e2m", PRK_3e2m->ptr, PRK_3e2m->len);

	TRY(signature_or_mac(VERIFY, static_dh_r, &rc->suite, NULL, &pk,
			     PRK_3e2m, c_r, &th2, &id_cred_r, &cred_r, &rc->ead,
			     MAC_2, &sign_or_mac));

	TRY(th34_calculate(rc->suite.edhoc_hash, &th2, &plaintext, &cred_r,
			   th3));

	BYTE_ARRAY_NEW(k_auth_i, ECDH_SECRET_SIZE, ECDH_SECRET_SIZE);
	if (c->method == INITIATOR_KEM_RESPONDER_KEM) {
		/*Decap ct_auth_i to obtain k_auth_i*/
		TRY(kem_decap(ke_alg, &c->sk_kem_i, &ct_auth_i, k_auth_i.ptr));
	}
	

	/*derive prk_4e3m*/
	TRY(prk_derive(c->method, static_dh_i, rc->suite, SALT_4e3m, th3, PRK_3e2m, &g_y,
		       &c->i, &k_auth_i, rc->prk_4e3m.ptr));
	PRINT_ARRAY("prk_4e3m", rc->prk_4e3m.ptr, rc->prk_4e3m.len);

	return ok;
}

static enum err msg3_only_gen(const struct edhoc_initiator_context *c,
			      struct runtime_context *rc, bool static_dh_i,
			      struct byte_array *th3,
			      struct byte_array *PRK_3e2m,
			      struct byte_array *prk_out)
{
	BYTE_ARRAY_NEW(plaintext, PLAINTEXT3_SIZE,
		       c->id_cred_i.len + AS_BSTR_SIZE(SIG_OR_MAC_SIZE) +
			       c->ead_3.len);
	BYTE_ARRAY_NEW(ciphertext, CIPHERTEXT3_SIZE + 33,
		       AS_BSTR_SIZE(plaintext.len) +
			       get_aead_mac_len(rc->suite.edhoc_aead));
	/*calculate Signature_or_MAC_3*/
	BYTE_ARRAY_NEW(sign_or_mac_3, SIG_OR_MAC_SIZE, SIG_OR_MAC_SIZE);
	TRY(signature_or_mac(GENERATE, static_dh_i, &rc->suite, &c->sk_i,
			     &c->pk_i, &rc->prk_4e3m, &NULL_ARRAY, th3,
			     &c->id_cred_i, &c->cred_i, &c->ead_3, MAC_3,
			     &sign_or_mac_3));

	/*create plaintext3 and ciphertext3*/
	TRY(ciphertext_gen(CIPHERTEXT3, &rc->suite, &NULL_ARRAY, &c->id_cred_i,
			   &sign_or_mac_3, &c->ead_3, PRK_3e2m, th3,
			   &ciphertext, &plaintext));

	/*massage 3 create and send*/
	TRY(encode_bstr(&ciphertext, &rc->msg));
	PRINT_ARRAY("message_3 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);

	/*TH4*/
	TRY(th34_calculate(rc->suite.edhoc_hash, th3, &plaintext, &c->cred_i,
			   &rc->th4));

	/*PRK_out*/
	TRY(edhoc_kdf(rc->suite.edhoc_hash, &rc->prk_4e3m, PRK_out, &rc->th4,
		      prk_out));
	return ok;
}

enum err msg3_gen(const struct edhoc_initiator_context *c,
		  struct runtime_context *rc, struct cred_array *cred_r_array,
		  struct byte_array *c_r, struct byte_array *prk_out)
{
	bool static_dh_i = false, static_dh_r = false;
	authentication_type_get(c->method, &static_dh_i, &static_dh_r);
	BYTE_ARRAY_NEW(th3, HASH_SIZE, HASH_SIZE);
	BYTE_ARRAY_NEW(PRK_3e2m, PRK_SIZE, PRK_SIZE);

	/*process message 2*/
	TRY(msg2_process(c, rc, cred_r_array, c_r, static_dh_i, static_dh_r,
			 &th3, &PRK_3e2m));

	/*generate message 3*/
	msg3_only_gen(c, rc, static_dh_i, &th3, &PRK_3e2m, prk_out);
	return ok;
}

#ifdef MESSAGE_4
enum err msg4_process(struct runtime_context *rc)
{
	PRINT_ARRAY("message_4 (CBOR Sequence)", rc->msg.ptr, rc->msg.len);

	BYTE_ARRAY_NEW(ciphertext4, CIPHERTEXT4_SIZE, CIPHERTEXT4_SIZE);
	TRY(decode_bstr(&rc->msg, &ciphertext4));
	PRINT_ARRAY("ciphertext_4", ciphertext4.ptr, ciphertext4.len);

	BYTE_ARRAY_NEW(plaintext4,
		       PLAINTEXT4_SIZE + get_aead_mac_len(rc->suite.edhoc_aead),
		       ciphertext4.len);
	TRY(ciphertext_decrypt_split(CIPHERTEXT4, &rc->suite, NULL, &NULL_ARRAY,
				     &NULL_ARRAY, &rc->ead, &rc->prk_4e3m,
				     &rc->th4, &ciphertext4, &plaintext4));
	return ok;
}
#endif // MESSAGE_4

enum err edhoc_initiator_run_extended(
	const struct edhoc_initiator_context *c,
	struct cred_array *cred_r_array, struct byte_array *err_msg,
	struct byte_array *c_r_bytes, struct byte_array *prk_out,
	enum err (*tx)(void *sock, struct byte_array *data),
	enum err (*rx)(void *sock, struct byte_array *data),
	enum err (*ead_process)(void *params, struct byte_array *ead24))
{
	struct runtime_context rc = { 0 };
	runtime_context_init(&rc);

	/*create and send message 1*/
	TRY(msg1_gen(c, &rc, cred_r_array));
	TRY(tx(c->sock, &rc.msg));

	/*receive message 2*/
	PRINT_MSG("waiting to receive message 2...\n");
	rc.msg.len = sizeof(rc.msg_buf);
	TRY(rx(c->sock, &rc.msg));

	/*create and send message 3*/
	TRY(msg3_gen(c, &rc, cred_r_array, c_r_bytes, prk_out));
	TRY(ead_process(c->params_ead_process, &rc.ead));
	TRY(tx(c->sock, &rc.msg));

	/*receive message 4*/
#ifdef MESSAGE_4
	PRINT_MSG("waiting to receive message 4...\n");
	rc.msg.len = sizeof(rc.msg_buf);
	TRY(rx(c->sock, &rc.msg));
	TRY(msg4_process(&rc));
	TRY(ead_process(c->params_ead_process, &rc.ead));
#endif // MESSAGE_4
	return ok;
}

enum err edhoc_initiator_run(
	const struct edhoc_initiator_context *c,
	struct cred_array *cred_r_array, struct byte_array *err_msg,
	struct byte_array *prk_out,
	enum err (*tx)(void *sock, struct byte_array *data),
	enum err (*rx)(void *sock, struct byte_array *data),
	enum err (*ead_process)(void *params, struct byte_array *ead24))
{
	BYTE_ARRAY_NEW(c_r, C_R_SIZE, C_R_SIZE);

	return edhoc_initiator_run_extended(c, cred_r_array, err_msg, &c_r,
					    prk_out, tx, rx, ead_process);
}
