## How to run Makefile
```sh
make MAIN=<main-tex-file> # ignore the extension name
# e.g. make MAIN=report
```

## MYSTERIES
- I am confused that how should parties in EDHOC protocol authenticated each other before
doing key exchange. Maybe this party-authentication is out of scope for EDHOC as
in the RFC the authors stated "Like in DTLS, authentication is the
responsibility of the application. EDHOC identifies (and optionally transports)
authentication credentials and provides proof-of-possession of the private
authentication key".
    - **Answer**: Yes, EDHOC assumes that any device typically has local access credentials of
    other devices, in constrast to TLS where client typically requests server's certificate
    in the first message. For example, credentails could be provisioned or acquired out-of-band
    over less constrained links.
    - More info: each protocol paricipant is associated with a long-term key pair (static DH key
    or sinature keys) called `credential CRED`. It is a data structure containing a unique
    identifier and the corresponding DH share or verification key. Further bandwidth savings
    is achieved by sending a short `credential identifier ID_CRED` rather than the credential
    itself, contrary to TLS, where certificates are always sent by at least one protocol participant
    (typically server's certificate would be sent over the wire).
    - **Important note**: credential identifiers `ID_CRED` does not need to be unique and may
    reference multiple credentials belonging to potentially different users. Hence, the receiver
    of a signature MUST try all possible public keys associated with the received credential
    identifier before determining the identity of the peer --> implicit assumption of signature scheme
    should be investigated in formal analysis. `ID_CRED` may contain the authentication
    credential `CRED`, but in many settings, it is not necessary to transport `CRED` within EDHOC.
    `ID_CRED` do not have any cryptographic purposes since the `CRED` are integrity
    protected by Signature or MAC.

- Why KEM is not possible for static-DH-key-based methods is still unanswered.
Static-DH-key-based full protocol looks too complicated now, needs to find the points
that KEM could not be applicable to.
    - KEM properties:
        - You need the other person's public key to do key encapsulation, but unlike key exchange
        algorithms e.g. ECDH, the other person **does not** need your public key to receive
        the shared-symmetric key and, unlike digital signature algorithms and key exchange
        algorithms, the recipient **cannot** authenticate the received key with only
        a single use of KEM. **SOLVED** the usage of ephemeral-static shared DH key
        makes KEM-adaptation would require an extra round trip.

## EDHOC benefits
- Primary use case is to establish a security context for the OSCORE protocol
- It provides authentication only where no application data to be sent
- It provides `exporter` mechanism to derive further key if needed in other applications.
- It provides lightweight `key_update` mechanism to limit the lifetime of key material
without repeatedly run the protocol.

## EDHOC design NOTES
- `Message 2`: Authentication is ensured by a mac `MAC_2` (with `PRK_3e2m`)
and (in methods 0 or 2) and **additional** signature (with `sk_R`) on relevant data
(looking at **EDHOC method 0** figure below for more info about relevant data).
When only a mac is used, `PRK_3e2m` is derived from `G^(XR)`, i.e., involving
the static longer-term DH key share R. Noted from RFC: "When using a static
DH key, the authentication is provided by a MAC computed from an
ephemeral-static ECDH shared secret that enables significant reduction in
message sizes."

![EDHOC method 0](figures/edhoc-method0.png)

- `MAC_length` in `MAC_2` and `MAC_3`: if a static DH key is used, `MAC_length` is
the EDHOC MAC length of the selected cipher suite. If a signature key is used,
`MAC_length` is the hash length.
- After creating message 3, The Initiator SHOULD NOT persistently store PRK_out or
application keys until the Initiator has verified message_4 or a message protected
with a derived application key, such as an OSCORE message, from the Responder and
the application has authenticated the Responder. This is similar to waiting for an
acknowledgment (ACK) in a transport protocol. The Initiator SHOULD NOT send protected
application data until the application has authenticated the Responder.
- After processing message_3, the Responder can compute `PRK_out` and derive application
keys using the `EDHOC_Exporter` interface. The Responder SHOULD NOT persistently store
`PRK_out` or application keys until the application has authenticated the Initiator.
The Responder SHOULD NOT send protected application data until the application
has authenticated the Initiator.

## EDHOC KEM-KEM protocol design **ONGOING**
It seems obviously that the method 0 is straight-forwardly replaced by KEM; however,
signature schemem is still not quantum-safe. Replacing the PQ Signature scheme will
cost a lot of extra message sizes and regenerate long-term signature keys for
the new scheme, at least 1500 bytes if HSS-LMS is utitilized (
HSS-LMS is already assigned in COSE). So the idea is to get rid of signatures,
implicit authentication could be done through KEM (yeah more KEM keys and ciphertexts
but without extra round trips), in order to fully PQC migrated. Take a look
at STS-CB KEM (Station-to-Station-Certificate-Binding KEM) to have more detail.

In KEM-KEM design, first message, the Initiator needs to encrypt its `ID_CRED_I` using the KEM-encapsulated
key `k_auth_r`. Given that, Initiator needs to decide which cipher suite being used even
before negotiating with the responder.**ONGOING**

Moreover, using AEAD.Enc requires a 16-byte key and 13-byte IV (optionally).
As the KEM-encapsulated key is 32-byte long, cannot be directly fed into AEAD.Enc.
An idea of using HKDF for deriving a key from `k_auth_r` and `id_cred_i` sounds
reasonable, but it would significantly change the states of HKDF chain,
resulting in major changes in EDHOC.**ONGOING**:
- When use AEAD.Enc, an AAD value is needed. For example, for processing message 3 which is
AEAD encryption, `TH3` (`|| CRED_I` if `CRED_I` is presented but commonly only `ID_CRED_I` is transferred
so `CRED_I` is absent in most coummnicating sessions) plays as an AAD. In my opinion, there are 2
ways to get around**ONGOING**:
    - Create a new transcript hash value: `TH1 = H(K_auth_r, H(msg_1))` -> need major changes in design and code
    - Hash of something, e.g. `k_auth_r` -> plausible at this moment, just for experimenting
A mature design will come later.

## EDHOC NIKE protocol design

## uEDHOC-uOSCORE
### KEM integration to the first method (SIG-SIG) **Code runs well, needs formal verification model (see [this section](#protocol-verification))**
As ML-KEM particularly, or KEM generally, have not been specified in RFC, there is no reserved
COSE value for them in `CIPHERSUITE`. Currently, [this page](https://www.iana.org/assignments/cose/cose.xhtml#algorithms)
have shown some unassigned spots which could be used for KEM, and NIKE as well, experiments.
For example, look at COSE Eliplitic Curves field for avaiable spots for KEM.**SOLVED**

Maybe the sizes of public/ciphertext KEM are too big for CBOR parser/encoder.
Currently, there is an error on `ZCBOR_ERR_NO_PAYLOAD`, it could be that the public/ciphertext
KEM keys have overwritten the message payload.**SOLVED**

The big size of KEM public key and ciphertext have rose several problems.
Since the current implementation relies on many fixed, known-in-advanced, buffer
so there are some cases the predicted maximum size has to be coded,
and only ECDH key sizes are considered so that max number is terribly smaller
than KEM key sizes, leading to KEM key sizes overwrite payloads and in some
cases out bound of the CoAP message buffer (MAX 1024 as assigned in the sample code).
The current solution is to increase maximum fixed-length buffer in the code, e.g.
`buffer_sizes.h`, and in the application code as well, e.g. `samples/common/sock.h`.

### EDHOC examples in uEDHOC-uOSCORE
- Some functions need to be modified both in `initiator` and `responder`, especially
mutually agreed operations. For example, randomly-generated ephemeral keys or
test vector keys need to specified for both parties implementation
to get them complete the protocol properly.

### ECDH
**Yeah the ECDH implementation still have some issues**. I think, by
addressing those problems, or at least figuring out why/how they happened,
could help the process of KEM transition.

No Random ephemeral DH keys used: all original test vectors passed (6/6)
If Random ephemeral DH keys used, the sample does not work at all (failed at
establishing a shared key).
**UPDATED**: I have found the way to fix it. In the original code, the authors
hardcode the curve X25519 for generating ephemeral keys, though, the curve
for later authentication is either X25519 or P256 depedning on the agreed
cipher suite. To address this, I made the `ephemeral_dh_key_gen` gets
curve input dynamically depending on the chosen cipher suite.**SOLVED**

The stage of generating private/public ephemeral DH keys are out scope
of the common core `initiator.c` and `responder.c`, it lies on the
application code, e.g. example code. The reason is that, I guess, is
to flexibliy use the fixed values from test vectors and randomly-generated
ephemeral keys.

### Cipher Suite Negotiation
As the public ephemeral key G_X is sent along
with the chosen cipher suite from Initiator (the curve is already selected
by the *I*), what happens if the Responder *R* does not support that suite
and negotiate another one with a different curve? NOTE that the *I* could
send a list of supported cipher suites, so it is possible to support
different curves.

There should be a way to choose the most secure cipher suite among
all mutually suported cipher suites between *I* and *R*. For example,
a PQC suite should be chosen over a non-quantum-safe suite.

### Test vectors
Currently, only test vectors in case EC P256 are provided. There is no test vectors
for X25519, or Edward Eliptic Curve. So if you want to run the test
code successfully, make sure the the EC signature algorithm, `ecdh_sign`, is P256.

## Verification tool
### Protocol verification
SAPIC+ is the most modern, state-of-the-art platform which enables the use of
multiple verification tools, such as ProVerif, Tamarin, and DeepSec, as possible
backends. It is directly integrated within Tamarin, which means it is able to
verify the Tamarin input file. On the other hand, valid input files for ProVerif
or DeepSec could be translated from SAPIC+ as well.

### Code/implementation verification
Besides to the protocol, the actual code/implementation should be formally verified
as well to guarantee that there is no bugs related to memory safety, side-channel
attacks, or misusing. Currently, there are few options to do that:
- LIBCRUX: Spec written in HACSPEC, the generated code is Rust (state-of-the- art)
- HACL*: Spec written in F*, the generated code is C
