Ephemeral Diffie-Hellman Over COSE is a lightweight authenticated key exchange protocol which
have been gaining interest from both academia and industry. Given the foreseeable threat of Cryptography-related Quantum Computer (CRQC), the current version of EDHOC is vulnerable as it is based on ECDH which is not quantum-safe. This project aims to the PQC migration of EDHOC protocol.

Table of contents:
[[_TOC_]]

# Project structure
```
|---pq-uoscore-uedhoc/
|---formal-verification/
|---thesis
|---docs
```
- `pq-uoscore-uedhoc` contains source code of EDHOC implementation.
- `formal-verification` contains models (Tamarin, Proverif, etc.) for formal verification.
- `thesis` contains TeX and related files to build my thesis PDF.
- `docs` contains notes, wiki pages.

# Quick Start
Open a terminal and run the following commands to build and run Initiator:
```sh
cd pq-uoscore-uedhoc/samples/linux_edhoc/initiator
make
./build/initiator
```
Open another terminal and run the following commands to build and run Responder:
```sh
cd pq-uoscore-uedhoc/samples/linux_edhoc/responder
make
./build/responder
```
At the end, both Initiator and Responder should share the same OSCORE master secret and master salt.

# Issues
TBA

# Tasks

<table>
<thead>
<tr><th>Task class</th><th>KEM-based method 0</th><th>KEM-KEM method</th></tr>
</thead>
<tbody>
<tr>
<td>Protocol Design</td>
<td>

- [x] 
</td>
<td></td>
</tr>
<tr>
<td>Formal Verification</td>
<td></td>
<td></td>
</tr>
<tr>
<td>Implementation</td>
<td></td>
<td></td>
</tr>
</tbody>
</table>
