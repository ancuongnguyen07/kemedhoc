# Master's Thesis: PQ EDHOC
Supervisor: Russell Lai | Advisor: Sampo Sovio

### What is the expected time frame of the thesis, i.e. when do you plan to start and finish?
In the best scenario, it should be done in 6 months. I already started in February so
it is supposed to be finished by the end of July.

### What would be expected amount of supervision?
Yes, as you suggested, meeting once per month sounds good.

### Do you plan to develop new NIKE/KEM, or just take existing ones and see if they fit into EDHOC?
Currently, there is no plan for inventing new ones. I would pick efficient, standardised ones
and integrate them into EDHOC.

### What is the scope of PQ schemes? Is it only lattices or also isogeny-based, multivariate-based
### and hash-based schemes?
Well, there is no fixed scope of PQ schemes as long as they are secure, through proofs or
believeness, and show reasonably small key sizes and acceptable computational time.
As far as I know, there have been only 2 PQ NIKE seems pratical enough, namely
SWOOSH and CTIDH (SWOOSH is even not completed, where only the passive model is
formally analyzed and experimented in the paper). On the other hand, CTIDH, which
is isogeny-based, is more promising, especially in the use cases of EDHOC where small
message sizes is the top priority, due to its compact public key sizes.

### Have you looked into the literature? Presumably, there is already a sizable body of work
### PQ DH. How does the proposed topic fit into the literature?
Yes, there are many previous works on post-quantum DH, but they chose KEM as a straight-forward
and sole approach with the extra cost of additional round trips. In my proposal, KEM is still
considered for the first method due to its maturity, though, NIKE is a new player which
solves the threat of quantum computing without introducing extra round trips, keeping
low latency which is crucial in constrained settings. Moreover, there have not been
formal works on implementing and benchmarking these two pratical PQ NIKE in widely-deployed
protocols, this work would hopefully skrink this gap.

### When you say "Modifies EDHOC design to adapt KEM for the method 0, and PQ NIKE, SWOOSH or
### CTIDH, for the remaining methods", do you have a rough idea on how to do it? Especially
### for lattice-based schemes, this seems difficult (depending on what efficiency goal you are thinking about)
Yes, I have a rough idea and have somehow played around with it:
- Method 0: both parties mutually authenticate through signatures. KEM, any secure PQ KEMs, is a straight-forward
replacement in this case as shown in many previous works KEMTLS [1], PQ WireGuard [2], STS-KEM [3],
and even in the EDHOC RFC [4]. Intuitively, Initiator (I) generates a public/private
key pair `pk_i`, `sk_i`, then sends `pk_i` to Responder (R). R encaps using `pk_i` to produce
`ct` and `shared_key`, and then sends `ct` to I. Finally, I decaps `ct` using `sk_i` to
obtain the `shared_key`.
- Method 1/2/3: either or both parties mutually authenticate through static DH keys.
If KEM is utitlized it will introduce extra round trips, which is not desirable
in constrained settings. Hence, a NIKE, which does not require an interactivity
between communicating parties, fits the role in those authentication methods.

Regarding to efficiency goal, currently I do not have a upper bound for it.
I have noticed that lattice-based schemems would drastically increase the
message sizes, 30-fold at least compared to what we have with ECDH.
My plan is to benchmark the PQ variant of EDHOC in constrained devices,
i.e. nRF52840, and see how big the overhead is compared to the results
shown in [4]. I could adapt some engineering techniques to optimize
the packet sizes, but the bottleneck obviously lies on the scheme itself
so it is great if I could have some insights from you, a crypto expert.s

### Meeting time
Russell suggested a meeting time 16-17:00 Wednesday 5th March, remotely or at Aalto campus.
(Remote meeting sounds more reasonable)