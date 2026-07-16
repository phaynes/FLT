# GPT-5.6 xhigh corrected source adjudication

Review commit: `5d376d153ad1641113781c317ee9ab69d38f200b`

Model: `gpt-5.6-sol`; reasoning tier: `xhigh`; elapsed time: 74 seconds; session: fresh, bounded
cross-review.

## Verdict

**CORRECTED ROUTE REQUIRES REPAIR**

Primary-source correction: Taylor 2018, Theorem 2.1.1 requires the residual automorphic witness to
be unramified at places `v | ell`. This is an at-`ell` condition. The repository's
`IsAutomorphicOfLevel ell ... empty` controls places away from `ell` and cannot encode it.

The correction makes both applications in the notes' auxiliary-curve route locally compatible:
good reduction at the two selected primes supplies the relevant at-prime condition. It removes the
false need for an everywhere-unramified witness.

The accepted source boundary is level-free GL2 automorphy for a representation over an algebraic
`ell`-adic coefficient field, with a chosen stable lattice and semisimplified residual reduction.
The repository-level quaternionic conclusion is a separate derived theorem. Required intervening
definitions and theorems are:

1. coefficient field, lattice, and semisimplified residual reduction;
2. crystalline, Hodge--Tate, regular-algebraic, and Fontaine--Laffaille predicates;
3. RACAR objects and attached Galois representations;
4. cyclotomic restriction irreducibility;
5. coefficient and residual comparison;
6. the source-exact, level-free Taylor contract;
7. the two concrete auxiliary-curve applications;
8. GL2-to-repository automorphy and quaternionic level specialization;
9. surjective `R -> T`, nilradical factorization, eigenform extraction, and trace compatibility.

New mathematical evidence: yes. The corrected primary-source condition both validates the route's
two local applications and refutes the prior Lean encoding.
