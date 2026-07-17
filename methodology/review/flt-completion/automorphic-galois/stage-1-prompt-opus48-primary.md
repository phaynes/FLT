PRIMARY OPUS 4.8 EARLY INTERFACE DESIGN — AUTOMORPHIC GALOIS

Repository: `/Volumes/second-store/devel/proof-forks/FLT`.
Component: `automorphic-galois`; obligations: `FLT-AUT-GALOIS`, `FLT-SUPPORT-AUTOMORPHIC`, and
`FLT-RACAR-DEF`; difficulty 10; design budget 3600s. This is early interface work only; builds remain
dependency-gated.

Work read-only. Inspect all three obligation/source-design rows, the transitive graph consumers,
automorphic form and quaternion modules, Galois representation predicates, compatible-family and
Jacquet–Langlands boundaries, source register, and available libraries. Separate data definitions,
automorphic-to-Galois realization, local-global compatibility, and support infrastructure into exact
contracts. Give complete Lean signatures, exact source locators/hypotheses, dependency order,
counterexample checks, signature probes, and bounded later build units. Reject an interface that
imports the desired MLT conclusion or leaves a generic support axiom. Verdict:
`READY-FOR-GPT-REVIEW`, `UNCERTAIN`, `REVISE`, or `OBSTRUCTION`.
