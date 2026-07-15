# Source register

This register distinguishes the repository's formal declarations from mathematical sources. A
source citation does not make a Lean declaration proved, and a Lean scaffold does not establish
that a cited theorem has the hypotheses required here.

| ID | Source | Locator | Role | Verification state |
|---|---|---|---|---|
| SRC-001 | Imperial College London FLT repository | commit `ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b` | Frozen formal baseline | Git object verified |
| SRC-002 | FLT blueprint | `blueprint/src/chapter/ch02reductions.tex` | FLT to Mazur plus Frey reducibility | Read at frozen commit |
| SRC-003 | FLT blueprint | `blueprint/src/chapter/ch03freyreduction.tex` | Hardly-ramified lift, compatible-family, and 3-adic route | Read at frozen commit |
| SRC-004 | FLT blueprint | `blueprint/src/chapter/ch04overview.tex` | Potential modularity and modularity-lifting sketch | Read; explicitly incomplete upstream |
| SRC-005 | J.-P. Serre, *Sur les représentations modulaires de degré 2 de GQ*, Duke Math. J. 54 (1987) | DOI `10.1215/S0012-7094-87-05413-5`, especially section 4.1 | Frey representation ramification and irreducibility reductions | Primary source identified; theorem-by-theorem source-condition audit open |
| SRC-006 | B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977) | DOI `10.1007/BF02684339` | Rational elliptic-curve torsion bound | Primary source identified; T3 formalization open |
| SRC-007 | G. Poitou, *Sur les petits discriminants* (1977) | Exp. 6, table on p.17 as cited by upstream | Explicit root-discriminant bound | Primary source identified; T3 formalization open |
| SRC-008 | A. Wiles, *Modular elliptic curves and Fermat's last theorem*, Ann. Math. 141 (1995) | DOI `10.2307/2118559` | Original modularity argument and deformation/Hecke input | Primary source identified; exact compatibility with the selected modern route open |
| SRC-009 | R. Taylor and A. Wiles, *Ring-theoretic properties of certain Hecke algebras*, Ann. Math. 141 (1995) | DOI `10.2307/2118560` | Taylor-Wiles patching | Primary source identified; exact selected theorem interface open |
| SRC-010 | C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture II*, Invent. Math. 178 (2009) | DOI `10.1007/s00222-009-0206-6` | Compatible-family / prime-switching strategy | Primary source identified; specialization audit open |
| SRC-011 | L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem I, II* (1989) | Ann. Sci. ENS 22, 161–194 | Prescribed-local-behaviour point construction | Primary source identified; exact Lean statement absent |
| SRC-012 | R. Taylor, *On the meromorphic continuation of degree two L-functions* (2006) | Theorem 3.3 | Near-match for modularity lifting | Requires the prime to split completely in the totally real base field, crystalline weights in range, residual irreducibility after the specified cyclotomic quadratic extension, and an everywhere-unramified residual automorphic input; these are not the blueprint's current temporary contract |
| SRC-013 | T. Gee, *Modularity lifting theorems* (2022) | Theorem 5.2 | Near-match for modularity lifting | Allows the prime to be unramified, but requires crystalline local representations with matching bounded distinct Hodge-Tate weights and residual image containing `SL₂(F_p)`; the last condition is stronger than the blueprint target |
| SRC-014 | Barnet-Lamb, Gee, Geraghty, Taylor, *Potential automorphy and change of weight* (2014) | Route cited as the Brauer-theorem compatible-family trick | Potential automorphy and compatible families | Primary source identified; exact specialization audit open |
| SRC-015 | P. de Smit and H. Lenstra, representability result cited in source | Proposition 2.3(1), locator recorded in `FLT/Deformations/Representable.lean` | Deformation-functor corepresentability | Exact bibliographic record and source-condition audit open |

## Load-bearing source warning

The frozen blueprint states that it is not certain where to find the exact modularity-lifting
theorem it sketches, and identifies only near-references with mismatched hypotheses. That is a
statement-design blocker until an exact primary-source route or a proved derivation from sourced
theorems is fixed. It must not be hidden behind a generic `sorry`, a custom axiom, or an informal
claim that the result is standard.

A possible repair for review is to strengthen the *constructed auxiliary field* so the prime splits
completely and then instantiate Taylor's exact theorem, while handling the residual representations
that fail Taylor's cyclotomic irreducibility condition by a separately sourced induced/solvable-image
argument. This changes neither FLT nor the public terminal, but it is not accepted until every local
condition and the residual automorphic input have exact Lean contracts and primary-source support.
