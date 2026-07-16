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
| SRC-016 | R. Taylor, lectures with notes by D. Dore and T. Feng, *Automorphy Lifting* (2018) | Theorem 2.1.1, printed p. 12; applications in sections 2.3.6--2.3.7 | Selected modularity-lifting theorem | Primary PDF visually checked; exact theorem selected, but required Lean vocabulary and repository-level bridges remain absent |

## Load-bearing source warning

The central review selected Taylor 2018, Theorem 2.1.1. Its exact source hypotheses include a
regular algebraic representation, a residual automorphic witness with matching Hodge--Tate weights,
cyclotomic-restriction irreducibility, `ell` unramified in the totally real field, crystallinity and
a Fontaine--Laffaille weight interval, and witness unramifiedness at places `v | ell`. Its conclusion
is level-free GL2 automorphy.

The theorem does not directly state the repository's quaternionic `IsAutomorphicOfLevel S`
conclusion. The source contract must therefore remain separate from the repository-level derived
theorem. Coefficient fields, stable lattices and semisimplified residual reduction, p-adic Hodge
predicates, RACAR and attached Galois representations, cyclotomic irreducibility at both concrete
applications, local-global compatibility, Jacquet--Langlands, and level specialization are explicit
open obligations. Until those definitions exist, the source route is selected but its Lean contract
is still a definition gap; no generic `Prop`, custom axiom, or level-empty shortcut may conceal it.
