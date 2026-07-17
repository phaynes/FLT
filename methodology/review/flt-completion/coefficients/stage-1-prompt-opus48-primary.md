PRIMARY OPUS 4.8 EARLY INTERFACE DESIGN — MLT COEFFICIENTS

Repository: `/Volumes/second-store/devel/proof-forks/FLT`.
Component: `coefficients`; obligation: `FLT-MLT-COEFFICIENTS`; difficulty 10; design budget 3600s.
This is early interface work only. Its later Lean build remains gated by Wave 0.

Work read-only. Inspect the exact obligation and source-design rows, proof graph and consumers,
source register, existing MLT/Taylor 2018 probes and reviews, coefficient-field/lattice code, and
relevant Mathlib declarations. Freeze the smallest source-faithful package of coefficient ring,
field, embedding, lattice, reduction, and scalar-extension theorems actually required by the
selected MLT interface. Give complete namespace-qualified Lean signatures intended to elaborate,
exact source locators and hypothesis translations, dependency order, counterexample/overstatement
checks, signature probes, and bounded later build units. Distinguish already-proved library facts
from absent obligations. Return `READY-FOR-GPT-REVIEW`, `UNCERTAIN`, `REVISE`, or `OBSTRUCTION`.
