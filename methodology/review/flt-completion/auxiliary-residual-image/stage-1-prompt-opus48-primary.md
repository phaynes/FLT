PRIMARY OPUS 4.8 EARLY INTERFACE DESIGN — AUXILIARY CURVE AND RESIDUAL IMAGE

Repository: `/Volumes/second-store/devel/proof-forks/FLT`.
Component: `auxiliary-residual-image`; obligations: `FLT-AUX-CURVE`, `FLT-RESIDUAL-IMAGE`, and
`FLT-AUX-LOCAL-FIELD`; difficulty 10; design budget 3600s. This is early interface work only; builds
remain dependency-gated.

Work read-only. Inspect all three obligation/source-design rows, Moret–Bailly and class-field
dependencies, potential-modularity and Taylor–Wiles consumers, source register, finite-subgroup/PGL2
library work, and local-field APIs. Separate local field construction, auxiliary elliptic-curve
existence, and residual-image adequacy into exact contracts. Give complete Lean signatures, exact
source locators and hypotheses, dependency order, failure/counterexample cases, signature probes,
and bounded later build units. Do not assume the desired residual-image conclusion in the curve
existence interface. Verdict: `READY-FOR-GPT-REVIEW`, `UNCERTAIN`, `REVISE`, or `OBSTRUCTION`.
