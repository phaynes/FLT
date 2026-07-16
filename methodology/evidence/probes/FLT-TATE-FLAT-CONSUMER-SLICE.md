# FLT-TATE-FLAT consumer-slice result

Checkpoint: `61ca825`.

Verdict: **GENERAL NERON--OGG--SHAFAREVICH INPUT REQUIRED**.

The concrete Frey specialization does not remove the missing mathematics. The prime-to-residue-
characteristic consumer still requires a genuine reduction map on elliptic-curve points, inertia
equivariance, and injectivity on the relevant torsion subgroup. The pinned FLT/Mathlib snapshot
contains coefficient reduction but no point-specialization or torsion-injectivity theorem.

The three admissions in this subcluster have distinct roles:

- `WeierstrassCurve.torsion_unramified_of_good_reduction` needs the easy
  Neron--Ogg--Shafarevich direction.
- `WeierstrassCurve.torsion_flat_of_good_reduction` is used at residue characteristic `P.p` and
  requires the finite-flat group-scheme/Hopf-algebra construction; unramifiedness is insufficient.
- `WeierstrassCurve.resultant_Φ_ΨSq` supplies only a polynomial coprimality input and does not by
  itself construct point specialization, prove torsion injectivity, or produce the finite-flat
  Hopf algebra.

The concrete downstream representation introduces a second API boundary: the local good-reduction
theorem acts on torsion over `AlgebraicClosure K_v`, while `FreyCurve.torsion_isHardlyRamified`
uses the global module `P.freyCurve.AbsoluteTorsion P.p` restricted through the absolute-Galois
base-change map. No bridge transporting those torsion modules and inertia actions exists in the
pinned snapshot.

The smallest directly consumed final step is axiom-free once one supplies pointwise fixedness of
the global torsion module under local inertia. The open work is therefore the mathematical NOS
specialization plus this local/global torsion-action transport, not a tactic-local rewrite.

No production theorem was weakened and no admission was removed.
