# GPT-5.6 xhigh independent review — tame-residue U3

Reviewed commit: `29660f6`

Verdict: `PASS-BUILD-U3`.

The command-capable reviewer independently reproduced both U3-A proof routes and the controller's
finite-field cardinality construction.

## Findings

- The Opus local-ring theorem is valid for commutative local rings with zero divisors. It is the
  smaller reusable public result; the controller's `IsDomain` proof is correct but unnecessarily
  restrictive for the generic injection theorem.
- The finite-field counting equivalence is correct, including:
  - the `q = 2` case;
  - construction of `NeZero (q - 1)`;
  - `Nat.card` / `Fintype.card` conversions;
  - injectivity of the finite-field unit map;
  - the `card_rootsOfUnity` upper bound; and
  - the direction

    ```lean
    (IsLocalRing.ResidueField 𝒪ᵥ)ˣ ≃*
      rootsOfUnity (Nat.card (IsLocalRing.ResidueField 𝒪ᵥ) - 1)
        (IsLocalRing.ResidueField S)
    ```

    where `S := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)`.
- `IsLocalRing.ResidueField.map (algebraMap 𝒪ᵥ S)` is an injective field homomorphism. The
  required `ValuationRing`, `IsLocalRing`, `IsDomain`, `Finite`, and `IsLocalHom` instances all
  synthesize at the production site.
- The combined reduction map has codomain `(IsLocalRing.ResidueField 𝒪ᵥ)ˣ` and is injective.
- The counting proof establishes residue-field descent only. It does not establish surjective
  lifting from the integral closure; that remains the U5 Henselian boundary.
- Every accepted declaration audited exactly to:

  ```text
  [propext, Classical.choice, Quot.sound]
  ```

  No `sorryAx` occurred.

## Authorized bounded surface

Add to `FLT/Mathlib/RingTheory/RootsOfUnity/ResidueField.lean`:

- the two Opus local-ring declarations; and
- the four `FiniteField.unitsToRootsOfUnity*` declarations.

Add to `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`:

- `isUnit_card_sub_one_ICv`;
- `residueUnitsEquivRootsOfUnity_at_place`;
- `tameRootsReduction_at_place`; and
- `tameRootsReduction_at_place_injective`.

Extend `FLTMethodology/Probes/TameResidueBoundary.lean` with exact checks and axiom audits for those
declarations.

`FLT-TAME-RESIDUE` remains open with all four outgoing edges unchanged. U4–U6, source/T2 promotion,
graph promotion, reciprocity, and historical assumptions remain unauthorized.

## Typed diversity disposition

Fable: `SKIP`.

Reason: difficulty 8 is above 7, but the mandatory GPT review returned a definite PASS rather than a
substantive mathematical or statement-level `REVISE`. Running the scarce diversity lane would
violate the operator's typed escalation rule.

