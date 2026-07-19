# Class-field implementation handoff — 2026-07-19

## Status and scope

This note records the bounded class-field proof work performed on the isolated worktree
`/Volumes/second-store/devel/proof-forks/FLT-class-field`.

- Branch: `task/flt-class-field-proof-20260719`
- Captured implementation HEAD before this note: `9754c2c41fa9feb94b02e9dd892c3befecc915f1`
- Common starting point: `1f6d11caee718028bf783c968511d34865ffd9f0`
- Governed task: `task:fg-flt-ra-math-source-design-20260716`
- Remote branch: `origin/task/flt-class-field-proof-20260719`

This is substantial kernel-clean progress, but **not completion of the aggregate class-field
component**. The tame-residue/kernel lane has been reduced to one explicit local value-group
theorem. The larger class-field programme still contains global/local reciprocity, idele topology,
discreteness/profiniteness, and globalization/local-prescription obligations.

## Proof source changed

The implementation is in:

- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`
- `FLTMethodology/Probes/TameResidueBoundary.lean`

Relative to the common starting point the branch changes these two files by 555 insertions and
3 deletions.

## Kernel-clean results added

The branch constructs and proves the plumbing needed for the tame residue character and its
kernel:

1. Root-of-unity reduction and cardinality results:
   - `integralClosureRootsEquiv`
   - `integralClosure_card_rootsOfUnity`
   - `tameRootsReduction_at_place_surjective`
   - `tameRootsReductionEquiv`
2. The Kummer ratio and its root-of-unity realization:
   - `galoisRatio_pow_eq_one`
   - `integralGaloisRatioRoot`
   - `tameUniformizer`
   - `tameKummerRoot`
   - `tameKummerRatioRoot`
3. The tame residue character and its action laws:
   - `tameResidueCharFun`
   - `tameResidueCharFun_one`
   - `tameResidueCharFun_mul`
   - `tameResidueChar`
4. Inertia/root-lifting facts:
   - `localInertia_residue_smul_eq`
   - `localInertia_fix_tameRoot`
   - `exists_tameRoot_mem_fixedField_of_integral_unit`
5. Kernel inclusions and conditional exactness:
   - `localTameAbelianInertiaGroup_le_mapped_tameResidueKer`
   - `tameKummerRoot_fixed_of_mem_ker`
   - `mapped_tameResidueKer_le_localTameAbelianInertiaGroup_of_decomposition`
   - `localTameAbelianInertiaGroup_eq_ker_of_decomposition`
   - `localTameAbelianInertiaGroup_eq_ker_of_fixedFieldUniformizerDecomposition`

The proof deliberately separates elementary Kummer/root-lifting/subgroup reasoning from the
remaining local ramification theorem.

## Exact remaining mathematical leaf

The residual contract is:

```lean
def FixedFieldUniformizerDecomposition : Prop :=
  ∀ {u : Kᵥᵃˡᵍ}, u ≠ 0 →
    u ∈ IntermediateField.fixedField (localInertiaGroup v) →
    ∃ (m : ℤ) (a : Kᵥᵃˡᵍ),
      IsIntegral 𝒪ᵥ a ∧ IsIntegral 𝒪ᵥ a⁻¹ ∧
      a ∈ IntermediateField.fixedField (localInertiaGroup v) ∧
      u = (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v)) ^ m * a
```

Mathematically, it says every nonzero element of the inertia fixed field is an integral unit times
an integer power of the selected base uniformizer.

The theorem
`localTameAbelianInertiaGroup_eq_ker_of_fixedFieldUniformizerDecomposition` proves the exact kernel
equality from this single premise. Therefore the next implementation should prove the value-group
contract rather than reopen the already discharged character and Kummer plumbing.

## Verification performed

The following checks passed at the captured implementation HEAD:

```text
lake build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
lake build FLTMethodology.Probes.TameResidueBoundary
lake build FLT FLTMethodology
```

The final umbrella build reported:

```text
Build completed successfully (9035 jobs).
```

The probe audits every new exported declaration to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No new `sorryAx`, custom axiom, `admit`, `unsafe`, or `native_decide` dependency was introduced by
these declarations.

## Commit sequence

```text
9e53819  prove tame residue character
836a6f0  prove tame root lifting equivalence
7bff600  prove inertia fixes tame roots
fb7b8fe  prove tame kernel forward inclusion
a8e4a12  prove fixed-field unit root lifting
f2d1c83  isolate final tame valuation contract
9754c2c  reduce tame kernel to value group
```

Every commit carries the governed task identifier in its full commit message and was pushed to the
remote task branch.

## Safe continuation

1. Start from this branch or cherry-pick the commits above in order.
2. Preserve `FixedFieldUniformizerDecomposition` as the next exact proof boundary.
3. Establish it using the value group of the maximal unramified extension/fixed field and the
   valuation of the chosen uniformizer.
4. Re-run the targeted module, probe, axiom audit, and full umbrella build.
5. Do not mark `FLT-CLASS-FIELD` complete merely because the tame-residue subgraph closes; audit the
   separate reciprocity, idele-topology, and globalization obligations first.
