# Verdict: REVISE — substantive

A distinct T1 `FLT-TAME-RESIDUE` obligation is mathematically and graph-theoretically correct.
Existing nodes do not own the whole boundary. However, the Opus artifact is not mutation-ready
because it misassigns consumers, misstates wild inertia, understates Lean risk, and misses the first
concrete Lean prerequisite.

The review was read-only. No repository files or task state were changed by the reviewer.

## Exact Lean result

These proposed signatures elaborate:

```lean
noncomputable def tameResidueChar (v : Ω K) :
    localInertiaGroup v →* (κ 𝒪ᵥ)ˣ

theorem localTameAbelianInertiaGroup_le_localInertiaGroup (v : Ω K) :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v

theorem localTameAbelianInertiaGroup_eq_ker (v : Ω K) :
    localTameAbelianInertiaGroup v =
      (tameResidueChar v).ker.map (localInertiaGroup v).subtype
```

The plain monoid hom is the correct minimal current type: `(κ 𝒪ᵥ)ˣ` has no available
`TopologicalSpace` instance, so the analogous continuous monoid-hom signature does not elaborate
without additional topology plumbing.

The exact first support theorem must also be named:

```lean
theorem isClosed_localInertiaGroup (v : Ω K) :
    IsClosed (localInertiaGroup v :
      Set (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
```

`#synth IsClosed ↑(localInertiaGroup v)` currently fails. With that closedness supplied as a
hypothesis, the natural Galois-correspondence proof of containment elaborates completely. Therefore:

- first genuine tame theorem: containment;
- first actual Lean residual: closedness of `localInertiaGroup`;
- next mathematical tranche: construct the Kummer tame character and prove the
  fixed-field/kernel identification.

The audit-only checks give exactly `[propext, Classical.choice, Quot.sound]` for
`localInertiaGroup`, `localTameAbelianInertiaGroup`, `BlueprintSGood`, and both trace-condition
functors. `cyclic_base_change` still has `sorryAx`, separately.

## Mathematical correction

The artifact's statement that wild inertia is excluded is false. If
`J_v = ker(I_v → k(v)ˣ)`, then wild inertia is contained in `J_v`, because the displayed quotient
has prime-to-residue-characteristic order. The correct relationship is:

```text
P_v ≤ J_v ≤ I_v
```

Also, `J_v < I_v` is not universal: when `k(v) = 𝔽₂`, the target unit group is trivial and
`J_v = I_v`. Keep the two subgroup declarations distinct, prove only `≤`, and never assert
universal strictness or inequality. `narrowTraceConditionFunctor` must remain on full inertia.

## Exact proposed graph mutation

After a corrected design passes the remaining review pipeline, add:

```text
obligation_id: FLT-TAME-RESIDUE
target_stage: T1
completion_targets: [T1, T2, T3]
current_state: definition-gap
direct_dependencies: []
source_refs: [SRC-004]
expected_module: FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
kernel_probe_state: signature-green
lean_risk: high
```

Do not add `FLT-LOCAL-GALOIS` upstream. That node owns balanced local deformation/cohomology
conditions, not the existing inertia definition; making it upstream would create a cycle through
`FLT-DEF-FUNCTOR`.

Add `FLT-TAME-RESIDUE` to exactly these four consumer owners:

```text
FLT-SGOOD-DEF.direct_dependencies
FLT-SUPPORT-DEFORMATION.direct_dependencies
FLT-SGOOD-SELECTED.direct_dependencies
FLT-CBASE.direct_dependencies
```

This derives:

```text
E-TAME-RESIDUE-SGOOD-DEF
E-TAME-RESIDUE-SUPPORT-DEFORMATION
E-TAME-RESIDUE-SGOOD-SELECTED
E-TAME-RESIDUE-CBASE
```

`FLT-CBASE`, not `FLT-SGOOD-SELECTED`, owns the live `cyclic_base_change` theorem. The prospective
`SelectedGood` boundary separately mentions the subgroup and therefore still needs its own future
edge. Do not add edges involving `FLT-CLASS-FIELD`, local/global reciprocity,
`FLT-AUX-LOCAL-FIELD`, or directly `FLT-MLT`.

## Source gate

`SRC-004` accurately states the target map and kernel in the blueprint, but it is explicitly an
incomplete sketch. Serre's *Local Fields* is a genuine candidate, but the exact proposition and
printed pages covering the absolute tame-residue character plus this fixed-field characterization
have not been verified from the primary text.

Therefore:

- do not add `SRC-026` yet;
- do not record a guessed proposition or page;
- require primary visual verification of the exact edition, locator, and statement match;
- no T2 historical assumption is authorized;
- although T1 globally permits `knownin1980s`, this elementary node's own completion gate must
  require only the standard axiom trio.

## Completion criteria

`FLT-TAME-RESIDUE` closes only when:

1. closedness, containment, `tameResidueChar`, and the kernel theorem compile;
2. every new theorem audits to exactly `[propext, Classical.choice, Quot.sound]`;
3. the exact primary-source locator is visually checked and independently reviewed;
4. all existing consumer signatures remain unchanged;
5. graph regeneration produces exactly the four edges above, no cycle, and no reciprocity edge;
6. the audit-only probe remains signature evidence, not mathematical discharge;
7. the existing `cyclic_base_change` admission remains separately owned by `FLT-CBASE`.

No graph mutation is authorized by this review itself. Because the revision is substantive and the
component difficulty is 10, the typed policy requires the conditional Fable diversity pass.
