# GPT-5.6 xhigh independent design review

Component: `class-field / FLT-CLASS-FIELD`  
Agent: `gpt56xhigh-independent-reviewer-d10`  
Model/backend: `gpt-5.6-sol` / Codex `exec`  
Verdict: **REVISE**  
Fable trigger: **NO under the conditional-only rule**

---

# Verdict: REVISE

The displayed predicates do elaborate with exactly `propext`, `Classical.choice`, and `Quot.sound`; I confirmed this directly through Lean stdin. But they are neither minimal nor yet the correct first class-field slice, and the four-way decomposition is not source- or dependency-clean enough for T2.

| Node | Finding |
|---|---|
| `CF-LOCAL-RECIP` | Conflates the full `Kˣ ≃ W_Kᵃᵇ` theorem with the derived inertia-to-residue map. These require a chosen reciprocity direction and an explicit derivation. Moreover, `localInertiaGroup` and `localTameAbelianInertiaGroup` already exist at the frozen SHA, contrary to the claimed inventory. |
| `CF-GLOBAL-RECIP` | The idele-class object remains missing, but `Field.absoluteGaloisGroupAbelianization` already exists, as do generic connected components and substantial finite-idele unit infrastructure. “Both sides absent” is false. Compatibility is also included here and repeated in `CF-COMPAT`. |
| `CF-CHAR-PRESCRIBE` | Not a minimal node. Part (a), arbitrary character globalization, has no exact registered source or type; `NonExceptional` is an opaque placeholder for the load-bearing Grunwald–Wang/product-formula conditions. Part (b), the Skinner–Wiles solvable-field theorem, is different mathematics and overlaps `FLT-AUX-LOCAL-FIELD`. |
| `CF-COMPAT` | Incorrectly bundles the local/global reciprocity diagram with determinant and conductor formulas for induced representations. The latter are induction/Artin-conductor results, not the cited class-field compatibility theorem, and belong under `FLT-INDUCED-MOD` or a separate induction-bookkeeping node. |

Key evidence:

- `GaloisRep.toLocal` already implements the proposed `localComponent` exactly, including its arbitrary-algebraic-closure-embedding caveat: [GaloisRep.lean:305](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/RepresentationTheory/GaloisRep.lean:305).
- Existing local inertia vocabulary appears at [AbsoluteGaloisGroup.lean:164](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:164).
- The topological Galois abelianization exists at [Mathlib AbsoluteGaloisGroup.lean:57](/Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/FieldTheory/AbsoluteGaloisGroup.lean:57), while restricted-product units and local ideles exist at [Units.lean:24](/Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Units.lean:24) and [LocalUnits.lean:89](/Volumes/second-store/devel/proof-forks/FLT/FLT/DedekindDomain/FiniteAdeleRing/LocalUnits.lean:89).
- The blueprint directly lists `Skinner_Wiles_CFT_trick` as an MLT dependency at [ch04overview.tex:68](/Volumes/second-store/devel/proof-forks/FLT/blueprint/src/chapter/ch04overview.tex:68), but the graph routes class field only to induced modularity and the auxiliary curve. Opus did not reconcile that source/graph mismatch.
- `SRC-004` remains explicitly incomplete, and `[cf]` supplies only a book-level citation, not an exact theorem/page locator. T2 forbids an assumption until both exact Lean type and primary-source locator are independently reviewed: [historical-assumptions.ndjson:1](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/historical-assumptions.ndjson:1). Therefore none of the four `CF-*` theorems is presently T2-nameable.

The two proposed predicates have these narrower results:

- `IsFiniteOrderCharacter`: syntactically green, but overgeneralized. With a subsingleton coefficient ring such as `ZMod 1`, `finrank A A = 1` and the image is finite, so the predicate accepts a degenerate “character.” It needs at least `[Nontrivial A]`; using `GaloisRep F A A` removes the unnecessary arbitrary rank-one module and its `Module.Finite`/`Module.Free` assumptions.
- `HasPrescribedLocalComponents`: syntactically green as a restriction-equality relation, but it neither expresses reciprocity nor proves globalization. It should reuse `χ.toLocal`, specialize to the same rank-one carrier, and remain explicitly only a relation.

The advertised `inducedRepresentation` is not a completed first-slice unit: `Representation.ind` forgets continuity, introduces an `IndV` carrier, and no existing bridge proves the finite-index, finite-rank, two-dimensional continuous `GaloisRep` required downstream.

Telemetry is adequate only as transport evidence. The listed 62 request IDs and 24 conflicting duplicate records are internally consistent, but the token totals choose the first conflicting usage record arbitrarily. No Lean build was performed, and the proposed probe file does not exist. The recorded plan-mode write also violated the requested read-only boundary, though it was disclosed.

## Fable trigger

No automatic Fable trigger under the current control rule: it is `conditional-only-if-review-uncertain`, while this is a determinate `REVISE` verdict. If diversity is nevertheless requested, scope it specifically to reconciling the source/graph consumer mismatch.

## Next exact probe

Create only `FLTMethodology.Probes.ClassFieldCharacterBoundary` with:

```lean
def IsFiniteOrderCharacter
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv
```

I verified this exact body elaborates with the standard axiom trio. Build it with:

```text
lake build FLTMethodology.Probes.ClassFieldCharacterBoundary
```

Do not add reciprocity, globalization, Skinner–Wiles, conductor formulas, or an induced `GaloisRep` until each has its own exact source, consumer, signature, and dependency node.

