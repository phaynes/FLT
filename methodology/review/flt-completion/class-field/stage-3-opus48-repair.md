# Opus 4.8 bounded design repair

Component: `class-field / FLT-CLASS-FIELD`
Agent: `opus48-primary-designer-d10`
Model/backend: `claude-opus-4-8` / `claude-code`
Attempt: 2 (attempt 1 was operator-cancelled, NO VERDICT)
Verdict: **READY-FOR-GPT-REVIEW**

---

The repaired design is complete, cross-verified against the repository, and written to the plan file. Here is the complete repaired design.

---

# FLT-CLASS-FIELD — Repaired Design (Opus d10 primary repair, attempt 2)

**Ladder verdict: `READY-FOR-GPT-REVIEW`** · Disposition: INTERFACE-FIRST · Read-only pass, no repo/control-file edits.

> Transport disclosure (honest, mirroring the defect the prior attempt was flagged for): plan mode persisted this design to `~/.claude/plans/opus-4-8-bounded-design-snoopy-tide.md`. No repository file was edited; no in-repo external plan file was created; no model was launched; nothing was promoted.

## What was wrong, and what I verified directly

The Stage-1 (Opus 4.8) four-way split earned a correct **REVISE** from Stage-2 (GPT-5.6 xhigh). I confirmed every Stage-2 claim against source, and reconciled one thing neither artifact resolved:

| Disputed claim | Verified truth (path) |
|---|---|
| `localComponent` is new | **False** — `GaloisRep.toLocal = ρ.map (algebraMap _ _)` already exists (`GaloisRep.lean:309`); rank-one↔character bridge `FramedGaloisRep.equivChar` exists (`:189`) |
| local inertia absent | **False** — `localInertiaGroup` (`AbsoluteGaloisGroup.lean:167`), `localTameAbelianInertiaGroup` (`:178`, = kernel of `I_v→𝒪_{F_v}^×→k(v)^×`, carries `TODO: show this is the right group`) |
| `(Γ F)^ab` absent | **False** — `Field.absoluteGaloisGroupAbelianization` (Mathlib `FieldTheory/AbsoluteGaloisGroup.lean:59`) |
| idele infra wholly absent | **False, partial** — `FiniteAdeleRing.unitEmbedding : Kˣ →* (FiniteAdeleRing R K)ˣ` (its **cokernel is the missing idele class group**), `RestrictedProduct.unitsEquiv`, `localUniformiserUnit`. Missing only: `(𝔸_F)ˣ/Fˣ`, `π₀`, Artin map |
| `IsFiniteOrderCharacter` sound | **Over-general** — `A=ZMod 1` accepts a degenerate character; needs `[Nontrivial A]` + rank-one `GaloisRep F A A` |
| Skinner–Wiles belongs to class-field | **No** — it is a `\uses` of `modularity_lifting_theorem` (`ch04overview.tex:68`), overlapping `FLT-AUX-LOCAL-FIELD` |

**Source/graph mismatch exposed (requirement 2):** the genuinely-consumed local-CFT object is the derived map `I_v→𝒪_{F_v}^×→k(v)^×` and its kernel `J_v` (`ch04overview.tex:44–47`), consumed by the **S-good representation definition inside the MLT** ("trace = 2 on `J_v`", `:50–60`) — already present in-repo as `localTameAbelianInertiaGroup`. The graph routes class-field only to INDUCED-MOD/AUX-CURVE, representing neither this MLT consumer relationship nor the Skinner–Wiles dependency. `library_candidates` `["NumberField.AdeleRing","IsLocalClassField","ContinuousCharacter"]` is **1/3 real** (last two do not exist).

## Repaired node decomposition

Class-field **owns**:

| Node | Content | State | T2-nameable? |
|---|---|---|---|
| **CF-CHAR** | predicates `IsFiniteOrderCharacter`, `HasPrescribedLocalComponents` (reuse `χ.toLocal`); relations only | **elaborates now** | **YES** |
| **CF-INERTIA-RESIDUE** | derived `I_v→k(v)^×` + kernel `J_v` | **PARTIAL** (`localTameAbelianInertiaGroup` exists; correctness theorem open) | object named; theorem open |
| **CF-LOCAL-RECIP** | full iso `Kˣ ≃ₜ (W_K)^ab` | **DEFINITION-GAP** (local Weil group absent) | **NO** |
| **CF-GLOBAL-RECIP** | `π₀((𝔸_F)ˣ/Fˣ) ≃ₜ (Γ F)^ab`, **incl.** local–global compat clause | **DEFINITION-GAP** (idele class group + `π₀` absent; codomain exists) | **NO** |
| **CF-CHAR-GLOBALIZE** | Grunwald–Wang existence + explicit non-exceptionality | **DEFINITION-GAP** (needs real source) | **NO** |

**Routed OUT (fixes requirements 2 & 3):** `Skinner_Wiles_CFT_trick` → **FLT-AUX-LOCAL-FIELD**; `det(Ind χ)`/`cond(Ind χ)` induction bookkeeping → **FLT-INDUCED-MOD** (or new `IND-CONDUCTOR`). **No duplication (req 5):** local–global compatibility lives *only* inside `CF-GLOBAL-RECIP`; the old `CF-COMPAT` node is deleted. **Split & direction (req 4):** `CF-INERTIA-RESIDUE` is defined independently of the full `CF-LOCAL-RECIP` iso (as the repo already does); reciprocity direction pinned globally to the arithmetic Artin map `Kˣ→(W_K)^ab`, uniformizer ↦ geometric Frobenius.

## Exact Lean signatures, dependency order (Slice A — the only node buildable now)

```lean
namespace FLT.PotentialModularity.ClassField

def IsFiniteOrderCharacter
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F] {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv

end FLT.PotentialModularity.ClassField
```
No `localComponent` (it *is* `χ.toLocal`); no `inducedRepresentation` (`Representation.ind` forgets continuity/finite-index → belongs to FLT-INDUCED-MOD). Slice-B targets held as named future obligations only, no fabricated signatures.

## Minimal first elaborating probe (req 7)
`FLTMethodology/Probes/ClassFieldCharacterBoundary.lean`, Slice-A only, mirroring `Probes/MLTSourceBoundary.lean`:
`lake build FLTMethodology.Probes.ClassFieldCharacterBoundary` then `#print axioms` on both predicates. **Pass = `{propext, Classical.choice, Quot.sound}` only, no `sorryAx`.** (Not built in this design-only pass.)

## Counterexample / stop-loss gates (req 7)
CE-1 subsingleton `ZMod 1` → `[Nontrivial A]` mandatory · CE-2 Grunwald–Wang order-8-at-2 → explicit `NonExceptional` hypothesis, spelled out, never opaque (unconditional existence is **unsound**) · CE-3 continuity → keep `GaloisRep`, never bare `MonoidHom` · CE-4 finite order → keep finite-range clause · CE-5 induction direction (`Γ E→Γ F`) · **circularity guard**: no node mentions `IsAutomorphicOfLevel`/curve existence · **S1** idele-class/Weil-group don't land → escalate to source-vendoring, keep CF-CHAR + CF-INERTIA-RESIDUE · **S2** Skinner–Wiles still bundled → REVISE · **S3** `NonExceptional` unstatable → scope-restrict or OBSTRUCTION on that sub-node.

## Revised component DAG (req 7)
```
CF-CHAR (predicates; ELABORATES NOW) ─────────────┐
                                                   ├─► CF-CHAR-GLOBALIZE ─► FLT-INDUCED-MOD
CF-LOCAL-RECIP ─► CF-GLOBAL-RECIP (incl. compat) ──┘                     └─► FLT-AUX-CURVE
CF-INERTIA-RESIDUE (PARTIAL; independent of full recip) ─► FLT-AUX-CURVE / MLT S-good def
routed OUT:  Skinner_Wiles_CFT_trick ─► FLT-AUX-LOCAL-FIELD ;  det/cond(Ind χ) ─► FLT-INDUCED-MOD
```

## Not-yet-T2-nameable (req 8)
`CF-LOCAL-RECIP`, `CF-GLOBAL-RECIP`, `CF-CHAR-GLOBALIZE` are **not T2-nameable**: domain objects (local Weil group; idele class group + `π₀`) absent, and `SRC-004`/`[cf]` give only book-level citations, no exact theorem/page locator — `historical-assumptions.ndjson:1` requires exact Lean type **and** primary-source locator, independently reviewed. `CF-INERTIA-RESIDUE`'s object is named but its characterizing theorem is open. Only **CF-CHAR**'s two predicates are T2-nameable now. **No generic authority axiom, `sorry` scaffold, automorphy claim, or auxiliary-curve existence is hidden in any node.**

---

**Verdict: `READY-FOR-GPT-REVIEW`.** The omnibus `classField_package` is replaced by a source-faithful, non-circular split whose only buildable-now node (CF-CHAR) elaborates kernel-clean over existing `GaloisRep`/`toLocal` vocabulary; the reciprocity nodes are honestly held at definition-gap with corrected inventory; Skinner–Wiles and induced-conductor bookkeeping are routed off-node with the source/graph mismatch exposed for a follow-up graph edit; and every not-yet-nameable interface is explicitly flagged. Ready for GPT-5.6 xhigh independent review.

