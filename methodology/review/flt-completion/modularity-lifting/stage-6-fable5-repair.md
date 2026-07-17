# Stage 6 — Second Fable repair of modularity-lifting source boundary — FINAL

## Verdict: DESIGN-VIABLE

Read-only turn. Repository untouched (the dirty `methodology/control/*.ndjson` entries and
`.kg-model-bridge/` predate this session — live orchestration state). All probes ran in
`/tmp/flt-stage6/Probe{A,B,C,D}.lean` against the pinned toolchain `leanprover/lean4:v4.32.0-rc1`
with prebuilt oleans; nothing persisted.

## Context

Stage-5 GPT-5.6 xhigh returned REVISE-SUBSTANTIVE against the Stage-4 Opus synthesis with four
defects: (1) H4 uses ordinary `GaloisRep.IsIrreducible` on `coeff.rhoBar` (weaker than absolute
irreducibility — C₃ ⊂ GL₂(𝔽₂) splits over 𝔽₄); (2) `regular`/`fontaineLaffaille` constrain a free
`weights` never equated to the representation's actual Hodge–Tate weights; (3) H2 residual agreement
is same-field, not closure-comparison with explicit embeddings; (4) the dependency ledger reverses
the live `FLT-MLT-SOURCE`/`FLT-RESIDUAL-IMAGE` edge. This design repairs exactly those four while
preserving the five-unit repository boundary verbatim (re-audited green).

## The four repairs (probe-verified signatures)

### R1 (defect 1) — neutral absolute-irreducibility vocabulary, new node FLT-ABSIRRED-VOCAB

File (future, build-enabled stage): `FLTMethodology/Probes/ResidualAbsoluteVocabulary.lean`,
namespace `FLTMethodology.Taylor2018`. Named common residual closure = `AlgebraicClosure (ZMod ell)`
with scoped discrete instances (`⊥`, `⟨rfl⟩`) — same as coefficients stage-6. Topology-free defs
(via `toRepresentation` + `Representation.baseChange`):

- `IsAbsolutelyIrreducibleInResidualClosure (ell) (f : k →+* AlgebraicClosure (ZMod ell))
   (ρbar : GaloisRep K k W) : Prop := letI := f.toAlgebra; Representation.IsIrreducible
   (Representation.baseChange (AlgebraicClosure (ZMod ell)) ρbar.toRepresentation)`
- `IsCyclotomicAbsolutelyIrreducibleInResidualClosure ell f ρbar :=
   IsAbsolutelyIrreducibleInResidualClosure ell f (ρbar.map (algebraMap F (CyclotomicField ell F)))`
   (restrict to F(ζ_ell) FIRST, then extend coefficients)
- Provider contract (statement only, first residual goal): `ClosureImpliesClassAbsIrred` — closure
  form ⇒ FLT ∀-class `Representation.IsAbsolutelyIrreducible.{max uK uk uW, uK, uk, uW}` (the form
  consumed by `Deformation.Representable` and aux-residual-image stage-2). Universe MUST be pinned
  explicitly (probe showed metavariable error otherwise).

H4 field becomes `cycloIrreducible : IsCyclotomicAbsolutelyIrreducibleInResidualClosure ell embRes
coeff.rhoBar` with a single new DATA field `embRes : κ(O) →+* AlgebraicClosure (ZMod ell)` shared by
H2 and H4 (one embedding owner; two embeddings would reintroduce the ∃ι class of bug).

### R2 (defect 2) — weights pinned to the representation

Add gated field `weightsExtracted : ‹HasHodgeTateWeightData r weights›` (owner FLT-MLT-PADIC-HODGE
Tier-2 = G2 extraction `GaloisRep.hodgeTateWeightsAt` ∘ G5 place map; ι-free — ι stays on the
witness side of H3). ProbeD machine-proves the defect was real: `{3,4}` passes both stage-4
constraints (trio axioms) yet ≠ `{-1,0}`.

### R3 (defect 3) — closure-comparison H2

`residualAgree : ‹AgreeInResidualClosure ell embRes (embAux witness) coeff.rhoBar
(attachedResidual ι witness)›` — reuses coefficients stage-6 U3 `AgreeInResidualClosure`
(explicit embeddings, delegates to landed `ResidualModelsAgreeAfterExtension
(kbar := AlgebraicClosure (ZMod ell))`; re-probed green here, incl. k₁ ≠ k₂). Identical residue-field
ownership is NOT independently proved (attachedResidual is a RACAR gap) ⇒ closure form mandatory.

### R4 (defect 4) — graph correction (rows to be applied at next authorized mutation stage)

- NEW obligation `FLT-ABSIRRED-VOCAB`: lean_declarations = the two irreducibility defs + transport
  contract; expected_module `FLTMethodology.Probes.ResidualAbsoluteVocabulary` (eventual home
  `FLT.ModularityLifting.ResidualVocabulary`); direct_dependencies `[]`.
- DELETE edge `E-MLT-SOURCE-RESIDUAL-IMAGE` (matches aux stage-2 mandate verbatim).
- ADD `E-ABSIRRED-VOCAB-MLT-SOURCE` (definition), `E-ABSIRRED-VOCAB-RESIDUAL-IMAGE` (definition).
- `FLT-RESIDUAL-IMAGE.direct_dependencies := [FLT-HR-DEF, FLT-ABSIRRED-VOCAB, FLT-AUX-CURVE]`.
- `FLT-MLT-SOURCE.direct_dependencies += FLT-ABSIRRED-VOCAB` (others unchanged).
- Concrete residual proof meets the source contract only at FLT-POTMOD (edges already live).
- Acyclic: VOCAB → {SOURCE, RESIDUAL-IMAGE} → {MLT, POTMOD, TW-PRIMES}. FLT-MLT-SOURCE consumes
  no downstream application proof; the stage-4 ledger line "SOURCE consumes RESIDUAL-IMAGE" is struck.
- Out of scope, flagged: aux stage-2's HR-DEF → AUX-CURVE redirection stays with the FLT-413 packet.

## Probe evidence (exact `#print axioms`)

- ProbeA (4 new sigs): all EXACTLY `[propext, Classical.choice, Quot.sound]`, exit 0.
- ProbeB (five-unit re-audit, verbatim stage-4 P-A): all five EXACTLY the trio.
- ProbeC: `tripwire` (applies sorried `cyclic_base_change` to the trio slots) =
  `[propext, sorryAx, Classical.choice, Quot.sound]` — evidence only, never persisted;
  H4-shape and mismatched-fields H2-shape examples elaborate clean.
- ProbeD: `freeWeightWitness_passes_stage4_constraints`, `freeWeightWitness_is_not_weightTwo`
  both PROVED with exactly the trio.

## Remaining provider theorems

- FLT-ABSIRRED-VOCAB: `ClosureImpliesClassAbsIrred` proof (Burnside/Schur, finite-dim; FIRST
  residual goal); embedding-independence lemma (named); aux stage-2 preserves-image transport.
- FLT-MLT-COEFFICIENTS: coeff stage-6 units (CoefficientData tower, GroupContract/BN,
  LatticeIndependent; first goal `IsLocalHom (algebraMap ℤ_[p] (IsLocalRing.ResidueField O))`).
- FLT-MLT-PADIC-HODGE Tier-2: G1 `IsCrystallineAt`, G2 `hodgeTateWeightsAt`, NEW
  `HasHodgeTateWeightData` (G2∘G5), G4 flat⇒crystalline (dominant risk), G6/G7 dual/det transport.
- FLT-RACAR-DEF (BLOCKED): witness, `attachedResidual` (+ residue field + `embAux`),
  `witnessWeights`, H7, level-free conclusion.

## First residual Lean goal

`⊢ IsAbsolutelyIrreducibleInResidualClosure ell f ρbar →
   Representation.IsAbsolutelyIrreducible.{max uK uk uW, uK, uk, uW} ρbar.toRepresentation`
via order-embedding of `Subrepresentation` lattices under (faithfully flat) coefficient extension +
Burnside over the algebraically closed `AlgebraicClosure (ZMod ell)` (needs `Module.Finite k W`).

## Hostile findings (coherence flags, not new disagreements)

1. Repo has THREE absolute-irreducibility spellings (∀-class in Deformations/Irreducible.lean;
   `Slop.OddRep` closure-form at `AlgebraicClosure k`; aux stage-2 composite). The vocab node is the
   single MLT spelling; bridges named. The OddAbsIrred equivalence needs a 1-dim 1-eigenspace —
   fails over 𝔽₂ for the C₃ counterexample (M−I invertible), consistent with stage-5.
2. `Representation.IsAbsolutelyIrreducible` is FLT-LOCAL, not Mathlib (aux stage-2's "the pin
   already has" is true only counting the FLT tree).
3. Discrete-topology instances on the closure are declared `local` in two packets (coefficients U3
   and the vocab file) — eventually one shared home to avoid divergence; named coherence point.

## Verification (later, build-enabled stage — NOT this turn)

1. Persist P-A (five units) + ResidualAbsoluteVocabulary together only after the mandatory GPT
   review of this stage passes (S6 gate); every `#print axioms` must equal the trio.
2. Apply the R4 graph rows; re-run generate_graph/monitor consistency checks.
3. `rg`-gate: no sorry/axiom under FLT/ roots; `source-design.ndjson:` modularity-lifting row flips
   only per its own next_gate.
