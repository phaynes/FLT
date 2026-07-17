I’m treating this as a read-only adjudication, not an implementation pass. I’ll first reopen the exact review chain, probes, consumer graph, and axiom ledger; then I’ll replay each load-bearing declaration in an ephemeral Lean input and separate interface compilability from provider discharge.
The review chain is internally consistent about the intended boundary, but the final synthesis leaves one key consumer identification explicitly unproved. I’m now checking whether that is genuinely routine Lean transport or whether it changes the statement, while also rebuilding the live dependency and axiom ledger from source rather than inheriting either prior table.
The original Stage-6 temporary probes are still present outside the repository, so I can replay the exact proof bodies rather than reconstructing them from prose. I’ll use those unchanged files, then run a separate ephemeral check for the closure-to-consumer collapse that Stage 6 did not include.
Fresh replay confirms the Stage-6 bodies themselves elaborate and audit cleanly, and the residue `IsLocalHom` still fails instance synthesis exactly as reported. The emerging defect is narrower but substantive: the proved tower lemma reaches `rho.baseChange C`; it does not identify an arbitrary closure-valued consumer representation with that base change. I’m testing that distinction directly now.
The branch advanced during the review, but only the generated obligation/graph ledgers changed among the reviewed surfaces. I’m refreshing those two records now so the verdict uses the current dependency state; the Lean files, review artifacts, consumers, and APIs remained unchanged.
REVISE-SUBSTANTIVE

The internal Lean tranche is mostly sound, but the closure-valued consumer boundary remains an omitted provider. Stage 7 incorrectly classifies it as discharged.

### Six-defect adjudication

| Stage-5 defect | Result |
|---|---|
| Generic-closure tower and consumer descent | **Not fully repaired.** The tower elaborates, but descent reaches only `rho.baseChange C`, not the named consumer representation. |
| Generalized universes | Repaired. `V0`, both residual modules, and the conjugation module elaborate at independent universes. |
| `CoefficientData extends StableLatticeData` | Repaired; `toStableLatticeData` is generated and trio-clean. |
| Residue `IsLocalHom` boundary | Repaired as an explicit open boundary. Fresh synthesis still fails exactly for `IsLocalHom (algebraMap ℤ_[p] (ResidueField O))`; the algebra and scalar-tower instances succeed. |
| Same-`O` two-lattice comparison | Repaired. Both charpoly lemmas elaborate at generalized module universes. They prove nothing cross-`O`. |
| Consumer ledger | Axiom statuses are correct, but the claimed closure relationship is overstated by the unresolved descent defect. |

### Exact substantive defect

The replayed theorem [exists_closure_descent](/tmp/flt-stage6/probe4.lean:61) proves only

```lean
∃ rc : C ⊗[O] V0 ≃ₗ[C] C ⊗[E] V,
  (rho0.baseChange C).conj rc = rho.baseChange C
```

The live consumers instead require equality with a named representation already over the closure:

- `cyclic_base_change`: `(ρ₀.baseChange ℚ̄_p).conj r₀ = ρ` in [Automorphic.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:160).
- `mem_isCompatible`: equality with `σ hℓ φ` in [Family.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Family.lean:45).

I proved ephemerally, with exactly the standard trio, that self-base-change collapses:

```lean
(rho.baseChange C).conj (TensorProduct.lid C V) = rho
```

But this helps only after taking `E := C`. That specialization is unavailable in the proposed data: `StableLatticeData` requires `[IsFractionRing O E]`, while `GenericClosureTower` does not provide—and fresh inference fails for—

```lean
IsFractionRing O (AlgebraicClosure ℚ_[p])
```

For the intended module-finite DVR `O`, its fraction field is a finite extension of `ℚ_[p]`, not the full algebraic closure. Taylor’s source likewise starts with a closure-valued representation and defines reduction through integral conjugation and semisimplification; later it works over `O_L` for a finite extension `L/ℚ_ℓ`. [Taylor 2018 notes](https://math.berkeley.edu/~fengt/249A_2018.pdf)

The exact missing datum is:

```lean
(ec : C ⊗[E] V ≃ₗ[C] Vc)
(hconsumer : (rho.baseChange C).conj ec = rhoc)
```

Given these, I replayed a trio-clean `exists_descent_to_named_consumer` by composing `exists_closure_descent` with `ec`. Thus:

- self-base-change collapse: bankable wiring;
- identification with the actual consumer: open field-of-definition/closure-descent provider;
- Stage 7’s “closure boundary PROVED” and six-provider ledger: statement-level defects.

`DescendsToClosure` may remain a clean predicate, but it must be required as data or listed as a seventh open provider. It is not produced from `StableLatticeData` and `GenericClosureTower` alone.

### Replay and axiom ledger

Fresh results at `2ffbcf0491c78ff3e8e75318e75569b9cedc18cf`:

- Stage-6 main probe: 18/18 declarations elaborate with only `propext`, `Classical.choice`, `Quot.sound`.
- Tower probe: both base-change/conjugation lemmas and `exists_closure_descent` have exactly that trio.
- Both live boundary probes compile; the one-sided-trace counterexample remains trio-clean.
- No `sorryAx`, custom axiom, `knownin1980s`, `admit`, `unsafe`, or `native_decide` occurs in the proposed bankable declarations.

| Live declaration | Current closure |
|---|---|
| `GaloisRep.baseChange`, `conj`; cited Mathlib tensor/charpoly APIs | standard trio |
| `GaloisRep.IsAutomorphicOfLevel` | standard trio |
| `GaloisRepFamily.isCompatible` | standard trio |
| `cyclic_base_change` | standard trio + `sorryAx` |
| `IsHardlyRamified.mem_isCompatible` | standard trio + `sorryAx` |
| `IsHardlyRamified.lifts` | standard trio + `sorryAx` |
| `Deformation.ProartinianCat.self` | standard trio |
| `isCorepresentable_narrowSLiftFunctor` | standard trio + `sorryAx` |

T-A1, T-A2, T-A3, M4, BN, and T-IND-CLOSURE remain open exactly as claimed; conditional contract wiring does not discharge them. The additional closure-realization provider is also open. Consequently the T1 obligation remains a definition gap and cannot be promoted.

The bounded two-iteration agreement gate is exhausted. This substantive disagreement now requires human adjudication before another repair, persistence, registration, or promotion.
