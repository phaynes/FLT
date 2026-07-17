# Human agreement gate — coefficient closure consumer

## Status

`OPERATOR-ADJUDICATION-REQUIRED`

The second and final automatic agreement iteration ended in a substantive disagreement. The proposed
coefficient tower proves descent only to `rho.baseChange C`; live consumers name a representation
`rhoc` already over `C`. Connecting them requires explicit data of the form:

```lean
(ec : C ⊗[E] V ≃ₗ[C] Vc)
(hconsumer : (rho.baseChange C).conj ec = rhoc)
```

Given this data, the reviewer built a trio-clean conditional composition with
`exists_closure_descent`. The data itself does not follow from `StableLatticeData` and
`GenericClosureTower`.

## Exact operator choices

1. **Accept an explicit seventh provider (recommended).** Treat the field-of-definition / named
   closure-realization datum above as an open T1 provider. Permit later persistence only of the
   trio-clean definitions and conditional wiring, with the coefficient obligation remaining a
   definition gap until all seven providers are proved.
2. **Require the seventh provider before any persistence.** Keep even the bounded coefficient slice
   unpersisted until a concrete source-backed theorem constructs `ec` and `hconsumer` for each live
   consumer.
3. **Reject this coefficient architecture.** Reopen the field-of-definition model and redesign the
   coefficient boundary before further work.

No option promotes `FLT-MLT-COEFFICIENTS`; T-A1, T-A2, T-A3, M4, BN, T-IND-CLOSURE, and the named
consumer realization all remain open. Until the operator chooses, no repair, persistence,
registration, or promotion is authorized on this component.
