# FLT-TORSION-001 Galois-representation closure audit

Date: 2026-07-17  
Task: `fg-flt-elliptic-torsion-card-provider-20260717`  
Obligation: `FLT-TORSION-001`

## Verdict

`WeierstrassCurve.galoisRep` and every load-bearing declaration in its concrete construction audit
to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The audited chain is:

- `WeierstrassCurve.n_torsion_finite`
- `WeierstrassCurve.n_torsion_card`
- `WeierstrassCurve.n_torsion_dimension`
- `WeierstrassCurve.Points.map`
- `WeierstrassCurve.Points.map_id`
- `WeierstrassCurve.Points.map_comp`
- `WeierstrassCurve.galoisRepresentationSmul`
- `WeierstrassCurve.galoisRepresentation`
- `WeierstrassCurve.torsionGaloisMap`
- `WeierstrassCurve.torsionGaloisLinearMap`
- `WeierstrassCurve.torsionGaloisActionHom`
- `WeierstrassCurve.torsionGaloisPointStabilizer_isOpen`
- `WeierstrassCurve.torsionGaloisActionHom_ker_isOpen`
- `WeierstrassCurve.galoisRep`

The audit was compiled through `lake env lean /dev/stdin` after importing
`FLT.EllipticCurve.Torsion`. Full `lake build FLT` and `lake build FLTMethodology` also pass at the
component checkpoint. No custom axiom or historical assumption is added.

## Consequence

The provider closure for `FLT-TATE-TORSION` removes the last transitive admission from the concrete
Galois-representation construction. `FLT-TORSION-001` is therefore proved and integrated. This does
not close the independent finite-flat, Tate/unramified, Weil-pairing, or `FLT-FREY-HR` obligations.
