# FLT-TATE-WEIL consumer-slice result

Checkpoint: `61ca825`.

Verdict: **STATEMENT/API CONSTRUCTION GAP**.

The exported type of `WeierstrassCurve.weilPairing` specifies only a biadditive map

```lean
AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
  AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
    Additive (rootsOfUnity n k)
```

and is therefore inhabited by the zero pairing. The permanent
`FLTMethodology.Probes.WeilPairingBoundary` kernel regression shows that this inhabitant
cannot satisfy the frozen downstream `weilPairing_tatePoint` equation whenever the selected root of
unity is nontrivial. Replacing the admission by zero would typecheck but would be mathematically
false at its consumer.

Pinned Mathlib has roots-of-unity and elliptic-point infrastructure but no Weil-pairing, Miller-
function, elliptic-divisor, Picard, or Cartier-duality implementation from which to construct the
required object. A sound closure needs a source-faithful Weil pairing with enough alternating,
perfectness, base-change, or Galois-equivariance laws to exclude the zero inhabitant, followed by
the Tate normalization theorem consumed downstream.

`WeierstrassCurve.tateEquivSepClosure` is additionally owned by the Tate-uniformization subcluster,
so `weilPairing_tatePoint` cannot be audited independently of `FLT-TATE-UNRAMIFIED`.

No admission was removed.
