# Tate uniformization source-design packet

## Scope and decision

This packet covers the uniformization and local-form portion of `FLT-TATE-UNRAMIFIED`:

- `WeierstrassCurve.tateCurveEquiv`;
- `WeierstrassCurve.exists_variableChange_tateCurve`;
- `WeierstrassCurve.tateEquiv`;
- the later base-change, Galois, and separable-closure compatibility declarations that consume
  those constructions.

It does not close `FLT-TATE-FLAT` or `FLT-TATE-WEIL`. Tate's paper supplies exact mathematical
sources for important parts of those clusters, but the pinned Lean library lacks the required
finite-flat group-scheme and source-faithful Weil-pairing objects.

Definition-of-ready decision: **PARTIAL**. The general-equivalence assembly and the local-form
consumer signatures elaborate and are kernel-clean. The explicit analytic point map has an exact
primary source, and its homomorphism/kernel/surjectivity boundary now has an exact Lean signature.
The repository already defines the formal `X/Y` series and proves their Weierstrass identity. A
second probe shows that concrete coordinates plus the addition law and surjectivity yield the exact
provider equivalence, with the kernel proof automatic. Concrete local-field evaluation of the
formal coordinates, the addition law, and surjectivity remain. Silverman V.5.3 has now been visually
checked with the official erratum: it supplies the local-form theorem for p-adic fields, including
residue characteristic 2. The repository signature remains broader than that source because
`IsNonarchimedeanLocalField` also admits a generic local-field formulation; a p-adic scope adapter or
a broader source is still required before authorizing the generic provider.

## Exact sources

### SRC-023: Tate's primary uniformization paper

John Tate, *A Review of Non-Archimedean Elliptic Functions*, in *Elliptic Curves, Modular Forms,
& Fermat's Last Theorem* (Hong Kong, 1993), International Press, 1995, pp. 162--184.

The author-hosted scan is:

`https://people.math.harvard.edu/~ctm/home/text/others/tate/tate-unif/tate-unif.pdf`

Load-bearing locators:

- Theorem 1, article p. 6 / book p. 167: the explicit map `phi : k^* -> E_t(k)` is a
  homomorphism onto the rational points with kernel `t^Z`.
- Lemmas 2 and 3 and the end of Theorem 1, article pp. 8--12 / book pp. 169--173: descent and
  surjectivity, including the exceptional characteristic-two case.
- the finite-algebra discussion, article p. 16 / book p. 177: the quotient isomorphism is
  functorial in finite-dimensional local `k`-algebras.
- “Points of finite order”, article pp. 18--19 / book pp. 179--180: the explicit finite-flat
  group scheme, its identification with `E_t[m]`, the canonical exact sequence
  `0 -> mu_m -> E_t[m] -> Z/mZ -> 0`, and the Weil-pairing formula up to sign convention.

Tate assumes a field complete for a nontrivial real-valued valuation and then treats the
nonarchimedean case. This is broader than the present provider's local-field restriction.

### SRC-024: Silverman's local-form theorem

Joseph H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer,
1994, Chapter V:

- Theorem V.3.1: explicit Tate-curve construction and uniformization;
- Lemma V.5.2 and Theorem V.5.3: the inverse `j` parameter and the equivalence between being the
  base-field Tate form and having split multiplicative reduction.

The book scan was visually checked at printed pp. 441--447, with Theorem V.5.3 and its proof on
printed pp. 442--444. Its SHA-256 is
`d06410160f5648135b060955e3a937c2f7de2361a02b0782e60ffec49fd49314`. The official errata p. 20
corrects part (a) to state first an algebraic-closure isomorphism while retaining that the unique
parameter lies in `K`; the errata SHA-256 is
`3d524535d7d5d50777b8a0fe66ef290d594effea46dc330b4df2486e8e017b8d`.

The local-form consequence required here is stronger and smaller than the two-proof decomposition
currently exposed in `TateLocalFormBoundary.lean`:

```text
same nonintegral j + split multiplicative reduction on both curves
  -> base-field variable change between the curves.
```

The exact theorem assumes a p-adic field. This covers finite extensions of `Q_p`, including `p = 2`,
but not arbitrary equal-characteristic complete nonarchimedean fields. It is source-ready for the
FLT characteristic-zero application after an exact p-adic Lean scope adapter is identified; it is
not source-ready for the current generic provider type without that restriction.

## Hypothesis translation

| Source hypothesis/data | Lean data | State |
|---|---|---|
| Tate: complete nonarchimedean field with nontrivial real-valued valuation; Silverman: p-adic field | `[ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]` | Tate's construction is broader; Silverman's local-form theorem requires a p-adic/characteristic-zero scope adapter |
| parameter `t != 0`, `0 < abs(t) < 1` | `(q : k^x)` and `valuation k (q : k) < 1` | exact provider arguments; nonzero comes from `q : k^x` |
| cyclic subgroup `t^Z` | `Subgroup.zpowers q` | exact library match |
| quotient group `k^*/t^Z` | `Additive (k^x / Subgroup.zpowers q)` | exact up to additive notation |
| rational points on the Tate curve | `((WeierstrassCurve.tateCurve (q : k))⁄k).Point` | exact target; `[DecidableEq k]` is an implementation requirement of the point group |
| formal `x(w), y(w)` series | `TateCurve.X`, `TateCurve.Y` | defined over `RatFunc ℚ`; formal Weierstrass equation kernel-clean |
| concrete local-field evaluation | `ExplicitTateCoordinateData` methodology contract | exact signature; provider absent |
| periodicity/addition under multiplication | `ExplicitTatePointLawData.map_add` | exact consumer signature; provider absent |
| homomorphism, exact kernel, surjectivity | `ExplicitTatePointMapData` | exact signature and quotient assembly kernel-clean; analytic provider absent |
| curve with nonintegral `j` | `1 < valuation k E.j` | kernel-clean as `WeierstrassCurve.one_lt_valuation_j` |
| Tate parameter inverse to `j(q)` | `E.q`, `tateParameter_tateCurve_j`, `tateCurve_tateParameter_j` | both concrete inverse laws are kernel-clean in methodology probes |
| split multiplicative reduction | `E.HasSplitMultiplicativeReduction 𝒪[k]` | exact repository predicate |
| base-field isomorphism of Weierstrass curves | `∃ C : VariableChange k, C • tateCurve E.q = E` | exact provider target |
| functoriality under field/base change | admitted `tateEquiv_baseChange` and `tateEquiv_galois` | source supports the explicit map; interaction with the chosen general-curve variable change remains a separate sign proof |

## Minimal mathematical and Lean graph

```text
formal X/Y series + Weierstrass identity [provider-proved]
  -> concrete local-field evaluation and equation
  -> piecewise point map (q^Z maps to infinity) [probe-proved]
  -> zero fibre = q^Z / exact kernel [probe-proved]
  -> addition theorem / homomorphism
  -> surjectivity (retain characteristic-two branch)
  -> tateCurveEquiv

formal-product identity + substitution evaluation [probe-proved]
  -> exact Tate parameter / j inverse laws [probe-proved]
  -> explicit tateCurve has split multiplicative reduction [probe-proved]
  -> Silverman V.5.3 local-form theorem
  -> exists_variableChange_tateCurve

tateCurveEquiv + exists_variableChange_tateCurve
  -> tateEquiv [assembly probe-proved]
  -> base-change and Galois sign compatibility
  -> tateEquivSepClosure
```

The alternative decomposition

```text
SameJQuadraticFormClassification
  + QuadraticTwistExcludesSecondSplit
  -> LocalSplitSameJClassification
```

also elaborates and is kernel-clean as an integration route. It should only be implemented if the
direct Silverman V.5.3 contract is harder to match to the pinned reduction API. It is not evidence
that two additional source theorems are intrinsically required.

## Existing library matches

- `Subgroup.zpowers` and the existing multiplicative quotient provide the source quotient.
- `TateCurve.X`, `TateCurve.Y`, and `TateCurve.weierstrass_equation` already provide the formal
  coordinate series and curve equation over `RatFunc ℚ`; the theorem has the standard axiom trio.
- `WeierstrassCurve.Affine.Point.equivVariableChange` and `equivOfEq` transport points to a
  variable-changed curve.
- `WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist` and
  `not_exists_smul_quadraticTwist_eq` support the alternative local-form route after the missing
  quadratic-extension and reduction statements are supplied.
- `TateReductionProbe.tateCurve_hasSplitMultiplicativeReduction` supplies the split-reduction
  premise for the explicit curve.
- `TateUniformizationAssemblyProbe.assembleTateEquiv` proves that no further mathematical theorem
  is hidden in the general `tateEquiv` construction.
- `TateCoordinatePointMapBoundaryProbe.tateCurveEquivOfCoordinates` proves that concrete
  coordinates, the addition law, and surjectivity are sufficient, and derives the exact kernel
  mechanically from the piecewise point-map definition.

No pinned declaration evaluates the formal `X/Y` coordinates in an arbitrary target local field,
proves the resulting point function respects multiplication, or proves its surjectivity. The
methodology probes show that the point construction, exact kernel, and quotient descent are then
mechanical. No pinned declaration is a source-faithful Weil pairing.

## Counterexample and statement review

1. A homomorphism from the quotient is insufficient: the proof needs both exact kernel and
   surjectivity to obtain an `AddEquiv`.
2. Equality of nonexceptional `j`-invariants alone gives only a form over the base field; split
   multiplicative reduction is the condition that selects the untwisted base-field form.
3. The separably closed same-`j` theorem cannot discharge the base-field variable change without a
   descent or twist argument.
4. The characteristic-two branch in Tate's surjectivity proof must not be silently replaced by an
   argument that divides by two.
   Silverman's p-adic theorem includes residue characteristic 2, but not equal characteristic 2.
5. The provider's `[DecidableEq k]` is a Lean implementation condition, not a mathematical source
   hypothesis.
6. Functoriality of the explicit Tate map is on the nose, while functoriality of a general curve's
   chosen variable change is only controlled up to sign. These must remain separate claims.
7. Tate's finite-flat torsion theorem does not by itself supply the repository's missing scheme
   definitions or a Lean Weil pairing; a citation cannot replace those objects.

## Lean signatures

`FLTMethodology/Probes/TateExplicitPointMapBoundary.lean` now exposes the explicit map rather than
assuming the final equivalence:

```lean
structure ExplicitTatePointMapData (q : kˣ)
    (_hq : valuation k (q : k) < 1) where
  phi : Additive kˣ →+ ((WeierstrassCurve.tateCurve (q : k))⁄k).Point
  surjective : Function.Surjective phi
  ker_eq : phi.ker = (Subgroup.zpowers q).toAddSubgroup
```

The probe proves that this data yields the existing `tateCurveEquiv` type via
`QuotientAddGroup.liftEquiv`. The quotient type and additive-subgroup conversion elaborate without
an extra transport theorem. Both the constructor and its proposition-valued `Nonempty` packaging
have only the standard axiom trio. No provider work is authorized by this packet.

`FLTMethodology/Probes/TateCoordinatePointMapBoundary.lean` further exposes:

```lean
structure ExplicitTateCoordinateData (q : kˣ) (hq : valuation k (q : k) < 1) where
  x y : kˣ → k
  equation : ∀ u, u ∉ Subgroup.zpowers q →
    (WeierstrassCurve.tateCurve (q : k)).toAffine.Equation (x u) (y u)

structure ExplicitTatePointLawData (q) (hq) (coordinates) where
  map_add : ∀ u v : Additive kˣ,
    explicitTatePointFun q hq coordinates (u + v) =
      explicitTatePointFun q hq coordinates u + explicitTatePointFun q hq coordinates v
  surjective : Function.Surjective (explicitTatePointFun q hq coordinates)
```

It proves that the zero fibre and exact kernel are automatically `q^ℤ`, then constructs
`tateCurveEquiv` from these fields. All exported probe declarations and the existing formal
`TateCurve.weierstrass_equation` have only the standard axiom trio.

For the local form, the already elaborating consumer contract is:

```lean
TateLocalFormBoundaryProbe.LocalSplitSameJClassification k
```

and the already elaborating assembly is:

```lean
TateUniformizationAssemblyProbe.assembleTateEquiv
```

## First likely residual Lean goals

1. evaluating the existing formal `X/Y` series in an arbitrary nonarchimedean local field and
   proving the concrete curve equation away from `q^ℤ`;
2. proving the resulting point function respects multiplication using the explicit addition law;
3. proving surjectivity without assuming algebraic closure and without losing characteristic two;
4. transporting Silverman V.5.3's curve isomorphism into the exact `VariableChange` action equality;
5. separating explicit-map naturality from the sign introduced by the chosen general-curve change.
