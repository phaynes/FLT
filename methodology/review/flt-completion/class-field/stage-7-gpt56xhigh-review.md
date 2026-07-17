# Stage 7 GPT-5.6 xhigh independent review — class field

## Verdict: REVISE

This is a mechanical interface-and-scope repair, not a substantive rejection of the mathematical
decomposition.

- `FLTMethodology.Probes.ClassFieldCharacterBoundary` elaborates. All four declarations have exactly
  `[propext, Classical.choice, Quot.sound]`; none asserts reciprocity, existence, discreteness, or
  profiniteness.
- The opaque `def IdeleClassGroup` does not expose synthesized `CommGroup`, `TopologicalSpace`, or
  `IsTopologicalGroup` instances. Those synthesize for the unfolded quotient. It is currently only a
  clean quotient-type definition, so Stage 6 over-described Bank 4 as a named topological
  commutative group and placed too much under the later P3 plumbing node.
- `localUniformiserUnit` is a unit of `FiniteAdeleRing`, not the full `AdeleRing` used by
  `IdeleClassGroup`. A finite-idele-to-full-idele embedding is required before the proposed global
  coset clause has exact vocabulary.
- There are three actual uses of `localTameAbelianInertiaGroup`: `BlueprintSGood.traceOnJ`,
  `traceConditionFunctor`, and `cyclic_base_change.hρtame`. `narrowTraceConditionFunctor` uses full
  inertia and is not a tame-kernel consumer. The first two are standard-trio clean;
  `cyclic_base_change` still contains `sorryAx`.
- The graph repair must name the exact tame-kernel edge to `FLT-SGOOD-DEF` and reconcile the routed
  `FLT-AUX-LOCAL-FIELD`/Skinner–Wiles ownership. A generic “class-field to MLT” edge is insufficient.
- Elementary tame-residue theory remains correctly separated from local/global reciprocity. Idele
  objects, closedness/discreteness, quotient-component plumbing, profiniteness, reciprocity, and
  globalization remain distinct.
- Arithmetic Frobenius is a source-compatible repository convention and the coset form is correct.
  Geometric normalization is an inverse convention, not itself a contradiction; mixing the two
  conventions creates the sign error.
- Source gating is honest. `SRC-004` remains incomplete, no primary CFT source is registered, and
  `HIST-UNRESOLVED` blocks every CFT T2 assumption. No T2 boundary is authorized.

## Typed Fable decision

`SKIP-FURTHER`: the component already received the retained Fable pass. The remaining failures are
deterministic Lean plumbing, exact-type vocabulary, graph scope, and normalization wording—not a new
substantive mathematical divergence.

## Next exact no-axiom unit

Create `FLTMethodology.Probes.ClassFieldIdeleTopologyBoundary`:

1. Make the quotient alias transparent, or provide coherent explicit instances, so the exact
   `IdeleClassGroup K` name synthesizes `CommGroup`, `TopologicalSpace`, and
   `IsTopologicalGroup`.
2. Define standard-trio-clean `finiteAdeleToAdele`, `finiteIdeleEmbedding`, and
   `localUniformiserIdele` maps.
3. Add `#synth` checks for the three structures and `#print axioms` for every declaration.
4. Exclude connected components, discreteness, profiniteness, reciprocity, and every generic package
   theorem.

The reviewer verified a transparent quotient and the three full-idele definitions in a temporary
probe with exactly the standard axiom trio. This review was read-only.
