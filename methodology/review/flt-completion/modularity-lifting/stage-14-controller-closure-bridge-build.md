# Controller build — residual-closure to class absolute irreducibility

Verdict: **KERNEL-GREEN — INDEPENDENT REVIEW REQUIRED**.

The root critical-path obligation `FLT-ABSIRRED-VOCAB` now has a production proof of its open
provider contract. No Taylor source theorem, residual-image application, or downstream component is
promoted by this build.

## Construction

`FLTMethodology.Probes.ResidualAbsoluteVocabulary` adds:

1. `adjoinRange_eq_top_of_isAlgClosed_irreducible`: Burnside/Schur density over an algebraically
   closed coefficient field;
2. `adjoinRange_eq_top_of_baseChange_eq_top`: faithful descent of full image-algebra density by a
   tensor-product surjection and finite-dimensional comparison;
3. `closureImpliesClassAbsIrred`: the chosen residual-closure irreducibility gives base-field density,
   which extends to every coefficient field and yields the repository
   `Representation.IsAbsolutelyIrreducible` class.

The proof does not assume algebraic-closure uniqueness or an embedding between arbitrary closures.
It descends the full matrix algebra once and then extends it forward to each requested field.

## Kernel gate

```text
lake build FLTMethodology.Probes.ResidualAbsoluteVocabulary
  -> Build completed successfully (3479 jobs)

'...adjoinRange_eq_top_of_isAlgClosed_irreducible' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'...adjoinRange_eq_top_of_baseChange_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'...closureImpliesClassAbsIrred' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The obligation remains `definition-gap` until an independent mathematical and build review checks
the new proof. Its two consumers remain open independently.
