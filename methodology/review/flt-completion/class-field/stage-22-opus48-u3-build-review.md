# Opus 4.8 review — tame-residue U3 bounded build

Date: 2026-07-18 (Australia/Sydney)

Verdict: `NO-RESULT — PLAN-ONLY REVIEW`.

This is neither a mathematical rejection nor a build-review PASS. The reviewer completed the
read-only portion, but its `suggest`/plan-mode execution profile refused to run the required Lean
build and axiom commands because they can update build artifacts. The U3 review gate therefore
remains open.

## Read-only findings

Opus reported all available read-only checks clean:

- the three reviewed source/probe paths at live HEAD were byte-identical to source commit
  `3cd3560`;
- the geometric-sum cancellation argument is valid for local rings with zero divisors;
- the finite-cardinality bijection, `q - 1` unit proof, residue-field embedding, equivalence
  orientation, and injectivity composition are coherent;
- the reusable module has no FLT-specific dependency and the place-specific declarations are in a
  valid declaration order;
- `localTameAbelianInertiaGroup`, graph edges, historical assumptions, and T2 boundaries are
  unchanged;
- U4, U5, and U6 remain absent/open and `FLT-TAME-RESIDUE` remains a `definition-gap`.

## Missing independent checks

The reviewer did not independently execute:

```text
lake build FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField \
  FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
  FLTMethodology.Probes.TameResidueBoundary
lake build FLT FLTMethodology
```

It also did not independently reproduce the ten `#print axioms` results. Controller evidence for
both builds and the exact standard trio already exists, but `VERIFY != PRODUCE` requires the
independent reviewer to reproduce it before U3 can be sealed.

## Resume point

Resume with an executable read-only reviewer profile that is permitted to update `.lake` build
artifacts, or explicitly continue the same Opus session with permission to run only the listed build
and axiom-audit commands. No mathematical redesign is indicated by this attempt.

The first exact U4 residual identified by Opus is to prove that the inertia ratio associated with a
uniformizer is a `(q - 1)`-st root of unity in the integral closure, so that the U3 reduction map can
be applied. This is a design hint only; U4 remains unauthorized until the governed review resumes.
