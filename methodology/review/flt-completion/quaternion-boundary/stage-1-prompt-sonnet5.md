INDEPENDENT STAGE-1 NAME-SOURCE DESIGN — FLT-HIST-QUATERNION

Repository root: /Volumes/second-store/devel/proof-forks/FLT
Frozen starting point: branch methodology/varro-proof-program-20260716 at
827eb969aff49fb5c5a1b17f807426d3be1b4056.
Pipeline: tri-design-axiomatise, Stage 1 only.
Component: quaternion-boundary.
Obligation: FLT-HIST-QUATERNION.
Target assurance stage: T2 named historical interface, not T3 proof discharge.

Act as an independent source-faithful mathematical and Lean interface designer. Work read-only in
the repository. Do not edit files, register an axiom, implement a proof, alter the control plane,
commit, or claim that a citation is a Lean proof. If you use a temporary Lean probe, put it outside
the repository and say exactly what it established.

Inspect at least:

- the FLT-HIST-QUATERNION row in methodology/control/proof-obligations.ndjson;
- methodology/source-design/quaternion-relative-index.md;
- methodology/SOURCE-REGISTER.md, especially SRC-001, SRC-017, and SRC-022;
- FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean, especially
  TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ,
  LevelStruct.Δ, and LevelStruct.range_units_le_range;
- FLT/Components/Contracts/QuaternionRelativeIndex.lean;
- every direct consumer of isFiniteRelIndex_Δ, including InnerProduct.lean and the concrete Hecke
  operator module; and
- any cited existing probe or audit needed to distinguish a signature-green scaffold from a proof.

Design the smallest exact named T2 theorem/interface that can replace this one generic
knownin1980s use without hiding unrelated obligations. Decide explicitly whether the named
historical boundary should be the exact adelic finite-relative-index result consumed by the
repository, a sourced compact-open-to-order/quotient theorem plus the already-proved finite
quotient adapter, or another strictly smaller source-faithful interface. Do not accept the current
docstring's direct injection into norm-one units without checking the reduced-norm square-class
problem. Do not infer finiteness from compactness alone; do not treat L.UA as compact; and do not
confuse Voight's order-unit finiteness theorem with the missing adelic-to-order bridge.

Return exactly these sections:

1. CURRENT CONSUMER BOUNDARY
   Give the exact declaration name and complete current Lean type, including universes, variables,
   typeclasses, notation expansions needed to understand Fscalar and Delta, and every direct
   consumer/top dependency path that would inherit the named axiom.

2. PRIMARY SOURCE LOCATOR
   Name the exact historical theorem(s), author, title, year, theorem/lemma/page locator, and exact
   mathematical hypotheses and conclusion. Distinguish a primary historical source from Voight
   2021 as a modern secondary source. If the repository evidence does not identify an exact
   primary source for the adelic bridge, say SOURCE GAP rather than inventing one.

3. MINIMAL NAMED T2 INTERFACE
   Propose one canonical namespace-qualified axiom name and one exact Lean signature intended to
   elaborate in this repository. List separately every definition or kernel-clean adapter it
   consumes. The proposed axiom must not contain a generic Prop parameter, must not imply unrelated
   claims, and must not simply reintroduce knownin1980s under an opaque generic name.

4. MINIMALITY AND SOURCE FAITHFULNESS
   Explain why the interface is genuinely historical/pre-1990, why each hypothesis is necessary,
   and why the conclusion is no stronger than the source. If an exact pre-1990 source is missing,
   state what narrower theorem can honestly be named now and what remains unnameable.

5. DEPENDENCY AND AXIOM-SURFACE PATH
   Show the path from the proposed axiom through the existing adapter/instance and all consumers to
   the relevant exported/top declarations. State which declarations should name the axiom in a
   #print axioms audit and which should remain unaffected.

6. COUNTEREXAMPLES AND OVERSTATEMENT RISKS
   Test at least: the norm-square-class obstruction, compact versus finite, central noncompactness
   of L.UA, conjugated-order dependence on g, and the difference between finite double-coset type
   and finite stabilizer quotient. Give a concrete failure mode for every rejected stronger claim.

7. SIGNATURE PROBE PLAN
   Provide an import-minimal temporary Lean file outline with #check and #print axioms commands that
   would test the signature and its intended consumer replacement. Clearly label whether you
   actually ran the probe.

8. VERDICT
   Return exactly one of NAMEABLE, REVISE, or OBSTRUCTION, followed by at most five sentences. A
   NAMEABLE verdict requires an exact primary-source locator and a plausible elaborating signature.

No proof claim. No T3 claim. No repository edits.
