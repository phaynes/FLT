INDEPENDENT STAGE-1 NAME-SOURCE DESIGN — FLT-HIST-MAZUR

Repository root: /Volumes/second-store/devel/proof-forks/FLT
Frozen starting point: branch methodology/varro-proof-program-20260716 at
827eb969aff49fb5c5a1b17f807426d3be1b4056.
Pipeline: tri-design-axiomatise, Stage 1 only.
Component: mazur.
Obligation: FLT-HIST-MAZUR.
Target assurance stage: T2 named historical interface, not T3 proof discharge.

Act as an independent source-faithful mathematical and Lean interface designer. Work read-only in
the repository. Do not edit files, register an axiom, implement a proof, alter the control plane,
commit, or claim that a citation is a Lean proof. If you use a temporary Lean probe, put it outside
the repository and say exactly what it established.

Inspect at least:

- the FLT-HIST-MAZUR row in methodology/control/proof-obligations.ndjson;
- methodology/source-design/mazur-frey.md;
- methodology/SOURCE-REGISTER.md, especially SRC-006, SRC-020, and SRC-021;
- FLT/FreyCurve/Mazur.lean and the complete type of FreyPackage.mazur;
- FLT/Assumptions/Mazur.lean and the exact weakness of Mazur_statement caused by Set.ncard on an
  infinite set;
- the kernel-clean torsion, semistability, two-torsion, and post-geometry assembly declarations
  cited by the source-design packet;
- FLT/Proof.lean, especially B4_implies_B3 and the path to flt; and
- axiom audits needed to distinguish the now-clean concrete galoisRep path from the still-historical
  irreducibility input.

Design the smallest exact named T2 theorem/interface that replaces the generic knownin1980s use in
FreyPackage.mazur. Decide explicitly whether the faithful historical boundary is Serre 1987 §4.1
Proposition 6 specialized to the repository's FreyPackage, a more general semistable-character or
quotient-isogeny theorem combined with already-proved adapters, Mazur 1977 Theorem 8 plus additional
named historical interfaces, or another strictly smaller sourced theorem. Do not substitute the
torsion classification alone for the actual irreducibility theorem. Do not identify a Galois-stable
line with a rational point, omit the cyclotomic-line/quotient-curve case, assume semistability from a
nonzero discriminant, or use Set.ncard without finiteness.

Return exactly these sections:

1. CURRENT CONSUMER BOUNDARY
   Give the exact declaration name and complete current Lean type, including lets, local Fact
   instance, parameter hypotheses, and the concrete galoisRep expression. List every direct
   consumer and the dependency path through the boss chain to flt.

2. PRIMARY SOURCE LOCATOR
   Name the exact historical theorem(s), author, title, year, theorem/lemma/page locator, and exact
   hypotheses/conclusion. State whether Serre 1987 Proposition 6 directly matches the Frey-shaped
   curve used here and exactly what repository adapter is still needed. Distinguish Mazur's torsion
   classification from Serre's irreducibility conclusion.

3. MINIMAL NAMED T2 INTERFACE
   Propose one canonical namespace-qualified axiom name and one exact Lean signature intended to
   elaborate in this repository. List separately every existing kernel-clean definition, provider,
   or adapter it consumes. The axiom must not have a generic Prop parameter, imply unrelated
   claims, or merely rename knownin1980s opaquely.

4. HYPOTHESIS TRANSLATION AND MINIMALITY
   Translate the source's A+B+C=0, pairwise-coprime/nonzero, parity normalization, semistability,
   full rational 2-torsion, prime p >= 5, and exact curve model into FreyPackage fields or existing
   proved adapters. Explain why each retained hypothesis is needed and why the conclusion is no
   stronger than the cited source.

5. DEPENDENCY AND AXIOM-SURFACE PATH
   Show the path from the proposed named axiom through FreyPackage.mazur, B4_implies_B3, B3_proof,
   B2_proof, B1_proof, and flt. State which declarations should name the exact axiom in #print
   axioms and which concrete galoisRep/torsion declarations should remain standard-axiom only.

6. COUNTEREXAMPLES AND OVERSTATEMENT RISKS
   Test at least: stable subgroup versus rational point, the missing cyclotomic-line case, odd-degree
   quotient preservation of full 2-torsion, semistability, p=5, sign/parity/model normalization, and
   Set.ncard's infinite-set behavior. Give a concrete failure mode for every rejected weakening.

7. SIGNATURE PROBE PLAN
   Provide an import-minimal temporary Lean file outline with #check and #print axioms commands that
   would test the signature and replacement path. Clearly label whether you actually ran the probe.

8. VERDICT
   Return exactly one of NAMEABLE, REVISE, or OBSTRUCTION, followed by at most five sentences. A
   NAMEABLE verdict requires an exact primary-source locator and a plausible elaborating signature.

No proof claim. No T3 claim. No repository edits.
