# Mazur T2 operator authorization and kernel gate

Status: **AUTHORIZED T2; KERNEL GATE PASS**.

Operator: philip.haynes
Authorization date: 2026-07-18
Governed task: task:fg-flt-ra-math-source-design-20260716

## Authorized boundary

The operator authorized exactly one named T2 interface in FLT/FreyCurve/Mazur.lean:

    Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
      let E := P.freyCurve
      let p := P.p
      have : Fact p.Prime := ⟨P.pp⟩
      GaloisRep.IsIrreducible (E.galoisRep p P.hppos)

It is declared with the unqualified name freyCurve_galoisRep_isIrreducible inside
namespace Serre1987, immediately before FreyPackage.mazur. The consumer is discharged directly
by the named interface. The former generic knownin1980s import and invocation are absent from this
path.

## Source and corrected justification

Source locator: J.-P. Serre (1987), §4.1, Proposition 6, printed p. 201, resting on Mazur's
theorem cited there (SRC-006, SRC-020, SRC-021).

For a semistable Frey curve with full rational two-torsion and prime p >= 5, Serre's two character
cases together with the odd-degree quotient isogeny retain the full two-torsion needed for the Mazur
torsion contradiction. The Opus counterexample rationale is withdrawn under the authoritative
stage-2a-review-disposition.md overlay and is not used in the registered justification.

## Placement and parity probes

lake env lean /private/tmp/MazurNamedPlacementProbe.lean passed. Its consumer probe depends on:

    [propext,
     Classical.choice,
     Quot.sound,
     Serre1987.freyCurve_galoisRep_isIrreducible_PLACEMENT_PROBE]

lake build FLT.FreyCurve.Mazur FLTMethodology.Probes.MazurParityBoundary passed. The two parity
translation declarations in FLTMethodology/Probes/MazurParityBoundary.lean each audit to:

    [propext, Classical.choice, Quot.sound]

## Consumer axiom audit

lake env lean /private/tmp/MazurT2ConsumerAudit.lean passed and reported:

    'FreyPackage.mazur' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     Serre1987.freyCurve_galoisRep_isIrreducible]

The authorized set is therefore exact. Focused scans found no knownin1980s, sorry, admit,
native_decide, or unsafe token in FLT/FreyCurve/Mazur.lean, and no withdrawn source rationale
was registered.

The first full terminal build exposed a stale exact-message guard in FermatsLastTheorem.lean: it
still expected the former generic axiom name. Under the bounded mechanical-repair rule, only that
expected audit message was changed to the new kernel-reported list. No theorem, source, scope, or
assurance rule changed. lake build FermatsLastTheorem then passed.

## Assurance boundary

This is a named historical T2 boundary. It is forbidden at T3. No unconditional proof discharge or
T3 completion is claimed.
