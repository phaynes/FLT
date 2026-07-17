# Stage 4 prompt — Opus 4.8 bounded Fontaine--Odlyzko characteristic-three build

Difficulty 10 component, but a deliberately bounded first Lean unit. You may edit only:

- a new `FLTMethodology/Probes/FontaineOdlyzkoCharP.lean`;
- the single matching import in `FLTMethodology.lean`.

Do not edit FLT source modules, theorem statements, control/graph/task files, review artifacts,
historical assumptions, or any other file. Do not commit or push.

Implement exactly the independently reviewed theorem:

```lean
theorem charP_three_of_zp3_algebra
    (k : Type u) [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3
```

Use a methodology namespace that cannot collide with future production declarations. Add a concise
docstring explaining that this is only the coefficient-characteristic leaf for the proposed
Fontaine--Odlyzko route; it does not prove reducibility, the cut-out-field argument, any discriminant
bound, or `mod_three`.

Hard requirements:

1. no `sorry`, `axiom`, `admit`, `native_decide`, or unsafe declaration;
2. do not import or consume `Odlyzko_statement`, `knownin1980s`, or any proposed N1/N2 assumption;
3. run the targeted file build and `lake build FLTMethodology`;
4. include `#check` and `#print axioms` in the probe;
5. PASS only if the theorem audits exactly to `[propext, Classical.choice, Quot.sound]`;
6. stop and report an obstruction rather than weakening the type or adding a premise.

Return `BUILT`, `OBSTRUCTION`, or `NO-RESULT`, with the exact changed files, build outputs, theorem
type, axiom audit, elapsed time if available, and the next still-open mathematical node. This build
cannot promote `FLT-FONTAINE-ODLYZKO`, which remains `absent` with N1, N2, D, E, F, and S11 open.
