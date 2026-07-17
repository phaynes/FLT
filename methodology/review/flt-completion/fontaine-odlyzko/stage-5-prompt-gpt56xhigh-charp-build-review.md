# Stage 5 prompt — GPT-5.6 xhigh independent review of Fontaine charP leaf

Difficulty 10 component; bounded build review. Work read-only. Do not edit repository files, task
state, graph rows, source registers, review artifacts, or Lean source. Review only:

- `FLTMethodology/Probes/FontaineOdlyzkoCharP.lean`;
- its single import in `FLTMethodology.lean`;
- the Stage-3 GPT review and Stage-4 bounded-build report.

Independently verify:

1. the theorem type is exactly
   `(k : Type u) [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3`;
2. the proof is mathematically valid for every finite field and uses the 3-adic unit argument in the
   correct direction;
3. targeted, direct-Lean, and umbrella builds pass;
4. `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`;
5. no `sorry`, `axiom`, `admit`, `native_decide`, unsafe declaration, hidden historical input, or
   dependency on `Odlyzko_statement`, `knownin1980s`, N1, or N2 occurs;
6. the namespace/import placement is non-colliding and the docstring honestly limits the scope;
7. the control plane still leaves `FLT-FONTAINE-ODLYZKO` absent with N1, N2, D, E, F, and S11 open.

Return exactly `PASS`, `REVISE`, `REFUTED`, or `NO-RESULT`, with exact build output, theorem type,
axiom audit, findings, and the first remaining mathematical node. A PASS accepts only this bounded
leaf and cannot promote the component or authorize an historical axiom.
