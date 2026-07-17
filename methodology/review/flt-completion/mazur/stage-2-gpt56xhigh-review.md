# GPT-5.6 xhigh independent review — Mazur

- Component: `mazur`
- Obligation: `FLT-HIST-MAZUR`
- Reviewed artifact: `stage-1-opus48-primary.md`
- Agent: `gpt56xhigh-independent-reviewer-d10`
- Backend/model: `codex` / `gpt-5.6-sol`
- Reasoning/transport/sandbox: `xhigh` / `exec` / `read-only`
- Scheduled budget: `2100s`
- Transport result: `SUCCESS`
- Actual elapsed: `356339ms` (`real 356.34s` from `/usr/bin/time`)
- Codex rollout/request correlation: `019f6f11-8b92-7ea0-a151-dbaad25efb9f`
- Codex turn/request correlation: `019f6f11-8eb1-79f3-8092-c811d8246278`
- Provider-level request IDs: not exposed by the Codex `exec` transport
- Final token count: `3945238` input (`3742208` cached input), `14938` output
  (`8891` reasoning output), `3960176` total
- Verdict: **REVISE**
- Promotion: none; design correction and the mandatory human gate remain open

## Verdict

**REVISE**

## Blocking findings

- The claimed counterexample in the Opus design is wrong. Serre's proof shows that semistability
  plus full rational 2-torsion already forces irreducibility for prime `p >= 5`: in either character
  case, `E` or `E/X` has rational `p`-torsion, while the odd-degree isogeny preserves full rational
  2-torsion, contradicting Mazur's bound. Semistable curves with rational `p`-isogenies but without
  full rational 2-torsion are not counterexamples.
- This invalidates the design artifact's counterexample/minimality rationale, though not its
  specialized conclusion.

## Nonblocking findings

- The locator is exact: Serre 1987 §4.1, Proposition 6, printed p. 201 proves irreducibility for the
  specified Frey-shaped curve; its proof cites Serre 1972 p. 307 and Mazur Theorem 8.
- The parity translation is valid but must include exponentiation rather than merely citing `ha4`
  and `hb2`:

  - `A = a^p ≡ -1 mod 4` follows from `ha4` and odd `p`.
  - `B = b^p ≡ 0 mod 32` follows from `hb2` and `p >= 5`.

- The transformed repository model is exactly Serre's change of variables, and the remaining
  nonzero, coprimality, equation, and prime hypotheses follow from `FreyPackage`.
- `MazurNamedInterfaceProbe.lean` compiles with exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- The proposed specialized axiom is appropriately narrow for the unchanged consumer, even though a
  more general mathematical theorem is true.
- Current closure is correctly separated: `galoisRep` is standard-trio clean;
  `FreyPackage.mazur -> B4_implies_B3` currently adds only `knownin1980s`; the independent
  `sorryAx` enters through `B4_proof` above that join.

## Mandatory human-gate decision

Do not authorize registration yet. After correcting the false counterexample claim, the human must
explicitly approve or reject registering exactly one T2-only historical assumption:

```lean
Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

Approval must also fix its module placement, attest to the `A mod 4` and `B mod 32` derivations,
and require post-registration audits showing the exact Serre axiom replaces `knownin1980s` with no
new `sorryAx`. It must not be permitted at T3.
