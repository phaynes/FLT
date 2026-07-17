## Controller kernel probe — class-field tame-residue U1/U2

Date: 2026-07-18 (Australia/Sydney)

Scope: independently test only the synthesis's presently buildable U1/U2 prefix. This is not a
proof of the tame residue character or its kernel theorem, and it does not discharge
`FLT-CLASS-FIELD` or the proposed `FLT-TAME-RESIDUE` obligation.

Temporary file outside the repository:

- `/private/tmp/FLTClassFieldTameClosednessProbe.lean`

Command:

```text
lake env lean /private/tmp/FLTClassFieldTameClosednessProbe.lean
```

Result: exit 0.

```text
'AddSubgroup.isClosed_inertia_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'isClosed_localInertiaGroup_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'localTameAbelianInertiaGroup_le_localInertiaGroup_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Controller verdict: `U1-U2-KERNEL-GREEN-BOUNDED`. The first arithmetic residual remains U3,
roots-of-unity reduction injectivity. No proof-graph mutation or historical assumption is authorized
by this probe.
