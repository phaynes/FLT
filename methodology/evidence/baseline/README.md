# Baseline evidence

`BaselineAudit.lean` is the executable audit for the frozen public baseline. It checks the exact
terminal and boss declarations and asks Lean to print both their axiom closures and transitive
admission dependencies.

The audit deliberately imports the real `FermatsLastTheorem` root. A successful elaboration is not
a green proof result: the printed axiom closure is the result being measured.

The frozen source census is 59 executable-looking admissions and two direct uses of the
`knownin1980s` tactic. These counts are not completion percentages and do not account for absent
mathematical programmes.
