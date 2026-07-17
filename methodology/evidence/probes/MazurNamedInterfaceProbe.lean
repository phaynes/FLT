import FLT.FreyCurve.Mazur

/--
Signature-only probe for the proposed Serre 1987 named T2 boundary. The historical statement is a
local hypothesis, not a repository axiom. This checks that its type is exactly the existing
`FreyPackage.mazur` consumer type.
-/
theorem serre1987_freyCurve_galoisRep_signature_applies (P : FreyPackage)
    (historicalFreyIrreducibility :
      let E := P.freyCurve
      let p := P.p
      have : Fact p.Prime := ⟨P.pp⟩
      GaloisRep.IsIrreducible (E.galoisRep p P.hppos)) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  exact historicalFreyIrreducibility

#print axioms serre1987_freyCurve_galoisRep_signature_applies
