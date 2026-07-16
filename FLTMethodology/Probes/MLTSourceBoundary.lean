import FLT.GaloisRepresentation.Automorphic
import FLT.Deformations.Representable
import FLT.Patching.REqualsT
import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
Kernel probe for the current Taylor-2018 modularity-lifting boundary.

This verifies only declarations that actually exist. The missing source vocabulary is represented
as graph definition gaps rather than fabricated placeholder propositions.
-/

#check GaloisRep
#check GaloisRep.baseChange
#check GaloisRep.IsIrreducible
#check GaloisRep.IsFlatAt
#check GaloisRep.IsAutomorphicOfLevel
#check cyclic_base_change
#check Deformation.narrowSLiftFunctor
#check Deformation.isCorepresentable_narrowSLiftFunctor
#check ker_RtoT_le_nilradical
#check GaloisRepresentation.IsHardlyRamified

#print axioms GaloisRep.IsAutomorphicOfLevel
#print axioms cyclic_base_change
#print axioms Deformation.isCorepresentable_narrowSLiftFunctor
#print axioms ker_RtoT_le_nilradical
