/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

import FLT

/-!
# Kernel probes for high-value library candidates

Presence and type elaboration do not establish that an admitted declaration is reusable. The
methodology library classifies exact interfaces, adaptable interfaces, proof patterns, and false
positives separately.
-/

#check FermatLastTheorem.of_p_ge_5
#check PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
#check FLT.Bosses.B4_implies_B3
#check GaloisRep.baseChange
#check GaloisRep.toLocal
#check GaloisRep.charFrob
#check GaloisRepFamily.isCompatible
#check Deformation.SLiftFunctor
#check Deformation.narrowSLiftFunctor
#check Deformation.isCorepresentable_narrowSLiftFunctor
#check Deformation.narrowSLiftUniversalRingCorepresentableBy
#check ker_RtoT_le_nilradical
#check GaloisRep.IsAutomorphicOfLevel
#check cyclic_base_change
#check GaloisRepresentation.IsHardlyRamified
