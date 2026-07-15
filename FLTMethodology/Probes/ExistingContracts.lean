/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

import FLT

/-!
# Existing FLT contract probes

These checks pin the declarations consumed by the methodology graph. They prove only that names and
types elaborate at the frozen upstream commit. They do not remove any upstream admission.
-/

#check FLT.Bosses.B4
#check FLT.Bosses.B4_proof
#check FreyCurve.torsion_isHardlyRamified
#check GaloisRepresentation.IsHardlyRamified
#check GaloisRepresentation.IsHardlyRamified.lifts
#check GaloisRepFamily
#check GaloisRepFamily.isCompatible
#check GaloisRepresentation.IsHardlyRamified.mem_isCompatible
#check GaloisRepresentation.IsHardlyRamified.mod_three
#check GaloisRepresentation.IsHardlyRamified.three_adic
#check GaloisRep.IsAutomorphicOfLevel
#check cyclic_base_change
#check FLT.Bosses.B4_implies_B3
#check flt
