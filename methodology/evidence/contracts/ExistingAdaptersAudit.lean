import FLT.Components.Existing
import FLT.Proof

#check FLT.Components.Existing.BossB1
#check FLT.Components.Existing.BossB2
#check FLT.Components.Existing.BossB3
#check FLT.Components.Existing.bossB2_of_bossB3
#check FLT.Components.Existing.bossB1_of_bossB2
#check FLT.Components.Existing.positiveNaturalFlt_of_bossB1

example : FLT.Components.Existing.BossB1 = FLT.Bosses.B1 := rfl
example : FLT.Components.Existing.BossB2 = FLT.Bosses.B2 := rfl
example : FLT.Components.Existing.BossB3 = FLT.Bosses.B3 := rfl

#check GaloisRepresentation.IsHardlyRamified
#check FLT.ModularityLifting.BlueprintSGood
#check GaloisRep.IsAutomorphicOfLevel
#check GaloisRepFamily
#check GaloisRepFamily.isCompatible

#print axioms FLT.Components.Existing.BossB1
#print axioms FLT.Components.Existing.BossB2
#print axioms FLT.Components.Existing.BossB3
#print axioms FLT.Components.Existing.bossB2_of_bossB3
#print axioms FLT.Components.Existing.bossB1_of_bossB2
#print axioms FLT.Components.Existing.positiveNaturalFlt_of_bossB1
#print axioms GaloisRepresentation.IsHardlyRamified
#print axioms FLT.ModularityLifting.BlueprintSGood
#print axioms GaloisRep.IsAutomorphicOfLevel
#print axioms GaloisRepFamily
#print axioms GaloisRepFamily.isCompatible

-- These are deliberately not adapters supplied by this module. Their current closures remain open.
#print axioms FLT.Bosses.B4
#print axioms FLT.Bosses.B4_implies_B3
#print axioms cyclic_base_change
