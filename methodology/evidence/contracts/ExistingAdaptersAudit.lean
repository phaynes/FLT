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

/-- info: 'FLT.Components.Existing.BossB1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FLT.Components.Existing.BossB1

/-- info: 'FLT.Components.Existing.BossB2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FLT.Components.Existing.BossB2

/--
info: 'FLT.Components.Existing.BossB3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Components.Existing.BossB3

/--
info: 'FLT.Components.Existing.bossB2_of_bossB3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Components.Existing.bossB2_of_bossB3

/--
info: 'FLT.Components.Existing.bossB1_of_bossB2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Components.Existing.bossB1_of_bossB2

/--
info: 'FLT.Components.Existing.positiveNaturalFlt_of_bossB1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Components.Existing.positiveNaturalFlt_of_bossB1

/--
info: 'GaloisRepresentation.IsHardlyRamified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GaloisRepresentation.IsHardlyRamified

/--
info: 'FLT.ModularityLifting.BlueprintSGood' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.ModularityLifting.BlueprintSGood

/--
info: 'GaloisRep.IsAutomorphicOfLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GaloisRep.IsAutomorphicOfLevel

/-- info: 'GaloisRepFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaloisRepFamily

/--
info: 'GaloisRepFamily.isCompatible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GaloisRepFamily.isCompatible

-- These are deliberately not adapters supplied by this module. Their contaminated closures are
-- mechanically pinned so a future change cannot silently alter the quarantine boundary.
--
-- The complete non-internal `knownin1980s` surface visible from this import was independently
-- enumerated at the FLT-204 review boundary. Besides `knownin1980s` itself, it is:
--
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T_smul_def`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.U_smul_def`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.apply_eq_smul`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.formMap_smul`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instFaithfulSMulSubtypeWeightTwoAutomorphicFormMemSubmoduleFormToStructU₁`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instIsNoetherianEndSubtypeWeightTwoAutomorphicFormMemSubmoduleFormToStructU₁OfIsNoetherianRing`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instIsNoetherianOfIsNoetherianRing`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instIsNoetherianRing`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instIsNoetherianRing_1`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instIsScalarTowerSubtypeWeightTwoAutomorphicFormMemSubmoduleFormToStructU₁`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instModuleSubtypeWeightTwoAutomorphicFormMemSubmoduleFormToStructU₁`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.instSMulCommClassSubtypeWeightTwoAutomorphicFormMemSubmoduleFormToStructU₁`
-- * `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.smul_formTensorScalar`
-- * `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ`
-- * `TotallyDefiniteQuaternionAlgebra.instIsSufficientlySmallToStructU₁OfIsQuaternionAlgebraOfIsTotallyRealOfIsTotallyDefinite`
--
-- `cyclic_base_change` is the sole observed declaration in this import closure whose audit reports
-- `sorryAx` without `knownin1980s`. The boss providers below intentionally expose both sources.
/-- info: 'FLT.Bosses.B4' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FLT.Bosses.B4

/--
info: 'FLT.Bosses.B4_implies_B3' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Bosses.B4_implies_B3

/--
info: 'cyclic_base_change' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cyclic_base_change

/--
info: 'FLT.Bosses.B3_proof' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Bosses.B3_proof

/--
info: 'FLT.Bosses.B2_proof' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Bosses.B2_proof

/--
info: 'FLT.Bosses.B1_proof' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Bosses.B1_proof

/--
info: 'flt' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms flt
