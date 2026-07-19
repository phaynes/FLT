import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Tame-residue boundary audit

This probe audits the bounded U1--U4 prefix: inertia closedness, containment of the existing
tame-abelian proxy in local inertia, the roots-of-unity reduction bridge, and construction of the
tame Kummer residue character. It does not prove Henselian lifting or identify the proxy with the
character kernel.
-/

#check AddSubgroup.isClosed_inertia
#check isClosed_localInertiaGroup
#check localTameAbelianInertiaGroup_le_localInertiaGroup
#check eq_one_of_pow_eq_one_of_residue_eq_one
#check rootsOfUnity_residue_injective
#check finiteFieldUnitsToRootsOfUnity
#check finiteFieldUnitsToRootsOfUnity_injective
#check finiteFieldUnitsToRootsOfUnity_bijective
#check finiteFieldUnitsEquivRootsOfUnity
#check isUnit_card_sub_one_ICv
#check residueUnitsEquivRootsOfUnity_at_place
#check tameRootsReduction_at_place
#check tameRootsReduction_at_place_injective
#check galoisRatio_pow_eq_one
#check integralGaloisRatioRoot
#check tameUniformizer
#check tameUniformizer_valuation
#check tameUniformizer_ne_zero
#check tameKummerRoot
#check tameKummerRoot_pow
#check tameKummerRoot_ne_zero
#check tameKummerRatioRoot
#check tameResidueCharFun
#check localInertia_residue_smul_eq
#check galoisRatio_mul
#check tameKummerRatioRoot_one
#check tameResidueCharFun_one
#check tameResidueCharFun_mul
#check tameResidueChar

#print axioms AddSubgroup.isClosed_inertia
#print axioms isClosed_localInertiaGroup
#print axioms localTameAbelianInertiaGroup_le_localInertiaGroup
#print axioms eq_one_of_pow_eq_one_of_residue_eq_one
#print axioms rootsOfUnity_residue_injective
#print axioms finiteFieldUnitsToRootsOfUnity
#print axioms finiteFieldUnitsToRootsOfUnity_injective
#print axioms finiteFieldUnitsToRootsOfUnity_bijective
#print axioms finiteFieldUnitsEquivRootsOfUnity
#print axioms isUnit_card_sub_one_ICv
#print axioms residueUnitsEquivRootsOfUnity_at_place
#print axioms tameRootsReduction_at_place
#print axioms tameRootsReduction_at_place_injective
#print axioms galoisRatio_pow_eq_one
#print axioms integralGaloisRatioRoot
#print axioms tameUniformizer
#print axioms tameUniformizer_valuation
#print axioms tameUniformizer_ne_zero
#print axioms tameKummerRoot
#print axioms tameKummerRoot_pow
#print axioms tameKummerRoot_ne_zero
#print axioms tameKummerRatioRoot
#print axioms tameResidueCharFun
#print axioms localInertia_residue_smul_eq
#print axioms galoisRatio_mul
#print axioms tameKummerRatioRoot_one
#print axioms tameResidueCharFun_one
#print axioms tameResidueCharFun_mul
#print axioms tameResidueChar
