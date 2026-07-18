import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Tame-residue boundary audit

This probe audits only the bounded U1/U2/U3 prefix: inertia closedness, containment of the existing
tame-abelian proxy in local inertia, and the roots-of-unity reduction bridge. It does not construct
a tame residue character, prove Henselian lifting, or identify the proxy with the character kernel.
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
