import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Tame-residue boundary audit

This probe audits only the bounded U1/U2 prefix: inertia closedness and containment of the existing
tame-abelian proxy in local inertia. It does not construct a tame residue character or identify the
proxy with its kernel.
-/

#check AddSubgroup.isClosed_inertia
#check isClosed_localInertiaGroup
#check localTameAbelianInertiaGroup_le_localInertiaGroup

#print axioms AddSubgroup.isClosed_inertia
#print axioms isClosed_localInertiaGroup
#print axioms localTameAbelianInertiaGroup_le_localInertiaGroup
