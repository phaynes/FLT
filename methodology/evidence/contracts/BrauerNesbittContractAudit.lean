import FLT.Components.Contracts.BrauerNesbitt

open FLT.Components.BrauerNesbitt

#check Contract
#check trace_eq_of_charpoly_eq
#check jointImagePoint
#check jointImageSpan
#check jointImageAlgebra
#check jointImageFst
#check jointImageSnd
#check jointImageElement
#check exists_jointImage_basis_from_group
#check FiniteJointImageContract
#check contract_of_finiteJointImageContract

/--
info: 'FLT.Components.BrauerNesbitt.Contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Contract

/--
info: 'FLT.Components.BrauerNesbitt.trace_eq_of_charpoly_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_eq_of_charpoly_eq

/--
info: 'FLT.Components.BrauerNesbitt.jointImageAlgebra' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms jointImageAlgebra

/--
info: 'FLT.Components.BrauerNesbitt.exists_jointImage_basis_from_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_jointImage_basis_from_group

/--
info: 'FLT.Components.BrauerNesbitt.FiniteJointImageContract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FiniteJointImageContract

/--
info: 'FLT.Components.BrauerNesbitt.contract_of_finiteJointImageContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms contract_of_finiteJointImageContract
