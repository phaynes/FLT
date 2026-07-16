import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import FLTMethodology.Probes.MLTSourceBoundary

/-!
Type-correct contracts and regressions for the open `FLT-BRAUER-NESBITT` leaf.

This module does not close that leaf. It freezes the full group-representation contract, the first
missing general algebra result in the source proof, and the smaller rank-two odd-characteristic
contract needed at the current Taylor-2018 boundary. It also prevents a tempting but false
one-sided trace weakening.
-/

namespace FLTProbe.BrauerNesbitt

open scoped MonoidAlgebra

/-- Full graph target: semisimple representations with matching characteristic polynomials on
every group element are equivalent. -/
def GroupContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      (∀ g, (rho g).charpoly = (sigma g).charpoly) →
      Nonempty (Representation.Equiv rho sigma)

/-- Character of a finite-dimensional module over a finite-dimensional algebra. -/
noncomputable def moduleCharacter
    {k A M : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] : A →ₗ[k] k :=
  (LinearMap.trace k M).comp (Algebra.lsmul k k M).toLinearMap

/-- The characteristic-polynomial hypothesis supplies the trace identity used by both source
proof architectures. -/
theorem trace_eq_of_charpoly_eq
    {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : Module.End k V) (g : Module.End k W)
    (h : f.charpoly = g.charpoly) :
    LinearMap.trace k V f = LinearMap.trace k W g := by
  let bV := Module.Free.chooseBasis k V
  let bW := Module.Free.chooseBasis k W
  calc
    LinearMap.trace k V f = Matrix.trace (LinearMap.toMatrix bV bV f) :=
      LinearMap.trace_eq_matrix_trace k bV f
    _ = -(LinearMap.toMatrix bV bV f).charpoly.nextCoeff :=
      Matrix.trace_eq_neg_charpoly_nextCoeff _
    _ = -f.charpoly.nextCoeff := by rw [LinearMap.charpoly_toMatrix]
    _ = -g.charpoly.nextCoeff := by rw [h]
    _ = -(LinearMap.toMatrix bW bW g).charpoly.nextCoeff := by
      rw [LinearMap.charpoly_toMatrix]
    _ = Matrix.trace (LinearMap.toMatrix bW bW g) :=
      (Matrix.trace_eq_neg_charpoly_nextCoeff _).symm
    _ = LinearMap.trace k W g := (LinearMap.trace_eq_matrix_trace k bW g).symm

/-! ### Finite-dimensional joint-image reduction

The possibly infinite group is replaced by the finite-dimensional algebra linearly spanned by its
joint action on the two representations. No characteristic-polynomial identity is extended
linearly here: this tranche only exposes a finite basis consisting of actual group elements.
-/

universe uK uG uV uW

section JointImage

variable {k : Type uK} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable (rho : Representation k G V) (sigma : Representation k G W)

/-- The pair of matrices through which one group element acts on the two representations. -/
def jointImagePoint (g : G) : Module.End k V × Module.End k W :=
  (rho g, sigma g)

/-- The linear span of the joint group image. -/
def jointImageSpan : Submodule k (Module.End k V × Module.End k W) :=
  Submodule.span k (Set.range (jointImagePoint rho sigma))

/-- The joint-image span is a subalgebra: products of generators are again group-image
generators, and bilinearity extends this fact to the whole span. -/
noncomputable def jointImageAlgebra : Subalgebra k (Module.End k V × Module.End k W) where
  carrier := jointImageSpan rho sigma
  zero_mem' := (jointImageSpan rho sigma).zero_mem
  add_mem' := (jointImageSpan rho sigma).add_mem
  one_mem' := by
    apply Submodule.subset_span
    exact ⟨1, by simp [jointImagePoint]⟩
  mul_mem' := by
    intro x y hx hy
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (jointImageSpan rho sigma) (Set.range (jointImagePoint rho sigma))
      (Set.range (jointImagePoint rho sigma))
      (LinearMap.mul k (Module.End k V × Module.End k W))
    · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      apply Submodule.subset_span
      exact ⟨g * h, by simp [jointImagePoint]⟩
    · exact hx
    · exact hy
  algebraMap_mem' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    exact (jointImageSpan rho sigma).smul_mem r (by
      apply Submodule.subset_span
      exact ⟨1, by simp [jointImagePoint]⟩)

/-- First projection of the joint-image algebra, recovering its action on `V`. -/
noncomputable def jointImageFst :
    jointImageAlgebra rho sigma →ₐ[k] Module.End k V :=
  (AlgHom.fst k (Module.End k V) (Module.End k W)).comp
    (jointImageAlgebra rho sigma).val

/-- Second projection of the joint-image algebra, recovering its action on `W`. -/
noncomputable def jointImageSnd :
    jointImageAlgebra rho sigma →ₐ[k] Module.End k W :=
  (AlgHom.snd k (Module.End k V) (Module.End k W)).comp
    (jointImageAlgebra rho sigma).val

/-- A group element regarded as an element of the joint-image algebra. -/
noncomputable def jointImageElement (g : G) : jointImageAlgebra rho sigma :=
  ⟨jointImagePoint rho sigma g, Submodule.subset_span (Set.mem_range_self g)⟩

@[simp]
theorem jointImageFst_element (g : G) :
    jointImageFst rho sigma (jointImageElement rho sigma g) = rho g := rfl

@[simp]
theorem jointImageSnd_element (g : G) :
    jointImageSnd rho sigma (jointImageElement rho sigma g) = sigma g := rfl

theorem jointImageAlgebra_toSubmodule :
    (jointImageAlgebra rho sigma).toSubmodule = jointImageSpan rho sigma := rfl

variable [Module.Finite k V] [Module.Finite k W]

/-- A basis of the joint-image span can be selected from actual group-image pairs. Its cardinality
is exactly the finrank of that span. -/
theorem exists_jointImage_basis_from_group :
    ∃ g : Fin (Module.finrank k (jointImageSpan rho sigma)) → G,
      LinearIndependent k (fun i ↦ jointImagePoint rho sigma (g i)) ∧
        Submodule.span k (Set.range (fun i ↦ jointImagePoint rho sigma (g i))) =
          jointImageSpan rho sigma := by
  unfold jointImageSpan
  obtain ⟨f, hfS, hfspan, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq k
    (Set.range (jointImagePoint rho sigma))
  choose g hg using hfS
  have hgf : (fun i ↦ jointImagePoint rho sigma (g i)) = f := funext hg
  refine ⟨g, ?_, ?_⟩
  · rw [hgf]
    exact hfli
  · rw [hgf]
    exact hfspan

end JointImage

/-- Exact finite-support remainder after extracting the joint image algebra and a basis of actual
group elements. This is strictly downstream of `GroupContract`; it remains the open algebraic
terminal after this tranche. -/
def FiniteJointImageContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      (∀ g, (rho g).charpoly = (sigma g).charpoly) →
      ∀ (g : Fin (Module.finrank k (jointImageSpan rho sigma)) → G),
        LinearIndependent k (fun i ↦ jointImagePoint rho sigma (g i)) →
        Submodule.span k (Set.range (fun i ↦ jointImagePoint rho sigma (g i))) =
          jointImageSpan rho sigma →
        Nonempty (Representation.Equiv rho sigma)

/-- The finite joint-image contract is sufficient for the unchanged full group contract. -/
theorem groupContract_of_finiteJointImageContract
    (hfinite : FiniteJointImageContract.{uK, uG, uV, uW}) :
    GroupContract.{uK, uG, uV, uW} := by
  intro k G V W _ _ _ _ _ _ _ _ rho sigma hrho hsigma hchar
  obtain ⟨g, hli, hspan⟩ := exists_jointImage_basis_from_group rho sigma
  exact hfinite rho sigma hrho hsigma hchar g hli hspan

/-- First absent terminal in the algebraically closed specialization: distinct simple modules
over a finite-dimensional algebra have linearly independent characters. The full arbitrary-field
route needs an additional spanning-set/descent argument and is not reduced to this contract. -/
def SimpleCharactersLinearIndependentContract : Prop :=
  ∀ {k A ι : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [Module.Finite k A] [Finite ι]
    (S : ι → Type*)
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)] [∀ i, Module A (S i)]
    [∀ i, IsScalarTower k A (S i)] [∀ i, Module.Finite k (S i)]
    [∀ i, IsSimpleModule A (S i)],
    (Pairwise fun i j ↦ IsEmpty (S i ≃ₗ[A] S j)) →
      LinearIndependent k (fun i ↦ moduleCharacter (k := k) (A := A) (M := S i))

/-- Smaller true specialization suggested by the source proof: trace equality is enough when
the characteristic is zero or exceeds the representation dimension. -/
def SmallDimensionTraceContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      Module.finrank k V = Module.finrank k W →
      (ringChar k = 0 ∨
        (Module.finrank k V < ringChar k ∧ Module.finrank k W < ringChar k)) →
      (∀ g, LinearMap.trace k V (rho g) = LinearMap.trace k W (sigma g)) →
      Nonempty (Representation.Equiv rho sigma)

/-- Minimal immediate Taylor-2018 specialization: both residual spaces are two-dimensional over
an algebraically closed residue coefficient field and the residual characteristic is odd. -/
def AlgClosedTwoDimensionalTraceContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      Module.finrank k V = 2 → Module.finrank k W = 2 →
      2 < ringChar k →
      (∀ g, LinearMap.trace k V (rho g) = LinearMap.trace k W (sigma g)) →
      Nonempty (Representation.Equiv rho sigma)

/-- Refuted predecessor of `SmallDimensionTraceContract`: bounding only the first dimension and
omitting equal rank permits dimensions `1` and `p+1` to have equal traces in characteristic `p`.
-/
def RefutedOneSidedTraceContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      (ringChar k = 0 ∨ Module.finrank k V < ringChar k) →
      (∀ g, LinearMap.trace k V (rho g) = LinearMap.trace k W (sigma g)) →
      Nonempty (Representation.Equiv rho sigma)

section Counterexample

abbrev F2 := ZMod 2
abbrev V1 := Fin 1 → F2
abbrev V3 := Fin 3 → F2

/-- A finite kernel regression showing that the one-sided trace contract is false. -/
theorem refutedOneSidedTraceContract_false :
    ¬ RefutedOneSidedTraceContract.{0, 0, 0, 0} := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : NeZero (Nat.card Unit : F2) := ⟨by simp⟩
  intro h
  let rho : Representation F2 Unit V1 := Representation.trivial F2 Unit V1
  let sigma : Representation F2 Unit V3 := Representation.trivial F2 Unit V3
  have hrho : Representation.IsSemisimpleRepresentation rho := by infer_instance
  have hsigma : Representation.IsSemisimpleRepresentation sigma := by infer_instance
  have hsmall : ringChar F2 = 0 ∨ Module.finrank F2 V1 < ringChar F2 := by
    right
    rw [Module.finrank_fin_fun, ZMod.ringChar_zmod_n]
    decide
  have htrace : ∀ g, LinearMap.trace F2 V1 (rho g) = LinearMap.trace F2 V3 (sigma g) := by
    intro g
    have : g = () := Subsingleton.elim _ _
    subst g
    rw [show rho () = LinearMap.id by ext; simp [rho],
      show sigma () = LinearMap.id by ext; simp [sigma],
      LinearMap.trace_id, LinearMap.trace_id,
      Module.finrank_fin_fun, Module.finrank_fin_fun]
    decide
  obtain ⟨e⟩ := h (k := F2) (G := Unit) (V := V1) (W := V3)
    rho sigma hrho hsigma hsmall htrace
  have hdim := LinearEquiv.finrank_eq e.toLinearEquiv
  norm_num [V1, V3, F2] at hdim

end Counterexample

section ConsumerBridge

open FLTMethodology.Taylor2018

universe uF uR uV0 uk uW1 uW2

/-- Kernel-clean wiring proof: the full group contract is sufficient for the current
same-field residual-model uniqueness target. This does not assume or prove the contract. -/
theorem semisimplifiedResidualModelsUnique_of_groupContract
    (hBN : GroupContract.{uk, uF, uW1, uW2})
    {F : Type uF} [Field F] [NumberField F]
    {R : Type uR} [CommRing R] [IsLocalRing R]
      [TopologicalSpace R] [IsTopologicalRing R]
    {V0 : Type uV0} [AddCommGroup V0] [Module R V0]
      [Module.Finite R V0] [Module.Free R V0]
    (rho0 : GaloisRep F R V0)
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
      [Algebra R k] [ContinuousSMul R k]
    {W1 : Type uW1} {W2 : Type uW2}
      [AddCommGroup W1] [Module k W1] [Module.Finite k W1] [Module.Free k W1]
      [AddCommGroup W2] [Module k W2] [Module.Finite k W2] [Module.Free k W2]
    (rho1 : GaloisRep F k W1) (rho2 : GaloisRep F k W2) :
    SemisimplifiedResidualModelsUnique rho0 rho1 rho2 := by
  intro h1 h2
  have hs1 : Representation.IsSemisimpleRepresentation rho1.toRepresentation := h1.2.1
  have hs2 : Representation.IsSemisimpleRepresentation rho2.toRepresentation := h2.2.1
  have hchar : ∀ g, (rho1.toRepresentation g).charpoly =
      (rho2.toRepresentation g).charpoly := fun g ↦ (h1.2.2 g).symm.trans (h2.2.2 g)
  obtain ⟨e⟩ := hBN rho1.toRepresentation rho2.toRepresentation hs1 hs2 hchar
  refine ⟨e.toLinearEquiv, ?_⟩
  apply GaloisRep.ext
  intro g
  exact e.conj_apply_self g

/-- Exact specialization probe for the intended residual coefficient boundary. It shows that the
algebraically closed, two-dimensional, odd-characteristic trace contract proves the existing
same-field consumer once those three additional hypotheses are supplied explicitly. -/
theorem specializedResidualModelsUnique
    (hBN : AlgClosedTwoDimensionalTraceContract.{uk, uF, uW1, uW2})
    {F : Type uF} [Field F] [NumberField F]
    {R : Type uR} [CommRing R] [IsLocalRing R]
      [TopologicalSpace R] [IsTopologicalRing R]
    {V0 : Type uV0} [AddCommGroup V0] [Module R V0]
      [Module.Finite R V0] [Module.Free R V0]
    (rho0 : GaloisRep F R V0)
    {k : Type uk} [Field k] [IsAlgClosed k]
      [TopologicalSpace k] [IsTopologicalRing k]
      [Algebra R k] [ContinuousSMul R k]
    {W1 : Type uW1} {W2 : Type uW2}
      [AddCommGroup W1] [Module k W1] [Module.Finite k W1] [Module.Free k W1]
      [AddCommGroup W2] [Module k W2] [Module.Finite k W2] [Module.Free k W2]
    (rho1 : GaloisRep F k W1) (rho2 : GaloisRep F k W2)
    (hW1 : Module.finrank k W1 = 2) (hW2 : Module.finrank k W2 = 2)
    (hodd : 2 < ringChar k) :
    SemisimplifiedResidualModelsUnique rho0 rho1 rho2 := by
  intro h1 h2
  have hs1 : Representation.IsSemisimpleRepresentation rho1.toRepresentation := h1.2.1
  have hs2 : Representation.IsSemisimpleRepresentation rho2.toRepresentation := h2.2.1
  have htrace : ∀ g, LinearMap.trace k W1 (rho1.toRepresentation g) =
      LinearMap.trace k W2 (rho2.toRepresentation g) := by
    intro g
    apply trace_eq_of_charpoly_eq
    exact (h1.2.2 g).symm.trans (h2.2.2 g)
  obtain ⟨e⟩ := hBN rho1.toRepresentation rho2.toRepresentation
    hs1 hs2 hW1 hW2 hodd htrace
  refine ⟨e.toLinearEquiv, ?_⟩
  apply GaloisRep.ext
  intro g
  exact e.conj_apply_self g

end ConsumerBridge

#check GroupContract
#check moduleCharacter
#check trace_eq_of_charpoly_eq
#check jointImagePoint
#check jointImageSpan
#check jointImageAlgebra
#check jointImageFst
#check jointImageSnd
#check jointImageElement
#check jointImageFst_element
#check jointImageSnd_element
#check jointImageAlgebra_toSubmodule
#check exists_jointImage_basis_from_group
#check FiniteJointImageContract
#check groupContract_of_finiteJointImageContract
#check SimpleCharactersLinearIndependentContract
#check SmallDimensionTraceContract
#check AlgClosedTwoDimensionalTraceContract
#check RefutedOneSidedTraceContract
#check specializedResidualModelsUnique

#print axioms GroupContract
#print axioms moduleCharacter
#print axioms trace_eq_of_charpoly_eq
#print axioms jointImagePoint
#print axioms jointImageSpan
#print axioms jointImageAlgebra
#print axioms jointImageFst
#print axioms jointImageSnd
#print axioms jointImageElement
#print axioms jointImageFst_element
#print axioms jointImageSnd_element
#print axioms jointImageAlgebra_toSubmodule
#print axioms exists_jointImage_basis_from_group
#print axioms FiniteJointImageContract
#print axioms groupContract_of_finiteJointImageContract
#print axioms SimpleCharactersLinearIndependentContract
#print axioms SmallDimensionTraceContract
#print axioms AlgClosedTwoDimensionalTraceContract
#print axioms RefutedOneSidedTraceContract
#print axioms refutedOneSidedTraceContract_false
#print axioms semisimplifiedResidualModelsUnique_of_groupContract
#print axioms specializedResidualModelsUnique

end FLTProbe.BrauerNesbitt
