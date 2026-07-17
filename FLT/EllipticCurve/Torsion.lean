/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.EllipticCurve.TorsionProvider

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine
open scoped DirectSum

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) :=
  FLT.EllipticCurve.TorsionProvider.nTorsion_finite E hn

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
-- This theorem was well-known in the early part of the 20th century.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 :=
  FLT.EllipticCurve.TorsionProvider.nTorsion_card_sepClosed E hn

-- This theorem was well-known in the early part of the 20th century.
private noncomputable def torsionByAddEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (d : ℕ) :
    Submodule.torsionBy ℤ A d ≃+ Submodule.torsionBy ℤ B d where
  toFun x := ⟨e x.1, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul]
    simpa using congrArg e ((Submodule.mem_torsionBy_iff _ _).mp x.2)⟩
  invFun x := ⟨e.symm x.1, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul]
    simpa using congrArg e.symm ((Submodule.mem_torsionBy_iff _ _).mp x.2)⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv x := by ext; exact e.apply_symm_apply x.1
  map_add' x y := by ext; exact e.map_add x.1 y.1

private noncomputable def torsionByTorsionEquiv {A : Type*} [AddCommGroup A]
    {d n : ℕ} (hd : d ∣ n) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d ≃+
      Submodule.torsionBy ℤ A d where
  toFun x := ⟨x.1.1, by
    rw [Submodule.mem_torsionBy_iff]
    have hx : (d : ℤ) • x.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    exact congrArg Subtype.val hx⟩
  invFun x := ⟨⟨x.1, by
    rw [Submodule.mem_torsionBy_iff]
    have hx : (d : ℤ) • x.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    obtain ⟨c, rfl⟩ := hd
    rw [Nat.mul_comm, Nat.cast_mul, mul_smul, hx, smul_zero]⟩, by
      rw [Submodule.mem_torsionBy_iff]
      apply Subtype.ext
      exact (Submodule.mem_torsionBy_iff _ _).mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := rfl

private lemma card_torsionBy_zmod (m d : ℕ) [NeZero m] :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) d) = Nat.gcd m d := by
  let e : Submodule.torsionBy ℤ (ZMod m) d ≃
      (nsmulAddMonoidHom d : ZMod m →+ ZMod m).ker :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro x
      simp [Submodule.mem_torsionBy_iff])
  rw [Nat.card_congr e]
  simpa using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d

private lemma card_torsionBy_pi_zmod {ι : Type} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (m i)) d) =
      ∏ i, Nat.gcd (m i) d := by
  let e : Submodule.torsionBy ℤ (∀ i, ZMod (m i)) d ≃
      ∀ i, Submodule.torsionBy ℤ (ZMod (m i)) d := {
    toFun x i := ⟨x.1 i, by
      rw [Submodule.mem_torsionBy_iff]
      have hx : (d : ℤ) • (x.1 : ∀ i, ZMod (m i)) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp x.2
      exact congr_fun hx i⟩
    invFun x := ⟨fun i ↦ (x i).1, by
      rw [Submodule.mem_torsionBy_iff]
      funext i
      simpa using (x i).2⟩
    left_inv x := by ext i; rfl
    right_inv x := by ext i; rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ card_torsionBy_zmod (m i) d

private noncomputable def piCongrLeftConstAddEquiv {A B G : Type*} [AddCommGroup G]
    (e : A ≃ B) : (A → G) ≃+ (B → G) where
  toFun f b := f (e.symm b)
  invFun f a := f (e a)
  left_inv f := by funext a; simp
  right_inv f := by funext b; simp
  map_add' x y := by funext b; rfl

private noncomputable def piCongrFiberwiseAddEquiv {A B : Type*} {f : A → B}
    {G : A → Type*} {H : B → Type*}
    [∀ a, AddCommGroup (G a)] [∀ b, AddCommGroup (H b)]
    (e : ∀ b, ((s : {a : A // f a = b}) → G s.1) ≃+ H b) :
    ((a : A) → G a) ≃+ ((b : B) → H b) :=
  { Equiv.piCongrFiberwise (fun b ↦ (e b).toEquiv) with
    map_add' := by
      intro x y
      funext b
      exact (e b).map_add _ _ }

private noncomputable def piCurryAddEquiv {A : Type*} {B : A → Type*}
    {G : ∀ a, B a → Type*} [∀ a b, AddCommGroup (G a b)] :
    (∀ x : Σ a, B a, G x.1 x.2) ≃+ (∀ a b, G a b) :=
  { Equiv.piCurry G with
    map_add' := by intro x y; funext a b; rfl }

private noncomputable def piCommAddEquiv {A B : Type*} {G : A → B → Type*}
    [∀ a b, AddCommGroup (G a b)] :
    (∀ a b, G a b) ≃+ (∀ b a, G a b) :=
  { Equiv.piComm G with
    map_add' := by intro x y; funext b a; rfl }

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  let T := Submodule.torsionBy ℤ A n
  have hn0 : n ≠ 0 := hn.ne'
  have hTcard : Nat.card T = n ^ r := h n dvd_rfl
  letI : Finite T := Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero r hn0)
  obtain ⟨ι, instι, m, hm, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' T
  letI : Fintype ι := instι
  letI : ∀ i, NeZero (m i) := fun i ↦ ⟨(Nat.zero_lt_of_lt (hm i)).ne'⟩
  have hm_dvd (i : ι) : m i ∣ n := by
    apply (ZMod.natCast_eq_zero_iff n (m i)).mp
    let t : T := e.symm (DirectSum.of (fun i ↦ ZMod (m i)) i 1)
    have ht : (n : ℤ) • t = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_torsionBy_iff _ _).mp t.2
    have het := congrArg e ht
    have het' : (n : ℤ) • DirectSum.of (fun i ↦ ZMod (m i)) i 1 = 0 := by
      simpa only [map_zsmul, t, e.apply_symm_apply, map_zero] using het
    have hei : (n : ℤ) • (DirectSum.of (fun i ↦ ZMod (m i)) i 1) i = 0 := by
      calc
        _ = (DFinsupp.evalAddMonoidHom i)
            ((n : ℤ) • DirectSum.of (fun i ↦ ZMod (m i)) i 1) :=
          (map_zsmul (DFinsupp.evalAddMonoidHom i) (n : ℤ)
            (DirectSum.of (fun i ↦ ZMod (m i)) i 1)).symm
        _ = (DFinsupp.evalAddMonoidHom i)
            (0 : ⨁ i, ZMod (m i)) := congrArg _ het'
        _ = (0 : ZMod (m i)) := map_zero (DFinsupp.evalAddMonoidHom i)
    simpa [DirectSum.of_apply, zsmul_eq_mul] using hei
  have hprod (d : ℕ) (hd : d ∣ n) : ∏ i, Nat.gcd (m i) d = d ^ r := by
    rw [← card_torsionBy_pi_zmod m d]
    rw [← Nat.card_congr (torsionByAddEquiv (e.trans (DirectSum.addEquivProd _)) d).toEquiv]
    rw [Nat.card_congr (torsionByTorsionEquiv hd).toEquiv]
    exact h d hd
  have hgcd_prime (p : ℕ) (hp : p.Prime) (i : ι) :
      Nat.gcd (m i) p = if p ∣ m i then p else 1 := by
    by_cases hpi : p ∣ m i
    · simp [hpi, Nat.gcd_eq_right_iff_dvd.mpr hpi]
    · have hcop : Nat.Coprime p (m i) := (hp.coprime_iff_not_dvd).mpr hpi
      simp [hpi, hcop.symm]
  have hfiber_card (p : n.primeFactors) :
      Fintype.card {i : ι // (p : ℕ) ∣ m i} = r := by
    have hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
    have hpd : (p : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors p.2
    apply Nat.pow_right_injective hp.two_le
    calc
      (p : ℕ) ^ Fintype.card {i : ι // (p : ℕ) ∣ m i} =
          (p : ℕ) ^ (Finset.univ.filter fun i ↦ (p : ℕ) ∣ m i).card := by
        rw [Fintype.card_of_subtype (Finset.univ.filter fun i ↦ (p : ℕ) ∣ m i) (by simp)]
      _ = ∏ i, if (p : ℕ) ∣ m i then (p : ℕ) else 1 := by
        simp [Finset.prod_ite]
      _ = ∏ i, Nat.gcd (m i) (p : ℕ) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (hgcd_prime (p : ℕ) hp i).symm
      _ = (p : ℕ) ^ r := hprod p hpd
  have hmprod : ∏ i, m i = n ^ r := by
    calc
      ∏ i, m i = ∏ i, Nat.gcd (m i) n := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (Nat.gcd_eq_left_iff_dvd.mpr (hm_dvd i)).symm
      _ = n ^ r := hprod n dvd_rfl
  have hfacsum (p : ℕ) :
      ∑ i, (m i).factorization p = r * n.factorization p := by
    calc
      ∑ i, (m i).factorization p = (∏ i, m i).factorization p := by
        symm
        exact Nat.factorization_prod_apply fun i hi ↦ (NeZero.ne (m i))
      _ = (n ^ r).factorization p := congrArg (fun x ↦ x.factorization p) hmprod
      _ = r * n.factorization p := by
        rw [Nat.factorization_pow]
        rfl
  have hfactorization_eq (p : n.primeFactors) (i : ι) (hpi : (p : ℕ) ∣ m i) :
      (m i).factorization p = n.factorization p := by
    let s : Finset ι := Finset.univ.filter fun j ↦ (p : ℕ) ∣ m j
    have hs_card : s.card = r := by
      rw [← hfiber_card p]
      exact (Fintype.card_of_subtype s (by simp [s])).symm
    have hle (j : ι) (hj : j ∈ s) :
        (m j).factorization p ≤ n.factorization p :=
      ((Nat.factorization_le_iff_dvd (NeZero.ne (m j)) hn0).mpr (hm_dvd j)) p
    have hsum_s : ∑ j ∈ s, (m j).factorization p = r * n.factorization p := by
      calc
        ∑ j ∈ s, (m j).factorization p = ∑ j, (m j).factorization p := by
          apply Finset.sum_subset (by simp [s])
          intro j hjuniv hjnot
          apply Nat.factorization_eq_zero_of_not_dvd
          simpa [s] using hjnot
        _ = r * n.factorization p := hfacsum p
    have hsum_const : ∑ j ∈ s, n.factorization p = r * n.factorization p := by
      simp [hs_card]
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp (hsum_s.trans hsum_const.symm)
    exact hall i (by simp [s, hpi])
  let J := Σ i : ι, (m i).primeFactors
  let primeMap : J → n.primeFactors := fun j ↦
    ⟨j.2, Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors j.2.2,
        (Nat.dvd_of_mem_primeFactors j.2.2).trans (hm_dvd j.1), hn0⟩⟩
  let fiberIndexEquiv (p : n.primeFactors) :
      {j : J // primeMap j = p} ≃ {i : ι // (p : ℕ) ∣ m i} := {
    toFun := fun j ↦ ⟨j.1.1, by
      have hd : (j.1.2 : ℕ) ∣ m j.1.1 := Nat.dvd_of_mem_primeFactors j.1.2.2
      have heq : (j.1.2 : ℕ) = (p : ℕ) := congrArg Subtype.val j.2
      simpa [heq] using hd⟩
    invFun := fun i ↦
      ⟨⟨i.1, ⟨p, Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors p.2, i.2, NeZero.ne (m i.1)⟩⟩⟩, by
          apply Subtype.ext
          rfl⟩
    left_inv := by
      rintro ⟨⟨i, q⟩, hq⟩
      cases hq
      apply Subtype.ext
      rfl
    right_inv := by
      intro i
      apply Subtype.ext
      rfl }
  let fiberFinEquiv (p : n.primeFactors) :
      {j : J // primeMap j = p} ≃ Fin r :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_congr (fiberIndexEquiv p), hfiber_card p]
      exact (Fintype.card_fin r).symm)
  let fiberAddEquiv (p : n.primeFactors) :
      ((s : {j : J // primeMap j = p}) →
          ZMod ((s.1.2 : ℕ) ^ (m s.1.1).factorization s.1.2)) ≃+
        (Fin r → ZMod ((p : ℕ) ^ n.factorization p)) :=
    (AddEquiv.piCongrRight fun s ↦ by
      have hq : (s.1.2 : ℕ) = (p : ℕ) := congrArg Subtype.val s.2
      have hpdiv : (p : ℕ) ∣ m s.1.1 := by
        have := Nat.dvd_of_mem_primeFactors s.1.2.2
        simpa [hq] using this
      have he := hfactorization_eq p s.1.1 hpdiv
      exact (ZMod.ringEquivCongr (by rw [hq, he])).toAddEquiv).trans
        (piCongrLeftConstAddEquiv (fiberFinEquiv p))
  let decompose : T ≃+ ((j : J) →
      ZMod ((j.2 : ℕ) ^ (m j.1).factorization j.2)) :=
    (e.trans (DirectSum.addEquivProd _)).trans
      ((AddEquiv.piCongrRight fun i ↦
        (ZMod.equivPi (m i) (NeZero.ne (m i))).toAddEquiv).trans
        (piCurryAddEquiv (B := fun i ↦ (m i).primeFactors) (G := fun i p ↦
          ZMod ((p : ℕ) ^ (m i).factorization p))).symm)
  let regroup : ((j : J) →
      ZMod ((j.2 : ℕ) ^ (m j.1).factorization j.2)) ≃+
      ((p : n.primeFactors) → Fin r →
        ZMod ((p : ℕ) ^ n.factorization p)) :=
    piCongrFiberwiseAddEquiv (f := primeMap) fiberAddEquiv
  exact ⟨(decompose.trans regroup).trans <|
    (piCommAddEquiv (G := fun (p : n.primeFactors) (_ : Fin r) ↦
      ZMod ((p : ℕ) ^ n.factorization p))).trans <|
      AddEquiv.piCongrRight fun (_ : Fin r) ↦
        (ZMod.equivPi n hn0).toAddEquiv.symm⟩

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- The positivity condition is essential: at `n = 0`, the torsion submodule is the
-- whole point group, which need not be finitely generated over `ZMod 0 = ℤ`.
noncomputable instance (n : ℕ) [NeZero n] : Module.Finite (ZMod n) (E.nTorsion n) := by
  letI : Finite (E.nTorsion n) := E.n_torsion_finite (NeZero.pos n)
  exact Module.Finite.of_finite

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul P := by
        change WeierstrassCurve.Affine.Point.map (AlgHom.id k K) P = P
        exact DFunLike.congr_fun (WeierstrassCurve.Points.map_id E K) P
      mul_smul g h P := by
        change
          WeierstrassCurve.Affine.Point.map ((g * h).toAlgHom) P =
            WeierstrassCurve.Affine.Point.map g.toAlgHom
              (WeierstrassCurve.Affine.Point.map h.toAlgHom P)
        rw [show (g * h).toAlgHom = g.toAlgHom.comp h.toAlgHom by ext x; rfl]
        exact
          (WeierstrassCurve.Affine.Point.map_map (h : K →ₐ[k] K) (g : K →ₐ[k] K) P).symm
      smul_zero g := map_zero (WeierstrassCurve.Points.map E (g : K →ₐ[k] K))
      smul_add g P Q := map_add (WeierstrassCurve.Points.map E (g : K →ₐ[k] K)) P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

abbrev WeierstrassCurve.AbsoluteTorsion {K : Type u} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq (AlgebraicClosure K)] (n : ℕ) :=
  (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n

noncomputable def WeierstrassCurve.torsionGaloisMap
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (σ : Field.absoluteGaloisGroup K) :
    E.AbsoluteTorsion n →+ E.AbsoluteTorsion n where
  toFun P := ⟨WeierstrassCurve.Points.map E σ P.1, by
    rw [Submodule.mem_torsionBy_iff]
    have hP : (n : ℤ) • P.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp P.2
    calc
      (n : ℤ) • WeierstrassCurve.Points.map E σ.toAlgHom P.1 =
          WeierstrassCurve.Points.map E σ.toAlgHom ((n : ℤ) • P.1) :=
        ((WeierstrassCurve.Points.map E σ.toAlgHom).map_zsmul (n : ℤ) P.1).symm
      _ = WeierstrassCurve.Points.map E σ.toAlgHom 0 := congrArg _ hP
      _ = 0 := map_zero (WeierstrassCurve.Points.map E σ.toAlgHom)⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (WeierstrassCurve.Points.map E σ.toAlgHom)
  map_add' P Q := by
    apply Subtype.ext
    exact map_add (WeierstrassCurve.Points.map E σ.toAlgHom) P.1 Q.1

noncomputable def WeierstrassCurve.torsionGaloisLinearMap
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (σ : Field.absoluteGaloisGroup K) :
    E.AbsoluteTorsion n →ₗ[ZMod n] E.AbsoluteTorsion n :=
  (E.torsionGaloisMap n σ).toZModLinearMap n

noncomputable def WeierstrassCurve.torsionGaloisActionHom
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) :
    Field.absoluteGaloisGroup K →* Module.End (ZMod n) (E.AbsoluteTorsion n) where
  toFun := E.torsionGaloisLinearMap n
  map_one' := by
    ext P
    change WeierstrassCurve.Points.map E
      (AlgHom.id K (AlgebraicClosure K)) P.1 = P.1
    exact DFunLike.congr_fun
      (WeierstrassCurve.Points.map_id E (AlgebraicClosure K)) P.1
  map_mul' σ τ := by
    ext P
    change WeierstrassCurve.Points.map E ((σ * τ).toAlgHom) P.1 =
      WeierstrassCurve.Points.map E σ.toAlgHom
        (WeierstrassCurve.Points.map E τ.toAlgHom P.1)
    rw [show (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom by ext x; rfl]
    exact DFunLike.congr_fun
      (WeierstrassCurve.Points.map_comp E (AlgebraicClosure K) (AlgebraicClosure K)
        (AlgebraicClosure K) τ.toAlgHom σ.toAlgHom) P.1 |>.symm

lemma WeierstrassCurve.torsionGaloisPointStabilizer_isOpen
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (P : E.AbsoluteTorsion n) :
    IsOpen {σ : Field.absoluteGaloisGroup K | E.torsionGaloisActionHom n σ P = P} := by
  rcases P with ⟨P, hP⟩
  rcases P with _ | ⟨x, y, hxy⟩
  · have heq : {σ : Field.absoluteGaloisGroup K | E.torsionGaloisActionHom n σ
        (⟨.zero, hP⟩ : E.AbsoluteTorsion n) = ⟨.zero, hP⟩} = Set.univ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hz : (⟨.zero, hP⟩ : E.AbsoluteTorsion n) = 0 := rfl
      simpa only [hz] using map_zero (E.torsionGaloisActionHom n σ)
    rw [heq]
    exact isOpen_univ
  · have hx : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup K) x :
          Set (Field.absoluteGaloisGroup K)) := stabilizer_isOpen_of_isIntegral x
    have hy : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup K) y :
          Set (Field.absoluteGaloisGroup K)) := stabilizer_isOpen_of_isIntegral y
    rw [show {σ : Field.absoluteGaloisGroup K | E.torsionGaloisActionHom n σ
        (⟨.some x y hxy, hP⟩ : E.AbsoluteTorsion n) = ⟨.some x y hxy, hP⟩} =
        (MulAction.stabilizer (Field.absoluteGaloisGroup K) x :
          Set (Field.absoluteGaloisGroup K)) ∩
        (MulAction.stabilizer (Field.absoluteGaloisGroup K) y :
          Set (Field.absoluteGaloisGroup K)) by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro h
        have h' : WeierstrassCurve.Points.map E σ.toAlgHom (.some x y hxy) =
            .some x y hxy := congrArg Subtype.val h
        have hcoords : σ x = x ∧ σ y = y := by
          simpa [WeierstrassCurve.Points.map] using
            WeierstrassCurve.Affine.Point.some.inj h'
        exact ⟨MulAction.mem_stabilizer_iff.mpr hcoords.1,
          MulAction.mem_stabilizer_iff.mpr hcoords.2⟩
      · rintro ⟨hx, hy⟩
        apply Subtype.ext
        have hx' : σ x = x := MulAction.mem_stabilizer_iff.mp hx
        have hy' : σ y = y := MulAction.mem_stabilizer_iff.mp hy
        change WeierstrassCurve.Affine.Point.some (σ x) (σ y) _ = .some x y hxy
        simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro hx' hy']
    exact hx.inter hy

lemma WeierstrassCurve.torsionGaloisActionHom_ker_isOpen
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
    IsOpen ((E.torsionGaloisActionHom n).ker : Set (Field.absoluteGaloisGroup K)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : Finite (E.AbsoluteTorsion n) :=
    (E.map (algebraMap K (AlgebraicClosure K))).n_torsion_finite hn
  rw [show ((E.torsionGaloisActionHom n).ker : Set (Field.absoluteGaloisGroup K)) =
      ⋂ P : E.AbsoluteTorsion n,
        {σ : Field.absoluteGaloisGroup K | E.torsionGaloisActionHom n σ P = P} by
    ext σ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    change E.torsionGaloisActionHom n σ = 1 ↔
      ∀ P : E.AbsoluteTorsion n, E.torsionGaloisActionHom n σ P = P
    constructor
    · intro h P
      rw [h]
      rfl
    · intro h
      ext P
      simpa using h P]
  exact isOpen_iInter_of_finite (E.torsionGaloisPointStabilizer_isOpen n)

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
noncomputable def WeierstrassCurve.galoisRep {K : Type u} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
    GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : Finite (E.AbsoluteTorsion n) :=
    (E.map (algebraMap K (AlgebraicClosure K))).n_torsion_finite hn
  letI := moduleTopology (ZMod n) (Module.End (ZMod n) (E.AbsoluteTorsion n))
  letI : ContinuousMul (Module.End (ZMod n) (E.AbsoluteTorsion n)) :=
    ⟨IsModuleTopology.continuous_mul_of_finite (ZMod n)
      (Module.End (ZMod n) (E.AbsoluteTorsion n))⟩
  exact ⟨E.torsionGaloisActionHom n,
    MonoidHom.continuous_of_isOpen_ker (E.torsionGaloisActionHom_ker_isOpen n hn)⟩
