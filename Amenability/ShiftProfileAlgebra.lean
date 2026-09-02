/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.LocallyMatrixProfile
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The shift-profile algebra

This file realizes the profile sequence in a two-generator algebra of
endomorphisms of a countably generated free module.  The shift moves basis
vectors to the right, while the profile operator stores the sequence in its
zeroth row.
-/

namespace HopfAmenability.ShiftProfileAlgebra

noncomputable section

universe u

open LocallyMatrixProfile

variable (k : Type u) [Field k]

/-- The countably generated free module over the locally matrix algebra. -/
abbrev ProfileModule := ℕ →₀ Limit k

/-- Its algebra of module endomorphisms. -/
abbrev ProfileEnd := Module.End (Limit k) (ProfileModule k)

/-- The standard basis vector. -/
def basisVector (j : ℕ) : ProfileModule k :=
  Finsupp.single j 1

/-- The unilateral shift. -/
def shift : ProfileEnd k :=
  Finsupp.lmapDomain (Limit k) (Limit k) Nat.succ

/-- The zeroth-row operator storing the entire weighted profile. -/
def store : ProfileEnd k :=
  (Finsupp.basisSingleOne.constr k)
    (fun j : ℕ => Finsupp.single 0 (profileElement k j))

@[simp]
theorem shift_basisVector (j : ℕ) :
    shift k (basisVector k j) = basisVector k (j + 1) := by
  simp [shift, basisVector, Finsupp.lmapDomain_apply]

@[simp]
theorem store_basisVector (j : ℕ) :
    store k (basisVector k j) =
      Finsupp.single 0 (profileElement k j) := by
  simpa only [store, basisVector, Finsupp.coe_basisSingleOne] using
    Finsupp.basisSingleOne.constr_basis k
      (fun j : ℕ => Finsupp.single 0 (profileElement k j)) j

@[simp]
theorem store_basisVector_zero :
    store k (basisVector k 0) = basisVector k 0 := by
  simpa [basisVector, profileElement] using store_basisVector k 0

/-- The profile operator is idempotent because its zeroth profile entry is
the identity. -/
theorem store_mul_store : store k * store k = store k := by
  apply Finsupp.basisSingleOne.ext
  intro j
  change store k (store k (basisVector k j)) = store k (basisVector k j)
  rw [store_basisVector]
  rw [← Finsupp.smul_single_one]
  change store k (profileElement k j • basisVector k 0) =
    profileElement k j • basisVector k 0
  rw [map_smul, store_basisVector_zero]

@[simp]
theorem shift_single (j : ℕ) (a : Limit k) :
    shift k (Finsupp.single j a) = Finsupp.single (j + 1) a := by
  rw [← Finsupp.smul_single_one]
  change shift k (a • basisVector k j) = _
  rw [map_smul, shift_basisVector]
  simp [basisVector]

@[simp]
theorem shift_pow_single (n j : ℕ) (a : Limit k) :
    ((shift k) ^ n) (Finsupp.single j a) = Finsupp.single (j + n) a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change shift k (((shift k) ^ n) (Finsupp.single j a)) = _
      rw [ih, shift_single]
      congr 1

@[simp]
theorem store_single (j : ℕ) (a : Limit k) :
    store k (Finsupp.single j a) =
      Finsupp.single 0 (a * profileElement k j) := by
  rw [← Finsupp.smul_single_one]
  change store k (a • basisVector k j) = _
  rw [map_smul, store_basisVector, Finsupp.smul_single]
  rfl

/-- The operator word `C Sⁱ¹ C ⋯ Sⁱᵐ C`. -/
def readWord (k : Type u) [Field k] : List ℕ → ProfileEnd k
  | [] => store k
  | i :: word => store k * (shift k) ^ i * readWord k word

theorem readWord_append_single (word : List ℕ) (i : ℕ) :
    readWord k (word ++ [i]) =
      readWord k word * (shift k) ^ i * store k := by
  induction word with
  | nil => simp [readWord]
  | cons j word ih =>
      simp only [List.cons_append, readWord]
      rw [ih]
      simp [mul_assoc]

/-- Reading an operator word at the zeroth basis vector returns the reversed
profile product.  The reversal is caused by using a free left module rather
than the right-module convention of the article and has no effect on the
weighted profile space. -/
theorem readWord_basisVector_zero (word : List ℕ) :
    readWord k word (basisVector k 0) =
      Finsupp.single 0 (profileProduct k word.reverse) := by
  induction word with
  | nil =>
      change store k (basisVector k 0) = Finsupp.single 0 1
      simpa [basisVector] using store_basisVector_zero k
  | cons i word ih =>
      rw [readWord]
      change store k (((shift k) ^ i)
        (readWord k word (basisVector k 0))) = _
      rw [ih, shift_pow_single, store_single]
      simp [profileProduct, List.reverse_cons, List.map_append,
        List.prod_append]

/-- A one-row profile operator. -/
def rho (p : ℕ) (u : Limit k) (q : ℕ) : ProfileEnd k :=
  (Finsupp.basisSingleOne.constr k) fun j : ℕ =>
    Finsupp.single p (profileElement k (q + j) * u)

@[simp]
theorem rho_basisVector (p : ℕ) (u : Limit k) (q j : ℕ) :
    rho k p u q (basisVector k j) =
      Finsupp.single p (profileElement k (q + j) * u) := by
  simpa only [rho, basisVector, Finsupp.coe_basisSingleOne] using
    Finsupp.basisSingleOne.constr_basis k
      (fun j : ℕ =>
        Finsupp.single p (profileElement k (q + j) * u)) j

@[simp]
theorem rho_single (p : ℕ) (u : Limit k) (q j : ℕ)
    (a : Limit k) :
    rho k p u q (Finsupp.single j a) =
      Finsupp.single p (a * (profileElement k (q + j) * u)) := by
  rw [← Finsupp.smul_single_one]
  change rho k p u q (a • basisVector k j) = _
  rw [map_smul, rho_basisVector, Finsupp.smul_single]
  rfl

/-- Multiplication of one-row profile operators. -/
theorem rho_mul_rho (p p' q q' : ℕ) (u u' : Limit k) :
    rho k p u q * rho k p' u' q' =
      rho k p (u' * profileElement k (q + p') * u) q' := by
  apply Finsupp.basisSingleOne.ext
  intro j
  change rho k p u q
      (rho k p' u' q' (basisVector k j)) =
    rho k p (u' * profileElement k (q + p') * u) q'
      (basisVector k j)
  rw [rho_basisVector, rho_single, rho_basisVector]
  congr 1
  simp [mul_assoc]

/-- The profile store is the basic one-row operator. -/
theorem store_eq_rho : store k = rho k 0 1 0 := by
  apply Finsupp.basisSingleOne.ext
  intro j
  change store k (basisVector k j) = rho k 0 1 0 (basisVector k j)
  rw [store_basisVector, rho_basisVector]
  simp

theorem shift_pow_mul_rho (r p q : ℕ) (u : Limit k) :
    (shift k) ^ r * rho k p u q = rho k (p + r) u q := by
  apply Finsupp.basisSingleOne.ext
  intro j
  change ((shift k) ^ r)
      (rho k p u q (basisVector k j)) =
    rho k (p + r) u q (basisVector k j)
  rw [rho_basisVector, shift_pow_single, rho_basisVector]

theorem rho_mul_shift_pow (p q r : ℕ) (u : Limit k) :
    rho k p u q * (shift k) ^ r = rho k p u (q + r) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  change rho k p u q
      (((shift k) ^ r) (basisVector k j)) =
    rho k p u (q + r) (basisVector k j)
  rw [show basisVector k j = Finsupp.single j 1 by rfl,
    shift_pow_single]
  rw [rho_single, rho_single]
  simp [add_left_comm, add_comm]

/-- The span of all one-row profile operators.  This is the locally finite
ideal denoted `J` in the article. -/
def profileIdeal : Submodule k (ProfileEnd k) :=
  Submodule.span k
    (Set.range fun a : ℕ × Limit k × ℕ => rho k a.1 a.2.1 a.2.2)

theorem rho_mem_profileIdeal (p q : ℕ) (u : Limit k) :
    rho k p u q ∈ profileIdeal k :=
  Submodule.subset_span ⟨(p, u, q), rfl⟩

/-- The profile ideal is closed under multiplication. -/
theorem mul_mem_profileIdeal {x y : ProfileEnd k}
    (hx : x ∈ profileIdeal k) (hy : y ∈ profileIdeal k) :
    x * y ∈ profileIdeal k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨p, u, q⟩, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨⟨p', u', q'⟩, rfl⟩ := hy
          rw [rho_mul_rho]
          exact rho_mem_profileIdeal k _ _ _
      | zero => simp
      | add y z _ _ hy hz => simpa [mul_add] using add_mem hy hz
      | smul r y _ hy =>
          rw [mul_smul_comm]
          exact (profileIdeal k).smul_mem r hy
  | zero => simp
  | add x z _ _ hx hz => simpa [add_mul] using add_mem hx hz
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact (profileIdeal k).smul_mem r hx

theorem shift_pow_mul_mem_profileIdeal (r : ℕ) {x : ProfileEnd k}
    (hx : x ∈ profileIdeal k) :
    (shift k) ^ r * x ∈ profileIdeal k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨p, u, q⟩, rfl⟩ := hx
      rw [shift_pow_mul_rho]
      exact rho_mem_profileIdeal k _ _ _
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using add_mem hx hy
  | smul a x _ hx =>
      rw [mul_smul_comm]
      exact (profileIdeal k).smul_mem a hx

theorem mul_shift_pow_mem_profileIdeal (r : ℕ) {x : ProfileEnd k}
    (hx : x ∈ profileIdeal k) :
    x * (shift k) ^ r ∈ profileIdeal k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨p, u, q⟩, rfl⟩ := hx
      rw [rho_mul_shift_pow]
      exact rho_mem_profileIdeal k _ _ _
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using add_mem hx hy
  | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact (profileIdeal k).smul_mem a hx

theorem store_mem_profileIdeal : store k ∈ profileIdeal k := by
  rw [store_eq_rho]
  exact rho_mem_profileIdeal k _ _ _

/-- Dependence of a one-row operator on its coefficient. -/
def rhoLinear (p q : ℕ) : Limit k →ₗ[k] ProfileEnd k where
  toFun u := rho k p u q
  map_add' u v := by
    apply Finsupp.basisSingleOne.ext
    intro j
    change rho k p (u + v) q (basisVector k j) =
      (rho k p u q + rho k p v q) (basisVector k j)
    simp [rho_basisVector, mul_add]
  map_smul' r u := by
    apply Finsupp.basisSingleOne.ext
    intro j
    change rho k p (r • u) q (basisVector k j) =
      (r • rho k p u q) (basisVector k j)
    simp [rho_basisVector]

/-- Operators with rows in `P`, tails in `Q`, and coefficients in `U`. -/
def boundedRhoSpace (P Q : Finset ℕ) (U : Submodule k (Limit k)) :
    Submodule k (ProfileEnd k) :=
  P.sup fun p => Q.sup fun q => Submodule.map (rhoLinear k p q) U

theorem rho_mem_boundedRhoSpace {P Q : Finset ℕ}
    {U : Submodule k (Limit k)} {p q : ℕ} {u : Limit k}
    (hp : p ∈ P) (hq : q ∈ Q) (hu : u ∈ U) :
    rho k p u q ∈ boundedRhoSpace k P Q U := by
  apply (show Submodule.map (rhoLinear k p q) U ≤
      boundedRhoSpace k P Q U by
    exact (Finset.le_sup (s := Q)
      (f := fun q => Submodule.map (rhoLinear k p q) U) hq).trans
      (Finset.le_sup (s := P)
        (f := fun p => Q.sup fun q =>
          Submodule.map (rhoLinear k p q) U) hp))
  exact ⟨u, hu, rfl⟩

theorem boundedRhoSpace_mono {P Q : Finset ℕ}
    {U U' : Submodule k (Limit k)} (hUU' : U ≤ U') :
    boundedRhoSpace k P Q U ≤ boundedRhoSpace k P Q U' := by
  apply Finset.sup_mono_fun
  intro p hp
  apply Finset.sup_mono_fun
  intro q hq
  exact Submodule.map_mono hUU'

theorem boundedRhoSpace_eq_span (P Q : Finset ℕ)
    (U : Submodule k (Limit k)) :
    boundedRhoSpace k P Q U =
      Submodule.span k {x | ∃ p ∈ P, ∃ q ∈ Q, ∃ u ∈ U,
        rho k p u q = x} := by
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    apply Finset.sup_le
    intro q hq
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨p, hp, q, hq, u, hu, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨p, hp, q, hq, u, hu, rfl⟩
    exact rho_mem_boundedRhoSpace k hp hq hu

/-- Every operator in a bounded rho space has zero output outside its
finite set of permitted rows. -/
theorem boundedRhoSpace_apply_eq_zero_of_not_mem
    {P Q : Finset ℕ} {U : Submodule k (Limit k)}
    {f : ProfileEnd k} (hf : f ∈ boundedRhoSpace k P Q U)
    {r : ℕ} (hr : r ∉ P) (v : ProfileModule k) : f v r = 0 := by
  rw [boundedRhoSpace_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, q, _hq, u, _hu, rfl⟩ := hf
      have hpr : p ≠ r := fun h => hr (h ▸ hp)
      induction v using Finsupp.induction with
      | zero => simp
      | single_add j a v hj ha ih =>
          rw [map_add, Finsupp.add_apply, rho_single, ih]
          simp [hpr]
  | zero => simp
  | add f g _ _ hf hg => simp [hf, hg]
  | smul a f _ hf => simp [hf]

/-- A bounded rho space is multiplicatively closed when its coefficient
space is a subalgebra containing all connecting profile entries. -/
theorem mul_mem_boundedRhoSpace
    (P Q : Finset ℕ) (U : Subalgebra k (Limit k))
    (hprofile : ∀ q ∈ Q, ∀ p ∈ P,
      profileElement k (q + p) ∈ U)
    {x y : ProfileEnd k}
    (hx : x ∈ boundedRhoSpace k P Q U.toSubmodule)
    (hy : y ∈ boundedRhoSpace k P Q U.toSubmodule) :
    x * y ∈ boundedRhoSpace k P Q U.toSubmodule := by
  rw [boundedRhoSpace_eq_span] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, hp, q, hq, u, hu, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨p', hp', q', hq', u', hu', rfl⟩ := hy
          rw [rho_mul_rho]
          apply Submodule.subset_span
          exact ⟨p, hp, q', hq',
            u' * profileElement k (q + p') * u,
            U.mul_mem (U.mul_mem hu' (hprofile q hq p' hp')) hu, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => simpa [mul_add] using add_mem hy hz
      | smul r y _ hy =>
          rw [mul_smul_comm]
          exact (Submodule.span k _).smul_mem r hy
  | zero => simp
  | add x z _ _ hx hz => simpa [add_mul] using add_mem hx hz
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact (Submodule.span k _).smul_mem r hx

instance moduleFinite_boundedRhoSpace
    (P Q : Finset ℕ) (U : Submodule k (Limit k))
    [FiniteDimensional k U] :
    Module.Finite k (boundedRhoSpace k P Q U) := by
  classical
  have finite_sup (A B : Submodule k (ProfileEnd k))
      [Module.Finite k A] [Module.Finite k B] :
      Module.Finite k (A ⊔ B : Submodule k (ProfileEnd k)) :=
    Module.Finite.of_fg
      (((Submodule.fg_top A).mp Module.Finite.fg_top).sup
        ((Submodule.fg_top B).mp Module.Finite.fg_top))
  have hQ (p : ℕ) : Module.Finite k
      (Q.sup fun q => Submodule.map (rhoLinear k p q) U :
        Submodule k (ProfileEnd k)) := by
    induction Q using Finset.induction_on with
    | empty =>
        change Module.Finite k (⊥ : Submodule k (ProfileEnd k))
        exact Module.Finite.bot k _
    | @insert q Q hq ih =>
        rw [Finset.sup_insert]
        exact finite_sup _ _
  unfold boundedRhoSpace
  induction P using Finset.induction_on with
  | empty =>
      change Module.Finite k (⊥ : Submodule k (ProfileEnd k))
      exact Module.Finite.bot k _
  | @insert p P hp ih =>
      rw [Finset.sup_insert]
      let _ := hQ p
      exact finite_sup _ _

/-- A finite-dimensional subspace of the profile ideal uses only finitely
many rows, tails, and coefficients. -/
theorem exists_boundedRhoSpace_of_le_profileIdeal
    (P : Submodule k (ProfileEnd k)) [Module.Finite k P]
    (hP : P ≤ profileIdeal k) :
    ∃ Ps Qs : Finset ℕ, ∃ Us : Finset (Limit k),
      P ≤ boundedRhoSpace k Ps Qs (Submodule.span k (Us : Set (Limit k))) := by
  classical
  have hfg : P.FG := (Submodule.fg_top P).mp Module.Finite.fg_top
  obtain ⟨S, hS⟩ := hfg
  have he (x : S) : (x : ProfileEnd k) ∈ profileIdeal k := by
    apply hP
    rw [← hS]
    exact Submodule.subset_span x.property
  have hcExists (x : S) :
      ∃ c : (ℕ × Limit k × ℕ) →₀ k,
        c.sum (fun a r => r • rho k a.1 a.2.1 a.2.2) =
          (x : ProfileEnd k) := by
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (he x)
  choose c hc using hcExists
  let T : Finset (ℕ × Limit k × ℕ) :=
    S.attach.biUnion fun x => (c x).support
  let Ps : Finset ℕ := T.image fun a => a.1
  let Qs : Finset ℕ := T.image fun a => a.2.2
  let Us : Finset (Limit k) := T.image fun a => a.2.1
  refine ⟨Ps, Qs, Us, ?_⟩
  rw [← hS]
  apply Submodule.span_le.2
  intro x hx
  let xS : S := ⟨x, hx⟩
  change (xS : ProfileEnd k) ∈ _
  rw [← hc xS]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  apply rho_mem_boundedRhoSpace k
  · exact Finset.mem_image.2 ⟨a, Finset.mem_biUnion.2
      ⟨xS, Finset.mem_attach _ _, ha⟩, rfl⟩
  · exact Finset.mem_image.2 ⟨a, Finset.mem_biUnion.2
      ⟨xS, Finset.mem_attach _ _, ha⟩, rfl⟩
  · exact Submodule.subset_span (Finset.mem_coe.2
      (Finset.mem_image.2 ⟨a, Finset.mem_biUnion.2
        ⟨xS, Finset.mem_attach _ _, ha⟩, rfl⟩))

/-- The unilateral shift is not in the profile ideal. -/
theorem shift_not_mem_profileIdeal : shift k ∉ profileIdeal k := by
  intro hshift
  let P : Submodule k (ProfileEnd k) := k ∙ shift k
  let _ : Module.Finite k P := Module.Finite.span_singleton k (shift k)
  obtain ⟨Ps, Qs, Us, hbounded⟩ :=
    exists_boundedRhoSpace_of_le_profileIdeal k P (by
      rw [Submodule.span_le]
      simpa [P] using hshift)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range Ps
  have hrow : N + 1 ∉ Ps := by
    intro hmem
    have := Finset.mem_range.mp (hN hmem)
    omega
  have hz := boundedRhoSpace_apply_eq_zero_of_not_mem k
    (hbounded (Submodule.mem_span_singleton_self (R := k) (shift k)))
    hrow (basisVector k N)
  rw [shift_basisVector] at hz
  have : (1 : Limit k) = 0 := by simpa [basisVector] using hz
  have hone : (1 : Limit k) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : Limit k => z) h
    have : (1 : Stage k 0) = 0 := by
      apply ofStage_injective k 0
      simpa using h'
    let i : Fin (stageDimension 0) := ⟨0, by simp [stageDimension]⟩
    have hii := congrFun (congrFun this i) i
    simp [i] at hii
  exact hone this

/-- Every finite-dimensional subspace of the profile ideal is contained in
a finite-dimensional multiplicatively closed subspace.  This is the local
finiteness statement needed for the Lie kernel. -/
theorem exists_finite_mulClosed_of_le_profileIdeal
    (P : Submodule k (ProfileEnd k)) [Module.Finite k P]
    (hP : P ≤ profileIdeal k) :
    ∃ W : Submodule k (ProfileEnd k),
      P ≤ W ∧ Module.Finite k W ∧
        ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W := by
  classical
  obtain ⟨Ps, Qs, Us, hbounded⟩ :=
    exists_boundedRhoSpace_of_le_profileIdeal k P hP
  let connectors : Finset (Limit k) :=
    (Qs.product Ps).image fun qp => profileElement k (qp.1 + qp.2)
  let coefficients : Finset (Limit k) := Us ∪ connectors
  obtain ⟨n, hn⟩ := exists_stageAlgebra_of_finset k coefficients
  let U : Subalgebra k (Limit k) := stageAlgebra k n
  have hUs : Submodule.span k (Us : Set (Limit k)) ≤ U.toSubmodule := by
    apply Submodule.span_le.2
    intro u hu
    apply hn u
    exact Finset.mem_union_left connectors (Finset.mem_coe.1 hu)
  have hprofile : ∀ q ∈ Qs, ∀ p ∈ Ps,
      profileElement k (q + p) ∈ U := by
    intro q hq p hp
    apply hn
    apply Finset.mem_union_right Us
    exact Finset.mem_image.2 ⟨(q, p), Finset.mem_product.2 ⟨hq, hp⟩, rfl⟩
  let W := boundedRhoSpace k Ps Qs U.toSubmodule
  refine ⟨W, hbounded.trans (boundedRhoSpace_mono k hUs), ?_, ?_⟩
  · let _ : Module.Finite k U := inferInstance
    exact moduleFinite_boundedRhoSpace k Ps Qs U.toSubmodule
  · intro x hx y hy
    exact mul_mem_boundedRhoSpace k Ps Qs U hprofile hx hy

end

end HopfAmenability.ShiftProfileAlgebra
