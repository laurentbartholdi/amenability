/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.SplitDual
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Existence of split dual filtrations
-/

open Module

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {R : Type v}
variable [Field k] [CommRing R] [Algebra k R]

/--
A finite-dimensional commutative algebra has a split dual filtration when
every simple subquotient of its regular module has `k`-dimension one.

The hypothesis is stated on covers `A ⋖ B`; by
`covBy_iff_quot_is_simple`, these are exactly the nonzero simple quotients
occurring in a composition series of the regular module.
-/
theorem exists_splitDualFiltration_of_simple_finrank_one
    [FiniteDimensional k R]
    (h : ∀ (A B : Submodule R R) (_hAB : A ≤ B),
      IsSimpleModule R (B ⧸ A.comap B.subtype) →
        finrank k
          ((B.restrictScalars k) ⧸
            (A.restrictScalars k).comap (B.restrictScalars k).subtype) = 1) :
    Nonempty (SplitDualFiltration k R) := by
  let _ : IsNoetherian R R := isNoetherian_of_tower k inferInstance
  let _ : IsArtinian R R := isArtinian_of_tower k inferInstance
  obtain ⟨s, hsbot, hstop⟩ :=
    exists_compositionSeries_of_isNoetherian_isArtinian R R
  let filtration : Fin (s.length + 1) → Submodule k R := fun j =>
    (s j).restrictScalars k
  let lower : ∀ i : Fin s.length, Submodule k (filtration i.succ) := fun i =>
    (filtration i.castSucc).comap (filtration i.succ).subtype
  let layer : Fin s.length → Type v := fun i => filtration i.succ ⧸ lower i
  let layerEquiv : ∀ i : Fin s.length, layer i ≃ₗ[k] k := fun i =>
    LinearEquiv.ofFinrankEq (layer i) k (by
      have hsimple : IsSimpleModule R
          (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) :=
        (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
      simpa [layer, lower, filtration] using
        h (s i.castSucc) (s i.succ) (s.step i).le hsimple)
  let coeff : ∀ i : Fin s.length, filtration i.succ →ₗ[k] k := fun i =>
    (layerEquiv i).toLinearMap.comp (lower i).mkQ
  have coeff_surjective : ∀ i : Fin s.length, Function.Surjective (coeff i) := by
    intro i y
    obtain ⟨q, rfl⟩ := (layerEquiv i).surjective y
    obtain ⟨x, rfl⟩ := (lower i).mkQ_surjective q
    exact ⟨x, rfl⟩
  have coeff_ker : ∀ i : Fin s.length,
      LinearMap.ker (coeff i) = lower i := by
    intro i
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      change layerEquiv i ((lower i).mkQ x) = 0 at hx
      have hq : (lower i).mkQ x = 0 :=
        (layerEquiv i).injective (hx.trans (layerEquiv i).map_zero.symm)
      rw [← (lower i).ker_mkQ, LinearMap.mem_ker]
      exact hq
    · intro hx
      rw [LinearMap.mem_ker]
      have hq : (lower i).mkQ x = 0 := by
        rw [← LinearMap.mem_ker, (lower i).ker_mkQ]
        exact hx
      simp [coeff, hq]
  have filtration_ideal : ∀ j : Fin (s.length + 1),
      IsIdealSubspace (filtration j) := by
    intro j r x hx
    change x ∈ s j at hx
    change r * x ∈ s j
    simpa [smul_eq_mul] using (s j).smul_mem r hx
  have action_of : ∀ (i : Fin s.length) (x0 : filtration i.succ),
      coeff i x0 = 1 → ∀ (r : R) (x : filtration i.succ),
        coeff i ⟨r * (x : R), filtration_ideal i.succ r x.2⟩ =
          coeff i ⟨r * (x0 : R), filtration_ideal i.succ r x0.2⟩ *
            coeff i x := by
    intro i x0 hx0 r x
    have hxker : x - (coeff i x) • x0 ∈ LinearMap.ker (coeff i) := by
      rw [LinearMap.mem_ker]
      simp [hx0]
    rw [coeff_ker i] at hxker
    have hrker := filtration_ideal i.castSucc r hxker
    let y : filtration i.succ :=
      ⟨r * ((x - (coeff i x) • x0 : filtration i.succ) : R),
        filtration_ideal i.succ r
          (x - (coeff i x) • x0 : filtration i.succ).2⟩
    have hyLower : y ∈ lower i := hrker
    have hyzero : coeff i y = 0 := by
      rw [← LinearMap.mem_ker, coeff_ker i]
      exact hyLower
    let rx : filtration i.succ :=
      ⟨r * (x : R), filtration_ideal i.succ r x.2⟩
    let rx0 : filtration i.succ :=
      ⟨r * (x0 : R), filtration_ideal i.succ r x0.2⟩
    have hy : y = rx - (coeff i x) • rx0 := by
      apply Subtype.ext
      simp [y, rx, rx0, Algebra.smul_def]
      ring
    rw [hy, map_sub, map_smul] at hyzero
    change coeff i rx = coeff i rx0 * coeff i x
    rw [mul_comm]
    exact sub_eq_zero.mp hyzero
  let character : Fin s.length → R →ₐ[k] k := fun i => by
    let x0 : filtration i.succ := Classical.choose (coeff_surjective i 1)
    have hx0 : coeff i x0 = 1 := Classical.choose_spec (coeff_surjective i 1)
    let act : R → filtration i.succ := fun r =>
      ⟨r * (x0 : R), filtration_ideal i.succ r x0.2⟩
    have act_one : act 1 = x0 := by ext; simp [act]
    have act_zero : act 0 = 0 := by ext; simp [act]
    have act_add : ∀ r q, act (r + q) = act r + act q := by
      intro r q
      ext
      simp [act, add_mul]
    have act_mul : ∀ r q, act (r * q) =
        ⟨r * (act q : R), filtration_ideal i.succ r (act q).2⟩ := by
      intro r q
      ext
      simp [act, mul_assoc]
    have act_algebraMap : ∀ a : k, act (algebraMap k R a) = a • x0 := by
      intro a
      ext
      simp [act, Algebra.smul_def]
    let χ : R → k := fun r => coeff i (act r)
    exact {
      toFun := χ
      map_one' := by
        rw [show χ 1 = coeff i (act 1) from rfl, act_one, hx0]
      map_mul' := by
        intro r q
        rw [show χ (r * q) = coeff i (act (r * q)) from rfl, act_mul]
        exact action_of i x0 hx0 r (act q)
      map_zero' := by rw [show χ 0 = coeff i (act 0) from rfl, act_zero]; simp
      map_add' := by
        intro r q
        rw [show χ (r + q) = coeff i (act (r + q)) from rfl, act_add]
        simp [χ]
      commutes' := by
        intro a
        rw [show χ (algebraMap k R a) =
          coeff i (act (algebraMap k R a)) from rfl, act_algebraMap]
        simp [hx0]
    }
  have coeff_mul : ∀ (i : Fin s.length) (r : R) (x : filtration i.succ),
      coeff i ⟨r * (x : R), filtration_ideal i.succ r x.2⟩ =
        character i r * coeff i x := by
    intro i r x
    let x0 : filtration i.succ := Classical.choose (coeff_surjective i 1)
    have hx0 : coeff i x0 = 1 := Classical.choose_spec (coeff_surjective i 1)
    have hchar : character i r = coeff i
        ⟨r * (x0 : R), filtration_ideal i.succ r x0.2⟩ := by
      rfl
    rw [hchar]
    exact action_of i x0 hx0 r x
  exact ⟨{
    n := s.length
    filtration := filtration
    bot := by
      change (s.head).restrictScalars k = ⊥
      rw [hsbot]
      rfl
    top := by
      change (s.last).restrictScalars k = ⊤
      rw [hstop]
      rfl
    monotone := fun i => Submodule.restrictScalars_mono k (s.step i).le
    ideal := filtration_ideal
    character := character
    coeff := coeff
    coeff_surjective := coeff_surjective
    coeff_ker := coeff_ker
    coeff_mul := coeff_mul
  }⟩

end

end HopfAmenability
