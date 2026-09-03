/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Bases adapted to an exhaustive ascending filtration

This file constructs the linear-algebra input for the filtered PBW argument:
an exhaustive ascending filtration of a vector space is the internal direct
sum of chosen complements of consecutive filtration terms.  Collecting bases
of those complements gives a basis whose degree-`n` vectors span precisely the
`n`th filtration term.
-/

namespace HopfAmenability

noncomputable section

open Module

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The preceding term of an ascending filtration, viewed inside its current
term.  In degree zero it is the zero submodule. -/
def ascendingPrevious (W : ℕ → Submodule k V) :
    (n : ℕ) → Submodule k (W n)
  | 0 => ⊥
  | n + 1 => (W n).comap (W (n + 1)).subtype

/-- A chosen complement of the preceding filtration term. -/
def ascendingLayerComplement (W : ℕ → Submodule k V) (n : ℕ) :
    Submodule k (W n) :=
  Classical.choose (ascendingPrevious (k := k) W n).exists_isCompl

theorem ascendingLayerComplement_isCompl (W : ℕ → Submodule k V)
    (n : ℕ) :
    IsCompl (ascendingPrevious (k := k) W n)
      (ascendingLayerComplement (k := k) W n) :=
  Classical.choose_spec (ascendingPrevious (k := k) W n).exists_isCompl

/-- The degree-`n` complement, included in the ambient vector space. -/
def ascendingLayer (W : ℕ → Submodule k V) (n : ℕ) :
    Submodule k V :=
  (ascendingLayerComplement (k := k) W n).map (W n).subtype

theorem ascendingLayer_le (W : ℕ → Submodule k V) (n : ℕ) :
    ascendingLayer (k := k) W n ≤ W n := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.2

@[simp]
theorem ascendingLayer_zero (W : ℕ → Submodule k V) :
    ascendingLayer (k := k) W 0 = W 0 := by
  rw [ascendingLayer]
  have htop : ascendingLayerComplement (k := k) W 0 = ⊤ := by
    simpa [ascendingPrevious] using
      (ascendingLayerComplement_isCompl (k := k) W 0).codisjoint.eq_top
  rw [htop, Submodule.map_top]
  exact Submodule.range_subtype _

theorem ascending_step_eq_sup (W : ℕ → Submodule k V)
    (hW : Monotone W) (n : ℕ) :
    W (n + 1) = W n ⊔ ascendingLayer (k := k) W (n + 1) := by
  apply le_antisymm
  · intro x hx
    let x' : W (n + 1) := ⟨x, hx⟩
    have hxmem : x' ∈ ascendingPrevious (k := k) W (n + 1) ⊔
        ascendingLayerComplement (k := k) W (n + 1) := by
      rw [(ascendingLayerComplement_isCompl
        (k := k) W (n + 1)).codisjoint.eq_top]
      trivial
    obtain ⟨(a : W (n + 1)), ha, (b : W (n + 1)), hb, hab⟩ :=
      Submodule.mem_sup.mp hxmem
    have haW : (a : V) ∈ W n := ha
    have hbLayer : (b : V) ∈ ascendingLayer (k := k) W (n + 1) :=
      ⟨b, hb, rfl⟩
    have hsum : (a : V) + b = x := congrArg Subtype.val hab
    rw [← hsum]
    exact Submodule.add_mem _ (Submodule.mem_sup_left haW)
      (Submodule.mem_sup_right hbLayer)
  · exact sup_le (hW (Nat.le_succ n))
      (ascendingLayer_le (k := k) W (n + 1))

theorem ascendingLayer_succ_disjoint (W : ℕ → Submodule k V)
    (n : ℕ) :
    Disjoint (ascendingLayer (k := k) W (n + 1)) (W n) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rcases hx.1 with ⟨y, hy, hyx⟩
  subst x
  have hprev := hx.2
  have hyPrev : y ∈ ascendingPrevious (k := k) W (n + 1) := hprev
  have hyzero := (Submodule.disjoint_def.mp
    (ascendingLayerComplement_isCompl (k := k) W (n + 1)).disjoint)
      y hyPrev hy
  simpa using congrArg Subtype.val hyzero

/-- The sum of the layers through degree `n` is the `n`th filtration term. -/
theorem iSup_layers_le_eq (W : ℕ → Submodule k V)
    (hW : Monotone W) (n : ℕ) :
    (⨆ i : Fin (n + 1), ascendingLayer (k := k) W i) = W n := by
  induction n with
  | zero =>
      simp [ascendingLayer_zero]
  | succ n ih =>
      rw [ascending_step_eq_sup (k := k) W hW n, ← ih]
      apply le_antisymm
      · apply iSup_le
        intro i
        by_cases hi : (i : ℕ) = n + 1
        · have hieq : i = ⟨n + 1, by omega⟩ := Fin.ext hi
          rw [hieq]
          exact le_sup_right
        · apply le_sup_left.trans'
          exact le_iSup (fun j : Fin (n + 1) ↦
            ascendingLayer (k := k) W j) ⟨i, by omega⟩
      · apply sup_le
        · apply iSup_le
          intro i
          exact le_iSup (fun j : Fin (n + 2) ↦
            ascendingLayer (k := k) W j) i.castSucc
        · exact le_iSup (fun j : Fin (n + 2) ↦
            ascendingLayer (k := k) W j) ⟨n + 1, by omega⟩

/-- Consecutive complements of an ascending filtration are independent. -/
theorem ascendingLayers_iSupIndep (W : ℕ → Submodule k V)
    (hW : Monotone W) :
    iSupIndep (ascendingLayer (k := k) W) := by
  classical
  rw [iSupIndep_iff_supIndep]
  intro s
  refine Finset.strongInductionOn s ?_
  intro t ih
  by_cases ht : t = ∅
  · subst t
    simp
  let m := t.max' (Finset.nonempty_iff_ne_empty.mpr ht)
  have hm : m ∈ t := Finset.max'_mem t _
  have herase : t.erase m ⊂ t := Finset.erase_ssubset hm
  have hi := ih (t.erase m) herase
  rw [← Finset.insert_erase hm]
  apply hi.insert
  cases hmval : m with
  | zero =>
      have hmax : t.max' (Finset.nonempty_iff_ne_empty.mpr ht) = 0 := by
        simpa [m] using hmval
      have hempty : t.erase 0 = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨j, hj⟩ := hne
        have hjle : j ≤ t.max' (Finset.nonempty_iff_ne_empty.mpr ht) :=
          Finset.le_max' t j (Finset.mem_of_mem_erase hj)
        have : j = 0 := Nat.eq_zero_of_le_zero (hmax ▸ hjle)
        exact (Finset.ne_of_mem_erase hj) this
      simp [hempty]
  | succ n =>
      have hmax : t.max' (Finset.nonempty_iff_ne_empty.mpr ht) = n + 1 := by
        simpa [m] using hmval
      apply (ascendingLayer_succ_disjoint (k := k) W n).mono_right
      apply Finset.sup_le
      intro j hj
      have hjmem : j ∈ t := Finset.mem_of_mem_erase hj
      have hjle : j ≤ t.max' (Finset.nonempty_iff_ne_empty.mpr ht) :=
        Finset.le_max' t j hjmem
      have hjne : j ≠ n + 1 := Finset.ne_of_mem_erase hj
      exact (ascendingLayer_le (k := k) W j).trans
        (hW (by rw [hmax] at hjle; omega))

/-- An exhaustive ascending filtration is the internal direct sum of its
chosen consecutive complements. -/
theorem ascendingLayers_isInternal (W : ℕ → Submodule k V)
    (hW : Monotone W) (hexhaustive : ⨆ n, W n = ⊤) :
    DirectSum.IsInternal (ascendingLayer (k := k) W) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (ascendingLayers_iSupIndep (k := k) W hW)
  apply top_unique
  rw [← hexhaustive]
  apply iSup_le
  intro n
  rw [← iSup_layers_le_eq (k := k) W hW n]
  apply iSup_le
  intro i
  exact le_iSup (ascendingLayer (k := k) W) i

/-- A basis adapted to an exhaustive ascending filtration.  Its index records
the filtration degree of each basis vector. -/
def ascendingFiltrationBasis (W : ℕ → Submodule k V)
    (hW : Monotone W) (hexhaustive : ⨆ n, W n = ⊤) :
    Basis (Σ n, Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W n)) k V :=
  (ascendingLayers_isInternal (k := k) W hW hexhaustive).collectedBasis
    (fun n ↦ Basis.ofVectorSpace k (ascendingLayer (k := k) W n))

@[simp]
theorem ascendingFiltrationBasis_apply
    (W : ℕ → Submodule k V) (hW : Monotone W)
    (hexhaustive : ⨆ n, W n = ⊤)
    (i : Σ n, Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W n)) :
    ascendingFiltrationBasis (k := k) W hW hexhaustive i = i.2.1 := by
  rw [ascendingFiltrationBasis,
    DirectSum.IsInternal.collectedBasis_coe]
  exact congrArg Subtype.val
    (Module.Basis.ofVectorSpace_apply_self k
      (ascendingLayer (k := k) W i.1) i.2)

theorem ascendingFiltrationBasis_mem
    (W : ℕ → Submodule k V) (hW : Monotone W)
    (hexhaustive : ⨆ n, W n = ⊤)
    (i : Σ n, Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W n)) :
    ascendingFiltrationBasis (k := k) W hW hexhaustive i ∈ W i.1 := by
  rw [ascendingFiltrationBasis_apply]
  exact (ascendingLayer_le (k := k) W i.1) i.2.1.2

/-- Indices of the adapted basis whose filtration degree is at most `n`. -/
def ascendingBasisBelow (W : ℕ → Submodule k V) (n : ℕ) :
    Set (Σ r, Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W r)) :=
  {i | i.1 ≤ n}

theorem ascendingLayer_le_span_basisBelow
    (W : ℕ → Submodule k V) (hW : Monotone W)
    (hexhaustive : ⨆ n, W n = ⊤) {r n : ℕ} (hrn : r ≤ n) :
    ascendingLayer (k := k) W r ≤
      Submodule.span k
        (ascendingFiltrationBasis (k := k) W hW hexhaustive ''
          ascendingBasisBelow (k := k) W n) := by
  let h := ascendingLayers_isInternal (k := k) W hW hexhaustive
  let v := fun r ↦ Basis.ofVectorSpace k (ascendingLayer (k := k) W r)
  let b := ascendingFiltrationBasis (k := k) W hW hexhaustive
  intro x hx
  change x ∈ Submodule.span k (b '' ascendingBasisBelow (k := k) W n)
  rw [show b = h.collectedBasis v from rfl]
  apply (h.collectedBasis v).mem_span_image.mpr
  intro i hi
  change i.1 ≤ n
  by_contra hir
  have hcoeff := h.collectedBasis_repr_of_mem_ne v
    (i := r) (j := i.1) (a := i.2) (show r ≠ i.1 by omega) hx
  exact (Finsupp.mem_support_iff.mp hi) (by simpa using hcoeff)

/-- The degree-at-most-`n` vectors of the adapted basis span exactly the
`n`th filtration term. -/
theorem span_ascendingBasisBelow_eq
    (W : ℕ → Submodule k V) (hW : Monotone W)
    (hexhaustive : ⨆ n, W n = ⊤) (n : ℕ) :
    Submodule.span k
        (ascendingFiltrationBasis (k := k) W hW hexhaustive ''
          ascendingBasisBelow (k := k) W n) = W n := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨i, hi, rfl⟩
    exact (ascendingFiltrationBasis_mem (k := k) W hW hexhaustive i) |>
      hW hi
  · rw [← iSup_layers_le_eq (k := k) W hW n]
    apply iSup_le
    intro i
    exact ascendingLayer_le_span_basisBelow (k := k) W hW hexhaustive
      (Nat.lt_succ_iff.mp i.isLt)

/-- The index type of the basis adapted to `W`. -/
abbrev AscendingBasisIndex (W : ℕ → Submodule k V) :=
  Σ r, Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W r)

/-- Adapted-basis indices of degree at most `n`. -/
abbrev AscendingBasisBelowIndex (W : ℕ → Submodule k V) (n : ℕ) :=
  {i : AscendingBasisIndex (k := k) W // i.1 ≤ n}

theorem finiteDimensional_ascendingLayer
    (W : ℕ → Submodule k V) (n : ℕ)
    [FiniteDimensional k (W n)] :
    FiniteDimensional k (ascendingLayer (k := k) W n) := by
  exact FiniteDimensional.of_injective
    ((ascendingLayer (k := k) W n).subtype.codRestrict
      (W n) (fun x ↦ (ascendingLayer_le (k := k) W n) x.2))
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : W n ↦ (z : V)) h)

/-- Bounded-degree indices are a finite sigma type. -/
def ascendingBasisBelowEquiv
    (W : ℕ → Submodule k V) (n : ℕ) :
    AscendingBasisBelowIndex (k := k) W n ≃
      Σ r : Fin (n + 1),
        Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W r) where
  toFun i := ⟨⟨i.1.1, Nat.lt_succ_iff.mpr i.2⟩, i.1.2⟩
  invFun i := ⟨⟨i.1, i.2⟩, Nat.lt_succ_iff.mp i.1.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible]
noncomputable def fintypeAscendingBasisBelowIndex
    (W : ℕ → Submodule k V) (n : ℕ)
    (hfinite : ∀ r, FiniteDimensional k (W r)) :
    Fintype (AscendingBasisBelowIndex (k := k) W n) := by
  letI (r : ℕ) : FiniteDimensional k (ascendingLayer (k := k) W r) :=
    let _ := hfinite r
    finiteDimensional_ascendingLayer (k := k) W r
  exact Fintype.ofEquiv
    (Σ r : Fin (n + 1),
      Basis.ofVectorSpaceIndex k (ascendingLayer (k := k) W r))
    (ascendingBasisBelowEquiv (k := k) W n).symm

/-- The dimensions of the consecutive complements telescope to the dimension
of the filtration term. -/
theorem sum_finrank_ascendingLayer
    (W : ℕ → Submodule k V) (hW : Monotone W) (n : ℕ)
    (hfinite : ∀ r, FiniteDimensional k (W r)) :
    ∑ r : Fin (n + 1), Module.finrank k (ascendingLayer (k := k) W r) =
      Module.finrank k (W n) := by
  let _ (r : ℕ) := hfinite r
  let _ (r : ℕ) : FiniteDimensional k (ascendingLayer (k := k) W r) :=
    finiteDimensional_ascendingLayer (k := k) W r
  induction n with
  | zero =>
      rw [Fin.sum_univ_one]
      exact LinearEquiv.finrank_eq
        (LinearEquiv.ofEq _ _ (ascendingLayer_zero (k := k) W))
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      change (∑ r : Fin (n + 1),
        Module.finrank k (ascendingLayer (k := k) W r)) +
          Module.finrank k (ascendingLayer (k := k) W (n + 1)) = _
      rw [ih]
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (W n) (ascendingLayer (k := k) W (n + 1))
      have hinf : W n ⊓ ascendingLayer (k := k) W (n + 1) = ⊥ :=
        (ascendingLayer_succ_disjoint (k := k) W n).symm.eq_bot
      rw [hinf, finrank_bot, add_zero,
        ← ascending_step_eq_sup (k := k) W hW n] at hdim
      omega

set_option linter.style.haveILetI false in
-- The statement fixes the same chosen finite instance used to count the basis.
/-- The bounded-degree adapted basis has cardinality equal to the dimension
of the corresponding filtration term. -/
theorem card_ascendingBasisBelowIndex
    (W : ℕ → Submodule k V) (hW : Monotone W)
    (n : ℕ) (hfinite : ∀ r, FiniteDimensional k (W r)) :
    @Fintype.card (AscendingBasisBelowIndex (k := k) W n)
        (fintypeAscendingBasisBelowIndex (k := k) W n hfinite) =
      Module.finrank k (W n) := by
  letI : Fintype (AscendingBasisBelowIndex (k := k) W n) :=
    fintypeAscendingBasisBelowIndex (k := k) W n hfinite
  let _ (r : ℕ) := hfinite r
  let _ (r : ℕ) : FiniteDimensional k (ascendingLayer (k := k) W r) :=
    finiteDimensional_ascendingLayer (k := k) W r
  rw [Fintype.card_congr (ascendingBasisBelowEquiv (k := k) W n),
    Fintype.card_sigma]
  simp_rw [← Module.finrank_eq_card_basis
    (Basis.ofVectorSpace k (ascendingLayer (k := k) W _))]
  exact sum_finrank_ascendingLayer (k := k) W hW n hfinite

end

end HopfAmenability
