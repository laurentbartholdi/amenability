/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.LieGrowth
import Amenability.ElementaryLieAlgebra
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # The Witt Lie algebra and its growth -/

namespace HopfAmenability
noncomputable section
universe u
variable (k : Type u) [Field k]

/-- The Witt vector space, with basis indexed by the integers. -/
abbrev WittAlgebra := ℤ →₀ k

/-- The standard basis vector `e i` of the Witt algebra. -/
def wittBasisVector (i : ℤ) : WittAlgebra k :=
  Finsupp.single i 1

/-- Bracket with a fixed standard basis vector. -/
def wittBracketRow (i : ℤ) : WittAlgebra k →ₗ[k] WittAlgebra k :=
  Finsupp.linearCombination k fun j : ℤ =>
    ((j - i : ℤ) : k) • wittBasisVector k (i + j)

/-- The bilinear Witt bracket. -/
def wittBracketBilinear :
    WittAlgebra k →ₗ[k] WittAlgebra k →ₗ[k] WittAlgebra k :=
  Finsupp.linearCombination k (wittBracketRow k)

instance : Bracket (WittAlgebra k) (WittAlgebra k) where
  bracket x y := wittBracketBilinear k x y

@[simp]
theorem witt_bracket_eq (x y : WittAlgebra k) :
    ⁅x, y⁆ = wittBracketBilinear k x y :=
  rfl

@[simp]
theorem witt_bracket_basis (i j : ℤ) :
    ⁅wittBasisVector k i, wittBasisVector k j⁆ =
      ((j - i : ℤ) : k) • wittBasisVector k (i + j) := by
  simp [wittBasisVector, wittBracketBilinear, wittBracketRow]

theorem witt_add_lie (x y z : WittAlgebra k) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  change wittBracketBilinear k (x + y) z =
    wittBracketBilinear k x z + wittBracketBilinear k y z
  rw [map_add, LinearMap.add_apply]

theorem witt_lie_add (x y z : WittAlgebra k) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  exact LinearMap.map_add (wittBracketBilinear k x) y z

theorem witt_smul_lie (r : k) (x y : WittAlgebra k) :
    ⁅r • x, y⁆ = r • ⁅x, y⁆ := by
  change wittBracketBilinear k (r • x) y =
    r • wittBracketBilinear k x y
  rw [map_smul, LinearMap.smul_apply]

theorem witt_lie_smul (r : k) (x y : WittAlgebra k) :
    ⁅x, r • y⁆ = r • ⁅x, y⁆ := by
  exact LinearMap.map_smul (wittBracketBilinear k x) r y

theorem witt_bracket_basis_skew (i j : ℤ) :
    ⁅wittBasisVector k i, wittBasisVector k j⁆ =
      -⁅wittBasisVector k j, wittBasisVector k i⁆ := by
  rw [witt_bracket_basis, witt_bracket_basis, add_comm]
  have hcoeff : ((j - i : ℤ) : k) = -((i - j : ℤ) : k) := by
    push_cast
    ring
  rw [hcoeff, neg_smul]

theorem witt_lie_skew (x y : WittAlgebra k) : ⁅x, y⁆ = -⁅y, x⁆ := by
  induction x using Finsupp.induction_linear generalizing y with
  | zero =>
      change wittBracketBilinear k 0 y = -wittBracketBilinear k y 0
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [witt_add_lie, witt_lie_add, hx₁, hx₂]
      abel
  | single i r =>
      induction y using Finsupp.induction_linear with
      | zero =>
          change wittBracketBilinear k (Finsupp.single i r) 0 =
            -wittBracketBilinear k 0 (Finsupp.single i r)
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [witt_lie_add, witt_add_lie, hy₁, hy₂]
          abel
      | single j s =>
          rw [show Finsupp.single i r = r • wittBasisVector k i by
            simp [wittBasisVector],
            show Finsupp.single j s = s • wittBasisVector k j by
              simp [wittBasisVector],
            witt_smul_lie, witt_lie_smul, witt_smul_lie,
            witt_lie_smul, witt_bracket_basis_skew]
          module

theorem witt_lie_self (x : WittAlgebra k) : ⁅x, x⁆ = 0 := by
  induction x using Finsupp.induction_linear with
  | zero =>
      change wittBracketBilinear k 0 0 = 0
      simp
  | add x y hx hy =>
      rw [witt_add_lie, witt_lie_add, witt_lie_add, hx, hy,
        witt_lie_skew (k := k) x y]
      abel
  | single i r =>
      rw [show Finsupp.single i r = r • wittBasisVector k i by
        simp [wittBasisVector], witt_smul_lie, witt_lie_smul,
        witt_bracket_basis]
      simp

theorem witt_leibniz_basis (i j l : ℤ) :
    ⁅wittBasisVector k i,
        ⁅wittBasisVector k j, wittBasisVector k l⁆⁆ =
      ⁅⁅wittBasisVector k i, wittBasisVector k j⁆,
          wittBasisVector k l⁆ +
        ⁅wittBasisVector k j,
          ⁅wittBasisVector k i, wittBasisVector k l⁆⁆ := by
  rw [witt_bracket_basis, witt_lie_smul, witt_bracket_basis,
    witt_bracket_basis, witt_smul_lie, witt_bracket_basis,
    witt_bracket_basis, witt_lie_smul, witt_bracket_basis]
  simp only [smul_smul]
  rw [show i + (j + l) = i + j + l by abel,
    show i + j + l = i + j + l by rfl,
    show j + (i + l) = i + j + l by abel]
  rw [← add_smul]
  apply congrArg (fun r : k => r • wittBasisVector k (i + j + l))
  push_cast
  ring

theorem witt_leibniz_lie (x y z : WittAlgebra k) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  induction x using Finsupp.induction_linear generalizing y z with
  | zero =>
      change wittBracketBilinear k 0 (wittBracketBilinear k y z) =
        wittBracketBilinear k (wittBracketBilinear k 0 y) z +
          wittBracketBilinear k y (wittBracketBilinear k 0 z)
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [witt_add_lie, witt_lie_add, hx₁, hx₂]
      abel
  | single i r =>
      rw [show Finsupp.single i r = r • wittBasisVector k i by
        simp [wittBasisVector]]
      induction y using Finsupp.induction_linear generalizing z with
      | zero =>
          change wittBracketBilinear k (r • wittBasisVector k i)
              (wittBracketBilinear k 0 z) =
            wittBracketBilinear k
                (wittBracketBilinear k (r • wittBasisVector k i) 0) z +
              wittBracketBilinear k 0
                (wittBracketBilinear k (r • wittBasisVector k i) z)
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [witt_add_lie, witt_lie_add, hy₁, hy₂]
          abel
      | single j s =>
          rw [show Finsupp.single j s = s • wittBasisVector k j by
            simp [wittBasisVector]]
          induction z using Finsupp.induction_linear with
          | zero =>
              change wittBracketBilinear k (r • wittBasisVector k i)
                  (wittBracketBilinear k (s • wittBasisVector k j) 0) =
                wittBracketBilinear k
                    (wittBracketBilinear k (r • wittBasisVector k i)
                      (s • wittBasisVector k j)) 0 +
                  wittBracketBilinear k (s • wittBasisVector k j)
                    (wittBracketBilinear k (r • wittBasisVector k i) 0)
              simp
          | add z₁ z₂ hz₁ hz₂ =>
              simp only [witt_lie_add, hz₁, hz₂]
              abel
          | single l t =>
              rw [show Finsupp.single l t = t • wittBasisVector k l by
                simp [wittBasisVector]]
              simp only [witt_smul_lie, witt_lie_smul, smul_smul]
              rw [witt_leibniz_basis (k := k) i j l]
              module

instance : LieRing (WittAlgebra k) where
  bracket x y := wittBracketBilinear k x y
  add_lie := witt_add_lie k
  lie_add := witt_lie_add k
  lie_self := witt_lie_self k
  leibniz_lie := witt_leibniz_lie k

instance : LieAlgebra k (WittAlgebra k) where
  lie_smul := witt_lie_smul k

/-- The standard integer-indexed basis of the Witt algebra. -/
noncomputable def wittBasis : Module.Basis ℤ k (WittAlgebra k) :=
  Finsupp.basisSingleOne

@[simp]
theorem wittBasis_apply (i : ℤ) :
    wittBasis k i = wittBasisVector k i := by
  simp [wittBasis, wittBasisVector]

/-- The Witt algebra is not finite-dimensional. -/
theorem wittAlgebra_not_finiteDimensional :
    ¬ FiniteDimensional k (WittAlgebra k) := by
  intro h
  let _ : FiniteDimensional k (WittAlgebra k) := h
  let _ : Finite ℤ := Module.Finite.finite_basis (wittBasis k)
  exact not_finite ℤ

/-- The four standard generators used for the Witt algebra. -/
def wittGeneratingSet : Set (WittAlgebra k) :=
  {wittBasisVector k (-2), wittBasisVector k (-1),
    wittBasisVector k 1, wittBasisVector k 2}

/-- The four-element generating finset for the Witt algebra. -/
noncomputable def wittGeneratingFinset : Finset (WittAlgebra k) := by
  classical
  exact {wittBasisVector k (-2), wittBasisVector k (-1),
    wittBasisVector k 1, wittBasisVector k 2}

@[simp]
theorem coe_wittGeneratingFinset :
    (wittGeneratingFinset k : Set (WittAlgebra k)) = wittGeneratingSet k := by
  classical
  ext x
  simp [wittGeneratingFinset, wittGeneratingSet]

theorem wittBasisVector_mem_lieSpan_generators [CharZero k] (i : ℤ) :
    wittBasisVector k i ∈
      LieSubalgebra.lieSpan k (WittAlgebra k) (wittGeneratingSet k) := by
  let W := LieSubalgebra.lieSpan k (WittAlgebra k) (wittGeneratingSet k)
  have hm2 : wittBasisVector k (-2) ∈ W := by
    exact LieSubalgebra.subset_lieSpan (by simp [wittGeneratingSet])
  have hm1 : wittBasisVector k (-1) ∈ W := by
    exact LieSubalgebra.subset_lieSpan (by simp [wittGeneratingSet])
  have h1 : wittBasisVector k 1 ∈ W := by
    exact LieSubalgebra.subset_lieSpan (by simp [wittGeneratingSet])
  have h2 : wittBasisVector k 2 ∈ W := by
    exact LieSubalgebra.subset_lieSpan (by simp [wittGeneratingSet])
  have h0 : wittBasisVector k 0 ∈ W := by
    have hbr := W.lie_mem hm1 h1
    rw [witt_bracket_basis] at hbr
    have hs := W.smul_mem (2 : k)⁻¹ hbr
    have htwo : (2 : k) ≠ 0 := by norm_num
    simpa [← mul_smul, htwo] using hs
  refine Int.inductionOn' i 0 h0 ?_ ?_
  · intro n hn ih
    by_cases hn1 : n = 1
    · simpa [hn1] using h2
    · have hcoeff : (((n - 1 : ℤ) : k)) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hn1
      have hbr := W.lie_mem h1 ih
      rw [witt_bracket_basis] at hbr
      have hs := W.smul_mem ((n - 1 : ℤ) : k)⁻¹ hbr
      rw [← mul_smul, inv_mul_cancel₀ hcoeff, one_smul] at hs
      simpa [add_comm] using hs
  · intro n hn ih
    by_cases hnm1 : n = -1
    · simpa [hnm1] using hm2
    · have hcoeff : (((n + 1 : ℤ) : k)) ≠ 0 := by
        have : n + 1 ≠ 0 := by omega
        exact_mod_cast this
      have hbr := W.lie_mem hm1 ih
      rw [witt_bracket_basis] at hbr
      rw [show n - (-1) = n + 1 by omega] at hbr
      have hs := W.smul_mem ((n + 1 : ℤ) : k)⁻¹ hbr
      rw [← mul_smul, inv_mul_cancel₀ hcoeff, one_smul] at hs
      change wittBasisVector k (n - 1) ∈ W
      simpa [sub_eq_add_neg, add_comm] using hs

/-- The standard four elements generate the Witt algebra as a Lie algebra. -/
theorem witt_lieSpan_generators_eq_top [CharZero k] :
    LieSubalgebra.lieSpan k (WittAlgebra k) (wittGeneratingSet k) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | single i r =>
      rw [show Finsupp.single i r = r • wittBasisVector k i by
        simp [wittBasisVector]]
      exact Submodule.smul_mem _ r (wittBasisVector_mem_lieSpan_generators k i)

/-- The Witt algebra is finitely generated in characteristic zero. -/
theorem wittAlgebra_finitelyGenerated [CharZero k] :
    IsFinitelyGeneratedLieAlgebra (k := k) (WittAlgebra k) := by
  refine ⟨wittGeneratingFinset k, ?_⟩
  rw [coe_wittGeneratingFinset, witt_lieSpan_generators_eq_top]

theorem witt_bracket_zero_apply (x : WittAlgebra k) (i : ℤ) :
    ⁅wittBasisVector k 0, x⁆ i = (i : k) * x i := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      change (wittBracketBilinear k (wittBasisVector k 0) (x + y)) i = _
      rw [map_add, Finsupp.add_apply]
      change (wittBracketBilinear k (wittBasisVector k 0) x) i +
        (wittBracketBilinear k (wittBasisVector k 0) y) i = _
      change (wittBracketBilinear k (wittBasisVector k 0) x) i = _ at hx
      change (wittBracketBilinear k (wittBasisVector k 0) y) i = _ at hy
      rw [hx, hy, Finsupp.add_apply, mul_add]
  | single j r =>
      rw [show Finsupp.single j r = r • wittBasisVector k j by
        simp [wittBasisVector], witt_lie_smul, witt_bracket_basis]
      by_cases hij : i = j
      · subst i
        simp [wittBasisVector, mul_comm]
      · simp [wittBasisVector, hij]

/-- Applying `ad(e₀) - l` to a Witt vector.  This kills its `l`th
coordinate and rescales every other coordinate. -/
def wittDiagonalStep (l : ℤ) (x : WittAlgebra k) : WittAlgebra k :=
  wittBracketBilinear k (wittBasisVector k 0) x - (l : k) • x

@[simp]
theorem wittDiagonalStep_apply (l : ℤ) (x : WittAlgebra k) (i : ℤ) :
    wittDiagonalStep k l x i = ((i - l : ℤ) : k) * x i := by
  rw [wittDiagonalStep, Finsupp.sub_apply, Finsupp.smul_apply]
  change (wittBracketBilinear k (wittBasisVector k 0) x) i -
    (l : k) * x i = _
  have hzero := witt_bracket_zero_apply (k := k) x i
  change (wittBracketBilinear k (wittBasisVector k 0) x) i = _ at hzero
  rw [hzero]
  push_cast
  ring

/-- Successively eliminate the coordinates indexed by a list. -/
def wittDiagonalEliminate : List ℤ → WittAlgebra k → WittAlgebra k
  | [], x => x
  | l :: ls, x => wittDiagonalEliminate ls (wittDiagonalStep k l x)

@[simp]
theorem wittDiagonalEliminate_apply (ls : List ℤ)
    (x : WittAlgebra k) (i : ℤ) :
    wittDiagonalEliminate k ls x i =
      (ls.map (fun l => ((i - l : ℤ) : k))).prod * x i := by
  induction ls generalizing x with
  | nil => simp [wittDiagonalEliminate]
  | cons l ls ih =>
      rw [wittDiagonalEliminate, ih, wittDiagonalStep_apply]
      simp only [List.map_cons, List.prod_cons]
      ring

theorem wittDiagonalEliminate_mem_lieIdeal
    (I : LieIdeal k (WittAlgebra k)) (ls : List ℤ)
    {x : WittAlgebra k} (hx : x ∈ I) :
    wittDiagonalEliminate k ls x ∈ I := by
  induction ls generalizing x with
  | nil => simpa [wittDiagonalEliminate]
  | cons l ls ih =>
      apply ih
      rw [wittDiagonalStep]
      exact Submodule.sub_mem _
        (lie_mem_right k (WittAlgebra k) I _ _ hx)
        (Submodule.smul_mem _ _ hx)

/-- Every nonzero Witt ideal contains a standard basis vector. -/
theorem LieIdeal.exists_wittBasisVector_mem [CharZero k]
    (I : LieIdeal k (WittAlgebra k)) (hI : I ≠ ⊥) :
    ∃ j : ℤ, wittBasisVector k j ∈ I := by
  classical
  obtain ⟨x, hxI, hx⟩ : ∃ x : WittAlgebra k, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    apply le_antisymm
    · intro x hxI
      change x = 0
      exact h x hxI
    · exact bot_le
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hx
  let ls : List ℤ := (x.support.erase j).toList
  let c : k := (ls.map (fun l => ((j - l : ℤ) : k))).prod * x j
  have hprod : (ls.map (fun l => ((j - l : ℤ) : k))).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    rcases List.mem_map.1 hzero with ⟨l, hl, hlzero⟩
    have hlj : l ≠ j := by
      have : l ∈ x.support.erase j := by simpa [ls] using hl
      exact (Finset.mem_erase.1 this).1
    have hcast : (((j - l : ℤ) : k)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hlj.symm
    exact hcast hlzero
  have hc : c ≠ 0 := mul_ne_zero hprod (Finsupp.mem_support_iff.mp hj)
  have hyI : wittDiagonalEliminate k ls x ∈ I :=
    wittDiagonalEliminate_mem_lieIdeal k I ls hxI
  have hy : wittDiagonalEliminate k ls x =
      c • wittBasisVector k j := by
    ext i
    rw [wittDiagonalEliminate_apply]
    by_cases hij : i = j
    · subst i
      simp [c, wittBasisVector]
    · by_cases hi : i ∈ x.support
      · have hilist : i ∈ ls := by
          simpa [ls, hij] using Finset.mem_erase.2 ⟨hij, hi⟩
        have hzero : ((i - i : ℤ) : k) ∈
            ls.map (fun l => ((i - l : ℤ) : k)) := by
          exact List.mem_map.2 ⟨i, hilist, rfl⟩
        have hprodzero :
            (ls.map (fun l => ((i - l : ℤ) : k))).prod = 0 := by
          apply List.prod_eq_zero
          simpa using hzero
        rw [hprodzero, zero_mul]
        simp [c, wittBasisVector, hij]
      · have hxi : x i = 0 := Finsupp.notMem_support_iff.mp hi
        simp [hxi, wittBasisVector, hij]
  rw [hy] at hyI
  have hscaled := I.smul_mem c⁻¹ hyI
  exact ⟨j, by simpa [← mul_smul, hc] using hscaled⟩

theorem LieIdeal.eq_top_of_ne_bot_witt [CharZero k]
    (I : LieIdeal k (WittAlgebra k)) (hI : I ≠ ⊥) : I = ⊤ := by
  obtain ⟨j, hjI⟩ := LieIdeal.exists_wittBasisVector_mem k I hI
  have hzero : wittBasisVector k 0 ∈ I := by
    by_cases hj : j = 0
    · simpa [hj] using hjI
    · have hbr := lie_mem_left k (WittAlgebra k) I
          (wittBasisVector k j) (wittBasisVector k (-j)) hjI
      rw [witt_bracket_basis] at hbr
      have hindex : j + -j = 0 := by omega
      rw [hindex] at hbr
      have hint : -j - j ≠ 0 := by omega
      have hcoeff : (((-j - j : ℤ) : k)) ≠ 0 := by exact_mod_cast hint
      have hs := I.smul_mem ((-j - j : ℤ) : k)⁻¹ hbr
      rw [← mul_smul, inv_mul_cancel₀ hcoeff, one_smul] at hs
      exact hs
  have hbasis (l : ℤ) : wittBasisVector k l ∈ I := by
    by_cases hl : l = 0
    · simpa [hl] using hzero
    · have hbr := lie_mem_left k (WittAlgebra k) I
          (wittBasisVector k 0) (wittBasisVector k l) hzero
      rw [witt_bracket_basis] at hbr
      have hcoeff : (l : k) ≠ 0 := by exact_mod_cast hl
      have hs := I.smul_mem (l : k)⁻¹ hbr
      simpa [← mul_smul, hcoeff] using hs
  apply top_unique
  intro x hx
  clear hx
  induction x using Finsupp.induction_linear with
  | zero => exact I.zero_mem
  | add x y hx hy => exact I.add_mem hx hy
  | single i r =>
      rw [show Finsupp.single i r = r • wittBasisVector k i by
        simp [wittBasisVector]]
      exact I.smul_mem r (hbasis i)

/-- The characteristic-zero Witt algebra is simple. -/
theorem wittAlgebra_isSimple [CharZero k] :
    LieAlgebra.IsSimple k (WittAlgebra k) := by
  constructor
  · intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · exact Or.inr (LieIdeal.eq_top_of_ne_bot_witt k I hI)
  · intro hAb
    have hzero := hAb.trivial (wittBasisVector k 0) (wittBasisVector k 1)
    rw [witt_bracket_basis] at hzero
    have hone : wittBasisVector k 1 ≠ 0 := by
      intro h
      have := DFunLike.congr_fun h 1
      simp [wittBasisVector] at this
    have heq : wittBasisVector k 1 = 0 := by simpa using hzero
    exact hone heq

/-- Integer degrees between `-r` and `r`. -/
abbrev WittDegreeIndex (r : ℕ) :=
  ↑(Finset.Icc (-(r : ℤ)) (r : ℤ))

/-- The span of the Witt basis vectors of degree at most `r` in absolute
value. -/
def wittDegreeWindow (r : ℕ) : Submodule k (WittAlgebra k) :=
  Submodule.span k
    (Set.range fun i : WittDegreeIndex r => wittBasisVector k i.1)

theorem wittBasisVector_mem_degreeWindow {r : ℕ} {i : ℤ}
    (hi : -(r : ℤ) ≤ i ∧ i ≤ (r : ℤ)) :
    wittBasisVector k i ∈ wittDegreeWindow k r := by
  apply Submodule.subset_span
  let j : WittDegreeIndex r := ⟨i, by simpa using hi⟩
  exact ⟨j, rfl⟩

theorem wittDegreeWindow_mono {r s : ℕ} (hrs : r ≤ s) :
    wittDegreeWindow k r ≤ wittDegreeWindow k s := by
  rw [wittDegreeWindow, wittDegreeWindow]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  have hi := i.2
  simp only [Finset.mem_Icc] at hi
  have hrsZ : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast hrs
  let j : WittDegreeIndex s := ⟨i.1, by
    simp only [Finset.mem_Icc]
    constructor <;> omega⟩
  exact ⟨j, rfl⟩

theorem witt_bracket_mem_degreeWindow {r s : ℕ}
    {x y : WittAlgebra k} (hx : x ∈ wittDegreeWindow k r)
    (hy : y ∈ wittDegreeWindow k s) :
    wittBracketBilinear k x y ∈ wittDegreeWindow k (r + s) := by
  refine Submodule.span_induction
    (p := fun x _ =>
      wittBracketBilinear k x y ∈ wittDegreeWindow k (r + s))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun y _ =>
        wittBracketBilinear k (wittBasisVector k i.1) y ∈
          wittDegreeWindow k (r + s))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      rw [← witt_bracket_eq, witt_bracket_basis]
      apply Submodule.smul_mem
      apply wittBasisVector_mem_degreeWindow (k := k) (r := r + s)
      have hi := i.2
      have hj := j.2
      simp only [Finset.mem_Icc] at hi hj
      norm_num [Nat.cast_add]
      constructor <;> omega
    · simp
    · intro a b ha hb hma hmb
      rw [map_add]
      exact Submodule.add_mem _ hma hmb
    · intro a z hz hmz
      rw [map_smul]
      exact Submodule.smul_mem _ a hmz
  · simp
  · intro a b ha hb hma hmb
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hma hmb
  · intro a z hz hmz
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ a hmz

/-- The subspace spanned by the four standard Witt generators. -/
def wittGeneratorSubmodule : Submodule k (WittAlgebra k) :=
  Submodule.span k (wittGeneratingSet k)

theorem wittGeneratorSubmodule_le_degreeWindow :
    wittGeneratorSubmodule k ≤ wittDegreeWindow k 2 := by
  apply Submodule.span_le.mpr
  intro x hx
  simp only [wittGeneratingSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    apply wittBasisVector_mem_degreeWindow (k := k) (r := 2) <;> norm_num

/-- The Lie-growth balls for the standard four-dimensional generating
subspace of the Witt algebra. -/
def wittLieBall : ℕ → Submodule k (WittAlgebra k)
  | 0 => wittGeneratorSubmodule k
  | n + 1 =>
      lieExpansion (wittGeneratorSubmodule k) (wittLieBall n)

@[simp]
theorem wittLieBall_zero :
    wittLieBall (k := k) 0 = wittGeneratorSubmodule k :=
  rfl

@[simp]
theorem wittLieBall_succ (n : ℕ) :
    wittLieBall (k := k) (n + 1) =
      lieExpansion (wittGeneratorSubmodule k) (wittLieBall (k := k) n) :=
  rfl

/-- The `n`th Witt ball is supported in degrees of absolute value at most
`2(n+1)`. -/
theorem wittLieBall_le_degreeWindow (n : ℕ) :
    wittLieBall (k := k) n ≤ wittDegreeWindow k (2 * (n + 1)) := by
  induction n with
  | zero =>
      simpa using wittGeneratorSubmodule_le_degreeWindow k
  | succ n ih =>
      rw [wittLieBall_succ, lieExpansion, sup_le_iff]
      constructor
      · exact ih.trans (wittDegreeWindow_mono (k := k) (by omega))
      · rw [lieActionSubspace_eq_map₂]
        apply Submodule.map₂_le.2
        intro x hx y hy
        have hx' := wittGeneratorSubmodule_le_degreeWindow k hx
        have hy' := ih hy
        have hbr := witt_bracket_mem_degreeWindow (k := k) hx' hy'
        change wittBracketBilinear k x y ∈ _
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hbr

theorem finiteDimensional_wittDegreeWindow (r : ℕ) :
    FiniteDimensional k (wittDegreeWindow k r) := by
  exact FiniteDimensional.span_of_finite k (Set.finite_range _)

theorem finrank_wittDegreeWindow (r : ℕ) :
    sfinrank k (wittDegreeWindow k r) = 2 * r + 1 := by
  have hli : LinearIndependent k
      (fun i : WittDegreeIndex r => wittBasisVector k i.1) := by
    change LinearIndependent k
      (fun i : WittDegreeIndex r => Finsupp.single i.1 (1 : k))
    have h := (Finsupp.basisSingleOne (R := k)).linearIndependent.comp
      (fun i : WittDegreeIndex r => i.1) Subtype.val_injective
    change LinearIndependent k
      ((fun i : ℤ => Finsupp.single i (1 : k)) ∘
        fun i : WittDegreeIndex r => i.1) at h
    simpa only [Function.comp_def] using h
  rw [sfinrank, wittDegreeWindow, finrank_span_eq_card hli,
    Fintype.card_coe, Int.card_Icc]
  rw [show ((r : ℤ) + 1 - -(r : ℤ)) =
      ((2 * r + 1 : ℕ) : ℤ) by
    push_cast
    ring, Int.toNat_natCast]

theorem finiteDimensional_wittLieBall (n : ℕ) :
    FiniteDimensional k (wittLieBall (k := k) n) := by
  let _ : FiniteDimensional k (wittDegreeWindow k (2 * (n + 1))) :=
    finiteDimensional_wittDegreeWindow k _
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (wittLieBall_le_degreeWindow k n))
    (Submodule.inclusion_injective _)

/-- The standard Witt growth balls have a linear dimension bound. -/
theorem finrank_wittLieBall_le (n : ℕ) :
    sfinrank k (wittLieBall (k := k) n) ≤ 4 * n + 5 := by
  let _ : FiniteDimensional k (wittLieBall (k := k) n) :=
    finiteDimensional_wittLieBall k n
  let _ : FiniteDimensional k (wittDegreeWindow k (2 * (n + 1))) :=
    finiteDimensional_wittDegreeWindow k _
  have hmono := Submodule.finrank_mono (wittLieBall_le_degreeWindow k n)
  change sfinrank k (wittLieBall (k := k) n) ≤
    sfinrank k (wittDegreeWindow k (2 * (n + 1))) at hmono
  rw [finrank_wittDegreeWindow] at hmono
  omega

/-- A concrete formulation of linear Lie growth: a finite-dimensional
generating subspace has recursively defined Lie balls bounded by an affine
linear function. -/
def HasLinearLieGrowth (L : Type*) [LieRing L] [LieAlgebra k L] : Prop :=
  ∃ (F : Submodule k L) (B : ℕ → Submodule k L) (a b : ℕ),
    FiniteDimensional k F ∧
      LieSubalgebra.lieSpan k L (F : Set L) = ⊤ ∧
      B 0 = F ∧
      (∀ n, B (n + 1) = lieExpansion F (B n)) ∧
      (∀ n, FiniteDimensional k (B n) ∧ sfinrank k (B n) ≤ a * n + b)

theorem finiteDimensional_wittGeneratorSubmodule :
    FiniteDimensional k (wittGeneratorSubmodule k) := by
  exact FiniteDimensional.span_of_finite k (by
    rw [← coe_wittGeneratingFinset]
    exact (wittGeneratingFinset k).finite_toSet)

theorem wittGeneratorSubmodule_lieSpan_eq_top [CharZero k] :
    LieSubalgebra.lieSpan k (WittAlgebra k)
      (wittGeneratorSubmodule k : Set (WittAlgebra k)) = ⊤ := by
  apply top_unique
  rw [← witt_lieSpan_generators_eq_top (k := k)]
  apply LieSubalgebra.lieSpan_mono
  exact Submodule.subset_span

/-- The standard Witt algebra has linear growth. -/
theorem wittAlgebra_hasLinearLieGrowth [CharZero k] :
    HasLinearLieGrowth k (WittAlgebra k) := by
  refine ⟨wittGeneratorSubmodule k, wittLieBall (k := k), 4, 5,
    finiteDimensional_wittGeneratorSubmodule k,
    wittGeneratorSubmodule_lieSpan_eq_top k, rfl, ?_, ?_⟩
  · intro n
    exact wittLieBall_succ k n
  · intro n
    exact ⟨finiteDimensional_wittLieBall k n, finrank_wittLieBall_le k n⟩




/-- The four standard properties of the characteristic-zero Witt algebra
used in Theorem H. -/
theorem wittAlgebra_properties [CharZero k] :
    IsFinitelyGeneratedLieAlgebra (k := k) (WittAlgebra k) ∧
      LieAlgebra.IsSimple k (WittAlgebra k) ∧
      ¬ FiniteDimensional k (WittAlgebra k) ∧
      HasLinearLieGrowth k (WittAlgebra k) :=
  ⟨wittAlgebra_finitelyGenerated k, wittAlgebra_isSimple k,
    wittAlgebra_not_finiteDimensional k, wittAlgebra_hasLinearLieGrowth k⟩

/-- The explicit Witt balls agree with the recursively defined manuscript
Lie balls. -/
theorem wittLieBall_eq_lieGrowthBall (n : ℕ) :
    wittLieBall (k := k) n =
      lieGrowthBall k (wittGeneratorSubmodule k) n := by
  induction n with
  | zero => rw [wittLieBall_zero, lieGrowthBall_zero]
  | succ n ih => rw [wittLieBall_succ, lieGrowthBall_succ, ih]

/-- Linear growth gives genuine subexponential growth of the Witt algebra. -/
theorem wittAlgebra_hasSubexponentialLieGrowth [CharZero k] :
    HasSubexponentialLieGrowth k (WittAlgebra k) := by
  refine ⟨wittGeneratorSubmodule k,
    finiteDimensional_wittGeneratorSubmodule k,
    wittGeneratorSubmodule_lieSpan_eq_top k, ?_⟩
  intro q hq
  let e : ℚ := q - 1
  have he : 0 < e := sub_pos.mpr hq
  let C : ℚ := 5 + 4 / e
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n
  dsimp only
  rw [← wittLieBall_eq_lieGrowthBall]
  have hdim := finrank_wittLieBall_le k n
  have hbern : 1 + (n : ℚ) * e ≤ q ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℚ) ≤ e by linarith) n
    simpa [e, add_comm, mul_comm] using this
  have hlin : (4 * n + 5 : ℚ) ≤ C * (1 + (n : ℚ) * e) := by
    dsimp [C]
    field_simp
    have hne2 : 0 ≤ (n : ℚ) * e ^ 2 := mul_nonneg (by positivity) (sq_nonneg e)
    nlinarith
  calc
    (sfinrank k (wittLieBall (k := k) n) : ℚ) ≤ (4 * n + 5 : ℕ) :=
      by exact_mod_cast hdim
    _ ≤ C * (1 + (n : ℚ) * e) := by
      norm_num [Nat.cast_add, Nat.cast_mul] at hlin ⊢
      exact hlin
    _ ≤ C * q ^ n := mul_le_mul_of_nonneg_left hbern hC.le


end
end HopfAmenability



