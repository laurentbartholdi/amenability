/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Comodule
import Amenability.TensorIndependentDecomposition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The fundamental theorem for comodules
-/

open Module TensorProduct

noncomputable section

universe u v w

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [RightComodule k C M]

/-- Contract the right tensor factor against a linear functional. -/
noncomputable def TensorProduct.rightContract (f : C →ₗ[k] k) :
    C ⊗[k] C →ₗ[k] C :=
  (TensorProduct.rid k C).toLinearMap ∘ₗ f.lTensor C

omit [Coalgebra k C] [RightComodule k C M] in
@[simp]
theorem TensorProduct.rightContract_tmul
    (f : C →ₗ[k] k) (c d : C) :
    TensorProduct.rightContract f (c ⊗ₜ[k] d) = f d • c := by
  rfl

omit [Coalgebra k C] [RightComodule k C M] in
@[simp]
theorem TensorProduct.rightContract_lTensor_assoc_tmul
    (f : C →ₗ[k] k) (z : M ⊗[k] C) (d : C) :
    (TensorProduct.rightContract f).lTensor M
        (TensorProduct.assoc k M C C (z ⊗ₜ[k] d)) =
      f d • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [add_tmul, map_add, map_add, hx, hy, smul_add]
  | tmul m c => simp

/-- The coordinate functional attached to a member of a linearly independent
finite family, extended to the whole ambient space. -/
noncomputable def linearIndependentCoordinate
    {n : ℕ} (c : Fin n → C) (hc : LinearIndependent k c) (j : Fin n) :
    C →ₗ[k] k :=
  let U := Submodule.span k (Set.range c)
  Subspace.dualLift U ((Basis.span hc).coord j)

omit [Coalgebra k C] in
@[simp]
theorem linearIndependentCoordinate_apply
    {n : ℕ} (c : Fin n → C) (hc : LinearIndependent k c) (i j : Fin n) :
    linearIndependentCoordinate c hc j (c i) = if i = j then 1 else 0 := by
  classical
  unfold linearIndependentCoordinate
  rw [Subspace.dualLift_of_mem
    (Submodule.subset_span (Set.mem_range_self i))]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- Every element of a right comodule lies in a finite-dimensional right
subcomodule. -/
theorem exists_finiteDimensional_rightSubcomodule (m : M) :
    ∃ N : Submodule k M,
      IsRightSubcomodule (C := C) N ∧
        FiniteDimensional k N ∧ m ∈ N := by
  let ρ := RightComodule.coaction (k := k) (C := C) (M := M)
  obtain ⟨n, mi, ci, hci, hρm⟩ :=
    TensorProduct.exists_sum_tmul_linearlyIndependent_right (ρ m)
  let N : Submodule k M := Submodule.span k (Set.range mi)
  have hmiN : ∀ i, mi i ∈ N := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have hmN : m ∈ N := by
    have hcounit := RightComodule.counit_apply (k := k) (C := C) m
    change TensorProduct.rid k M
      ((Coalgebra.counit (R := k) (A := C)).lTensor M (ρ m)) = m at hcounit
    rw [hρm, map_sum] at hcounit
    have hcounit' :
        ∑ i, Coalgebra.counit (R := k) (A := C) (ci i) • mi i = m := by
      simpa only [map_sum, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul] using hcounit
    rw [← hcounit']
    apply Submodule.sum_mem
    intro i hi
    exact N.smul_mem _ (hmiN i)
  have hgenerator : ∀ j, ρ (mi j) ∈ LinearMap.range (N.subtype.rTensor C) := by
    intro j
    let fj : C →ₗ[k] k := linearIndependentCoordinate ci hci j
    have hcoassoc := RightComodule.coassoc_apply (k := k) (C := C) m
    change TensorProduct.assoc k M C C (ρ.rTensor C (ρ m)) =
      (Coalgebra.comul (R := k) (A := C)).lTensor M (ρ m) at hcoassoc
    rw [hρm, map_sum, map_sum] at hcoassoc
    have hcontract := congrArg
      ((TensorProduct.rightContract fj).lTensor M) hcoassoc
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_sum] at hcontract
    have hj : ρ (mi j) =
        ∑ i, mi i ⊗ₜ[k]
          TensorProduct.rightContract fj
            (Coalgebra.comul (R := k) (A := C) (ci i)) := by
      simpa [fj, linearIndependentCoordinate_apply] using hcontract
    refine ⟨∑ i, (⟨mi i, hmiN i⟩ : N) ⊗ₜ[k]
        TensorProduct.rightContract fj
          (Coalgebra.comul (R := k) (A := C) (ci i)), ?_⟩
    rw [map_sum]
    change (∑ i, mi i ⊗ₜ[k]
        TensorProduct.rightContract fj
          (Coalgebra.comul (R := k) (A := C) (ci i))) = ρ (mi j)
    exact hj.symm
  have hNsub : IsRightSubcomodule (C := C) N := by
    intro x hx
    let stable : Submodule k M :=
      (LinearMap.range (N.subtype.rTensor C)).comap ρ
    have hNstable : N ≤ stable := by
      change Submodule.span k (Set.range mi) ≤ stable
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hgenerator i
    exact hNstable hx
  refine ⟨N, hNsub, ?_, hmN⟩
  exact Module.Finite.span_of_finite k (Set.finite_range mi)

/-- A finite set of comodule elements is contained in one finite-dimensional
right subcomodule. -/
theorem exists_finiteDimensional_rightSubcomodule_of_finite
    (s : Set M) (hs : s.Finite) :
    ∃ N : Submodule k M,
      IsRightSubcomodule (C := C) N ∧
        FiniteDimensional k N ∧ s ⊆ N := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      refine ⟨⊥, IsRightSubcomodule.bot, ?_, by simp⟩
      infer_instance
  | @insert m s hms hs ih =>
      obtain ⟨Nm, hNm, hNmfin, hmNm⟩ :=
        exists_finiteDimensional_rightSubcomodule (k := k) (C := C) m
      obtain ⟨Ns, hNs, hNsfin, hsNs⟩ := ih
      let _ : FiniteDimensional k Nm := hNmfin
      let _ : FiniteDimensional k Ns := hNsfin
      refine ⟨Nm ⊔ Ns, IsRightSubcomodule.sup hNm hNs, ?_, ?_⟩
      · infer_instance
      · intro x hx
        rcases hx with rfl | hx
        · exact (show Nm ≤ Nm ⊔ Ns from le_sup_left) hmNm
        · exact (show Ns ≤ Nm ⊔ Ns from le_sup_right) (hsNs hx)

/-- A finite-dimensional subspace of a comodule is contained in a
finite-dimensional right subcomodule. -/
theorem exists_finiteDimensional_rightSubcomodule_of_submodule
    (E : Submodule k M) [FiniteDimensional k E] :
    ∃ N : Submodule k M,
      IsRightSubcomodule (C := C) N ∧
        FiniteDimensional k N ∧ E ≤ N := by
  let e := Module.finBasis k E
  let s : Set M := Set.range fun i : Fin (finrank k E) => (e i : M)
  have hs : s.Finite := Set.finite_range _
  obtain ⟨N, hN, hNfin, hsN⟩ :=
    exists_finiteDimensional_rightSubcomodule_of_finite (k := k) (C := C) s hs
  refine ⟨N, hN, hNfin, ?_⟩
  intro x hx
  let y : E := ⟨x, hx⟩
  have hsum :
      (∑ i, (e.repr y i) • (e i : M)) ∈ N := by
    apply Submodule.sum_mem
    intro i hi
    apply N.smul_mem
    exact hsN (Set.mem_range_self i)
  have hy := e.sum_repr y
  change (∑ i, (e.repr y i) • e i) = y at hy
  have hcoe : (∑ i, (e.repr y i) • (e i : M)) = x := by
    change (∑ i, (e.repr y i) • (e i : M)) = (y : M)
    calc
      (∑ i, (e.repr y i) • (e i : M)) =
          ((↑) : E → M) (∑ i, (e.repr y i) • e i) := by
            change (∑ i, (e.repr y i) • (e i : M)) =
              E.subtype (∑ i, (e.repr y i) • e i)
            rw [map_sum]
            simp
      _ = (y : M) := congrArg ((↑) : E → M) hy
  rw [hcoe] at hsum
  exact hsum

end
