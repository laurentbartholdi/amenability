/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FundamentalTheoremComodule
import Amenability.FiniteSubcoalgebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Coefficient coalgebras of finite-dimensional comodules
-/

open Module TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v w x

variable {k : Type u} {C : Type v} {M : Type w} {X : Type x}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [RightComodule k C M]
variable [AddCommGroup X] [Module k X]

/-- Contract the left tensor factor against a linear functional. -/
noncomputable def TensorProduct.leftContract (f : M →ₗ[k] k) :
    M ⊗[k] X →ₗ[k] X :=
  (TensorProduct.lid k X).toLinearMap ∘ₗ f.rTensor X

omit [Coalgebra k C] [RightComodule k C M] in
@[simp]
theorem TensorProduct.leftContract_tmul
    (f : M →ₗ[k] k) (m : M) (y : X) :
    TensorProduct.leftContract f (m ⊗ₜ[k] y) = f m • y := by
  rfl

/-- The coaction on a finite-dimensional right subcomodule factors through a
finite-dimensional subcoalgebra of coefficients. -/
theorem exists_finiteSubcoalgebra_coaction_of_rightSubcomodule
    (N : Submodule k M)
    [FiniteDimensional k N]
    (hN : IsRightSubcomodule (C := C) N) :
    ∃ D : FiniteSubcoalgebra k C,
      ∀ m : M, m ∈ N →
        RightComodule.coaction (k := k) (C := C) (M := M) m ∈
          LinearMap.range (D.carrier.subtype.lTensor M) := by
  let ρ := RightComodule.coaction (k := k) (C := C) (M := M)
  let I := Fin (finrank k N)
  let e : Basis I k N := Module.finBasis k N
  have hzExists : ∀ j : I, ∃ z : N ⊗[k] C,
      N.subtype.rTensor C z = ρ (e j : M) := by
    intro j
    exact hN (e j : M) (e j).2
  choose z hz using hzExists
  let coeff : I → I → C := fun i j =>
    TensorProduct.equivFinsuppOfBasisLeft e (z j) i
  have hzExpansion : ∀ j : I,
      z j = ∑ i, e i ⊗ₜ[k] coeff i j := by
    intro j
    let a : I →₀ C := TensorProduct.equivFinsuppOfBasisLeft e (z j)
    calc
      z j = (TensorProduct.equivFinsuppOfBasisLeft e).symm a := by
        exact (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply (z j) |>.symm
      _ = a.sum fun i c => e i ⊗ₜ[k] c := by simp
      _ = ∑ i, e i ⊗ₜ[k] coeff i j := by
        classical
        rw [Finsupp.sum_fintype]
        intro i
        simp
  have hstar : ∀ j : I,
      ρ (e j : M) = ∑ i, (e i : M) ⊗ₜ[k] coeff i j := by
    intro j
    rw [← hz j, hzExpansion j, map_sum]
    rfl
  have heIndependent :
      LinearIndependent k (fun i : I => (e i : M)) :=
    e.linearIndependent.map' N.subtype N.ker_subtype
  have hcoeffComul : ∀ l j : I,
      Coalgebra.comul (R := k) (A := C) (coeff l j) =
        ∑ i, coeff l i ⊗ₜ[k] coeff i j := by
    intro l j
    have hcoassoc := RightComodule.coassoc_apply (k := k) (C := C) (e j : M)
    change TensorProduct.assoc k M C C (ρ.rTensor C (ρ (e j : M))) =
      (Coalgebra.comul (R := k) (A := C)).lTensor M (ρ (e j : M)) at hcoassoc
    rw [hstar j, map_sum, map_sum] at hcoassoc
    simp only [LinearMap.rTensor_tmul] at hcoassoc
    simp_rw [hstar] at hcoassoc
    simp only [sum_tmul, map_sum, TensorProduct.assoc_tmul] at hcoassoc
    let fl : M →ₗ[k] k :=
      linearIndependentCoordinate (fun i : I => (e i : M)) heIndependent l
    have hcontract := congrArg (TensorProduct.leftContract fl) hcoassoc
    simp only [map_sum, TensorProduct.leftContract_tmul] at hcontract
    simpa [fl, linearIndependentCoordinate_apply] using hcontract.symm
  let D0 : Submodule k C :=
    Submodule.span k (Set.range fun p : I × I => coeff p.1 p.2)
  have hcoeffD0 : ∀ i j : I, coeff i j ∈ D0 := by
    intro i j
    exact Submodule.subset_span (Set.mem_range_self (i, j))
  have hD0 : IsSubcoalgebra (k := k) D0 := by
    let stable : Submodule k C :=
      (LinearMap.range (TensorProduct.mapIncl D0 D0)).comap
        (Coalgebra.comul (R := k) (A := C))
    have hD0stable : D0 ≤ stable := by
      change Submodule.span k
        (Set.range fun p : I × I => coeff p.1 p.2) ≤ stable
      rw [Submodule.span_le]
      rintro c ⟨p, rfl⟩
      change Coalgebra.comul (R := k) (A := C) (coeff p.1 p.2) ∈
        LinearMap.range (TensorProduct.mapIncl D0 D0)
      refine ⟨∑ i, (⟨coeff p.1 i, hcoeffD0 p.1 i⟩ : D0) ⊗ₜ[k]
          (⟨coeff i p.2, hcoeffD0 i p.2⟩ : D0), ?_⟩
      rw [map_sum]
      change (∑ i, coeff p.1 i ⊗ₜ[k] coeff i p.2) =
        Coalgebra.comul (R := k) (A := C) (coeff p.1 p.2)
      exact (hcoeffComul p.1 p.2).symm
    intro c hc
    exact hD0stable hc
  let D : FiniteSubcoalgebra k C := {
    carrier := D0
    isSubcoalgebra := hD0
    finiteDimensional := Module.Finite.span_of_finite k
      (Set.finite_range fun p : I × I => coeff p.1 p.2)
  }
  refine ⟨D, ?_⟩
  let P : Submodule k M :=
    (LinearMap.range (D.carrier.subtype.lTensor M)).comap ρ
  have heP : ∀ j : I, (e j : M) ∈ P := by
    intro j
    change ρ (e j : M) ∈ LinearMap.range (D.carrier.subtype.lTensor M)
    refine ⟨∑ i, (e i : M) ⊗ₜ[k]
        (⟨coeff i j, hcoeffD0 i j⟩ : D.carrier), ?_⟩
    rw [map_sum]
    change (∑ i, (e i : M) ⊗ₜ[k] coeff i j) = ρ (e j : M)
    exact (hstar j).symm
  have hNP : N ≤ P := by
    intro m hm
    let Pint : Submodule k N := P.comap N.subtype
    have htop : (⊤ : Submodule k N) ≤ Pint := by
      rw [← e.span_eq, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact heP i
    exact htop (show (⟨m, hm⟩ : N) ∈ ⊤ from trivial)
  intro m hm
  exact hNP hm

end

end UnifiedRounding
