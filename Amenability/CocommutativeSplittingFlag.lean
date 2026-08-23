/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.SimultaneousInvariantFlag
import Amenability.CoalgebraBaseChange
import Amenability.CompleteSubcoalgebraFlag
import Amenability.FundamentalTheoremComodule
import Amenability.RightCoideal
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Complete subcoalgebra flags after a finite splitting-field extension
-/

open Coalgebra Module Polynomial TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {C : Type v}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Coalgebra.IsCocomm k C] [FiniteDimensional k C]

abbrev CoalgebraBasisIndex (k : Type u) (C : Type v)
    [Field k] [AddCommGroup C] [Module k C] [FiniteDimensional k C] :=
  Fin (finrank k C)

/-- The coefficient operator obtained by contracting the second leg of comultiplication. -/
noncomputable def coalgebraCoefficientOperator
    (i : CoalgebraBasisIndex k C) : Module.End k C :=
  TensorProduct.rightContract ((Module.finBasis k C).coord i) ∘ₗ
    Coalgebra.comul

omit [Coalgebra.IsCocomm k C] in
/-- Comultiplication expanded in the fixed basis on its second tensor factor. -/
theorem comul_eq_sum_coefficientOperator_tmul (c : C) :
    Coalgebra.comul (R := k) (A := C) c =
      ∑ i : CoalgebraBasisIndex k C,
        coalgebraCoefficientOperator (C := C) i c ⊗ₜ[k]
          Module.finBasis k C i := by
  let e := Module.finBasis k C
  let a : CoalgebraBasisIndex k C →₀ C :=
    TensorProduct.equivFinsuppOfBasisRight e
      (Coalgebra.comul (R := k) (A := C) c)
  calc
    Coalgebra.comul (R := k) (A := C) c =
        (TensorProduct.equivFinsuppOfBasisRight e).symm a := by
      exact (TensorProduct.equivFinsuppOfBasisRight e).symm_apply_apply _ |>.symm
    _ = a.sum fun i x ↦ x ⊗ₜ[k] e i := by simp
    _ = ∑ i, a i ⊗ₜ[k] e i := by
      rw [Finsupp.sum_fintype]
      intro i
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact TensorProduct.equivFinsuppOfBasisRight_apply
        (Module.finBasis k C) (Coalgebra.comul (R := k) (A := C) c) i

/-- Contract both factors of a tensor against two functionals. -/
noncomputable def TensorProduct.pairContract
    (f g : C →ₗ[k] k) : C ⊗[k] C →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map f g

omit [Coalgebra k C] [Coalgebra.IsCocomm k C] [FiniteDimensional k C] in
@[simp]
theorem TensorProduct.pairContract_tmul
    (f g : C →ₗ[k] k) (x y : C) :
    TensorProduct.pairContract f g (x ⊗ₜ[k] y) = f x * g y := by
  simp [TensorProduct.pairContract]

/-- Contract the last two legs of a right-associated triple tensor. -/
noncomputable def TensorProduct.rightContractTwo
    (f g : C →ₗ[k] k) : C ⊗[k] (C ⊗[k] C) →ₗ[k] C :=
  (TensorProduct.rid k C).toLinearMap ∘ₗ
    (TensorProduct.pairContract f g).lTensor C

omit [Coalgebra k C] [Coalgebra.IsCocomm k C] [FiniteDimensional k C] in
@[simp]
theorem TensorProduct.rightContractTwo_tmul
    (f g : C →ₗ[k] k) (x y z : C) :
    TensorProduct.rightContractTwo f g (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      (f y * g z) • x := by
  simp [TensorProduct.rightContractTwo]

omit [Coalgebra.IsCocomm k C] [FiniteDimensional k C] in
theorem TensorProduct.rightContract_comul_rightContract
    (f g : C →ₗ[k] k) (z : C ⊗[k] C) :
    TensorProduct.rightContract f
        (Coalgebra.comul (R := k) (A := C)
          (TensorProduct.rightContract g z)) =
      TensorProduct.rightContractTwo f g
        (TensorProduct.assoc k C C C
          ((Coalgebra.comul (R := k) (A := C)).rTensor C z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz hz'
  | tmul x y =>
      simp only [TensorProduct.rightContract_tmul, map_smul,
        LinearMap.rTensor_tmul]
      induction Coalgebra.comul (R := k) (A := C) x using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [add_tmul, map_add, hz, hz', smul_add]
      | tmul x₁ x₂ => simp [smul_smul, mul_comm]

omit [Coalgebra k C] [Coalgebra.IsCocomm k C] [FiniteDimensional k C] in
theorem TensorProduct.pairContract_comm
    (f g : C →ₗ[k] k) (z : C ⊗[k] C) :
    TensorProduct.pairContract f g (TensorProduct.comm k C C z) =
      TensorProduct.pairContract g f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz hz'
  | tmul x y => simp [mul_comm]

omit [FiniteDimensional k C] in
/-- On a cocommutative comultiplication, the last two contractions may be swapped. -/
theorem TensorProduct.rightContractTwo_comul_lTensor_comm
    (f g : C →ₗ[k] k) (z : C ⊗[k] C) :
    TensorProduct.rightContractTwo f g
        ((Coalgebra.comul (R := k) (A := C)).lTensor C z) =
      TensorProduct.rightContractTwo g f
        ((Coalgebra.comul (R := k) (A := C)).lTensor C z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz hz'
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul]
      change (TensorProduct.pairContract f g
          (Coalgebra.comul (R := k) (A := C) y)) • x =
        (TensorProduct.pairContract g f
          (Coalgebra.comul (R := k) (A := C) y)) • x
      congr 1
      rw [← TensorProduct.pairContract_comm f g,
        Coalgebra.comm_comul]

/-- Coordinate coefficient operators commute in a cocommutative coalgebra. -/
theorem coefficientOperator_commute
    (i j : CoalgebraBasisIndex k C) :
    Commute (coalgebraCoefficientOperator (C := C) i)
      (coalgebraCoefficientOperator (C := C) j) := by
  apply LinearMap.ext
  intro c
  let fi := (Module.finBasis k C).coord i
  let fj := (Module.finBasis k C).coord j
  calc
    coalgebraCoefficientOperator (C := C) i
        (coalgebraCoefficientOperator (C := C) j c) =
      TensorProduct.rightContractTwo fi fj
        (TensorProduct.assoc k C C C
          ((Coalgebra.comul (R := k) (A := C)).rTensor C
            (Coalgebra.comul (R := k) (A := C) c))) := by
        exact TensorProduct.rightContract_comul_rightContract fi fj _
    _ = TensorProduct.rightContractTwo fi fj
        ((Coalgebra.comul (R := k) (A := C)).lTensor C
          (Coalgebra.comul (R := k) (A := C) c)) := by
        rw [Coalgebra.coassoc_apply]
    _ = TensorProduct.rightContractTwo fj fi
        ((Coalgebra.comul (R := k) (A := C)).lTensor C
          (Coalgebra.comul (R := k) (A := C) c)) :=
        TensorProduct.rightContractTwo_comul_lTensor_comm fi fj _
    _ = coalgebraCoefficientOperator (C := C) j
        (coalgebraCoefficientOperator (C := C) i c) := by
        rw [← Coalgebra.coassoc_apply]
        exact (TensorProduct.rightContract_comul_rightContract fj fi _).symm

/-- A single polynomial whose splitting field splits all coefficient operators. -/
noncomputable def coalgebraSplittingPolynomial : k[X] :=
  ∏ i : CoalgebraBasisIndex k C,
    (coalgebraCoefficientOperator (C := C) i).charpoly

/-- The finite splitting field used to triangularize the coefficient operators. -/
abbrev CoalgebraSplittingField :=
  Polynomial.SplittingField (coalgebraSplittingPolynomial (k := k) (C := C))

omit [Coalgebra.IsCocomm k C] in
/-- Every base-changed coefficient operator has split characteristic polynomial. -/
theorem coefficientOperator_charpoly_splits
    (i : CoalgebraBasisIndex k C) :
    ((coalgebraCoefficientOperator (C := C) i).baseChange
      (CoalgebraSplittingField (k := k) (C := C))).charpoly.Splits := by
  let q := coalgebraSplittingPolynomial (k := k) (C := C)
  let K := CoalgebraSplittingField (k := k) (C := C)
  rw [LinearMap.charpoly_baseChange]
  apply (Polynomial.SplittingField.splits q).of_dvd
  · apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    apply Polynomial.monic_prod_of_monic
    intro j _
    exact LinearMap.charpoly_monic
      (coalgebraCoefficientOperator (C := C) j)
  · apply Polynomial.map_dvd
    exact Finset.dvd_prod_of_mem (fun j : CoalgebraBasisIndex k C ↦
      (coalgebraCoefficientOperator (C := C) j).charpoly) (Finset.mem_univ i)

section BaseChanged

variable {K : Type w} [Field K] [Algebra k K]

/-- The scalar extension of a coefficient operator. -/
noncomputable def baseChangedCoefficientOperator
    (i : CoalgebraBasisIndex k C) : Module.End K (K ⊗[k] C) :=
  (coalgebraCoefficientOperator (C := C) i).baseChange K

omit [Coalgebra.IsCocomm k C] in
/-- Base-changed comultiplication expanded using the original basis vectors. -/
theorem baseChange_comul_eq_sum_coefficientOperator_tmul
    (z : K ⊗[k] C) :
    Coalgebra.comul (R := K) (A := K ⊗[k] C) z =
      ∑ i : CoalgebraBasisIndex k C,
        baseChangedCoefficientOperator (K := K) (C := C) i z ⊗ₜ[K]
          ((1 : K) ⊗ₜ[k] Module.finBasis k C i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      rw [map_add, hz, hz', ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_add, add_tmul]
  | tmul a c =>
      rw [TensorProduct.comul_tmul,
        comul_eq_sum_coefficientOperator_tmul (C := C) c,
        tmul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [CommSemiring.comul_apply,
        AlgebraTensorModule.tensorTensorTensorComm_tmul,
        baseChangedCoefficientOperator, LinearMap.baseChange_tmul]
      calc
        ((1 : K) ⊗ₜ[k] coalgebraCoefficientOperator (C := C) i c) ⊗ₜ[K]
            (a ⊗ₜ[k] Module.finBasis k C i) =
          ((1 : K) ⊗ₜ[k] coalgebraCoefficientOperator (C := C) i c) ⊗ₜ[K]
            (a • ((1 : K) ⊗ₜ[k] Module.finBasis k C i)) := by
              congr 1
              simp [smul_tmul', smul_eq_mul]
        _ = (a • ((1 : K) ⊗ₜ[k]
              coalgebraCoefficientOperator (C := C) i c)) ⊗ₜ[K]
            ((1 : K) ⊗ₜ[k] Module.finBasis k C i) := by
              rw [tmul_smul, smul_tmul']
        _ = _ := by
          apply congrArg (fun z : K ⊗[k] C ↦
            z ⊗ₜ[K] ((1 : K) ⊗ₜ[k] Module.finBasis k C i))
          simp [smul_tmul', smul_eq_mul]

end BaseChanged

section InvariantCoideals

variable {K : Type w} [Field K] [Algebra k K]

omit [Coalgebra.IsCocomm k C] in
/-- Invariance under all coefficient operators makes a subspace a right coideal. -/
theorem isRightSubcomodule_of_coefficient_invariant
    (P : Submodule K (K ⊗[k] C))
    (hP : IsInvariantUnder
      (fun i ↦ baseChangedCoefficientOperator (K := K) (C := C) i) P) :
    IsRightSubcomodule (k := K) (C := K ⊗[k] C) P := by
  intro z hz
  let q : P ⊗[K] (K ⊗[k] C) :=
    ∑ i : CoalgebraBasisIndex k C,
      (⟨baseChangedCoefficientOperator (K := K) (C := C) i z,
        hP i hz⟩ : P) ⊗ₜ[K]
          ((1 : K) ⊗ₜ[k] Module.finBasis k C i)
  refine ⟨q, ?_⟩
  change (P.subtype.rTensor (K ⊗[k] C)) q =
    Coalgebra.comul (R := K) (A := K ⊗[k] C) z
  rw [baseChange_comul_eq_sum_coefficientOperator_tmul (C := C) z]
  unfold q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- In the cocommutative scalar extension, coefficient-invariant subspaces are subcoalgebras. -/
theorem isSubcoalgebra_of_coefficient_invariant
    (P : Submodule K (K ⊗[k] C))
    (hP : IsInvariantUnder
      (fun i ↦ baseChangedCoefficientOperator (K := K) (C := C) i) P) :
    IsSubcoalgebra (k := K) P := by
  apply isSubcoalgebra_of_isRightSubcomodule
  exact isRightSubcomodule_of_coefficient_invariant P hP

end InvariantCoideals

/-- The full scalar extension has a complete flag by finite subcoalgebras. -/
theorem exists_topFiniteSubcoalgebra_with_completeFlag :
    let K := CoalgebraSplittingField (k := k) (C := C)
    ∃ ATop : FiniteSubcoalgebra K (K ⊗[k] C),
      ATop.carrier = ⊤ ∧
        PrimalTransfer.HasCompleteSubcoalgebraFlag ATop := by
  let K := CoalgebraSplittingField (k := k) (C := C)
  let T : CoalgebraBasisIndex k C → Module.End K (K ⊗[k] C) :=
    fun i ↦ baseChangedCoefficientOperator (K := K) (C := C) i
  have hcommT : ∀ i j, Commute (T i) (T j) := by
    intro i j
    rw [Commute]
    change (coalgebraCoefficientOperator (C := C) i).baseChange K ∘ₗ
        (coalgebraCoefficientOperator (C := C) j).baseChange K =
      (coalgebraCoefficientOperator (C := C) j).baseChange K ∘ₗ
        (coalgebraCoefficientOperator (C := C) i).baseChange K
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      show (coalgebraCoefficientOperator (C := C) i).comp
          (coalgebraCoefficientOperator (C := C) j) =
        (coalgebraCoefficientOperator (C := C) j).comp
          (coalgebraCoefficientOperator (C := C) i) from
        (coefficientOperator_commute (C := C) i j).eq]
  have hflagInv : HasCompleteInvariantFlag T ⊤ :=
    completeInvariantFlag_of_commute_of_splits_charpoly T hcommT
      (fun i ↦ coefficientOperator_charpoly_splits (C := C) i)
  have convert {P : Submodule K (K ⊗[k] C)}
      (hflag : HasCompleteInvariantFlag T P) :
      ∃ A : FiniteSubcoalgebra K (K ⊗[k] C),
        A.carrier = P ∧ PrimalTransfer.HasCompleteSubcoalgebraFlag A := by
    induction hflag with
    | bot =>
        let A : FiniteSubcoalgebra K (K ⊗[k] C) :=
          { carrier := ⊥
            isSubcoalgebra := by
              exact isSubcoalgebra_of_coefficient_invariant ⊥
                (isInvariantUnder_bot T)
            finiteDimensional := inferInstance }
        exact ⟨A, rfl, PrimalTransfer.HasCompleteSubcoalgebraFlag.bot rfl⟩
    | @step P Q hflag hPQ hdim hQinv ih =>
        obtain ⟨A', hA', hflagA'⟩ := ih
        let A : FiniteSubcoalgebra K (K ⊗[k] C) :=
          { carrier := Q
            isSubcoalgebra :=
              isSubcoalgebra_of_coefficient_invariant Q hQinv
            finiteDimensional := inferInstance }
        refine ⟨A, rfl, PrimalTransfer.HasCompleteSubcoalgebraFlag.step
          hflagA' ?_ ?_⟩
        · simpa [hA'] using hPQ
        · change finrank K Q = finrank K A'.carrier + 1
          rw [hA']
          exact hdim
  exact convert hflagInv

section AmbientHopf

variable {H : Type w} [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/-- After a finite field extension, an ambient finite subcoalgebra has a complete flag. -/
theorem exists_baseChange_completeSubcoalgebraFlag
    (A : FiniteSubcoalgebra k H) :
    let K := CoalgebraSplittingField (k := k) (C := A.carrier)
    ∃ AK : FiniteSubcoalgebra K (K ⊗[k] H),
      AK.carrier = baseChangeSubspace (k := k) K A.carrier ∧
        PrimalTransfer.HasCompleteSubcoalgebraFlag AK := by
  let K := CoalgebraSplittingField (k := k) (C := A.carrier)
  let incK : K ⊗[k] A.carrier →ₗc[K] K ⊗[k] H :=
    Coalgebra.TensorProduct.map (CoalgHom.id K K)
      (subcoalgebraInclusion A.carrier A.isSubcoalgebra)
  have hincLinear : incK.toLinearMap = A.carrier.subtype.baseChange K := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz hz'
    | tmul a x => rfl
  have hincK : Function.Injective incK := by
    rw [show Function.Injective incK ↔ Function.Injective incK.toLinearMap from Iff.rfl,
      hincLinear]
    exact Module.Flat.lTensor_preserves_injective_linearMap
      A.carrier.subtype A.carrier.injective_subtype
  obtain ⟨ATop, hATop, hflag⟩ :=
    exists_topFiniteSubcoalgebra_with_completeFlag
      (k := k) (C := A.carrier)
  let AK := ATop.map incK hincK
  refine ⟨AK, ?_, hflag.map incK hincK⟩
  rw [FiniteSubcoalgebra.map_carrier, hATop, Submodule.map_top]
  change LinearMap.range incK.toLinearMap =
    LinearMap.range (A.carrier.subtype.baseChange K)
  rw [hincLinear]

end AmbientHopf

end

end UnifiedRounding
