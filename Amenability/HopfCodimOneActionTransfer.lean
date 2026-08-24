/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfActionSubspace
import Amenability.CodimOneCoalgebraStep
import Amenability.TwoSidedCoideal
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The codimension-one transfer step for Hopf-module coalgebras
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M]
variable [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- The cocommutative mirror of the existing codimension-one error term. -/
theorem comul_sub_codimOneGroupLikeCandidate_tmul_mem
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A) (ha : ell a = 1) :
    Coalgebra.comul (R := k) (A := A.carrier) a -
        codimOneGroupLikeCandidate A ell a ⊗ₜ[k] a ∈
      LinearMap.range
        ((codimOneLower A' A).subtype.lTensor A.carrier) := by
  rcases comul_sub_tmul_codimOneGroupLikeCandidate_mem
    A' A hAA ell a hker ha with ⟨z, hz⟩
  refine ⟨(TensorProduct.comm k (codimOneLower A' A) A.carrier) z, ?_⟩
  have hz' := congrArg (TensorProduct.comm k A.carrier A.carrier) hz
  calc
    ((codimOneLower A' A).subtype.lTensor A.carrier)
        ((TensorProduct.comm k (codimOneLower A' A) A.carrier) z) =
      (TensorProduct.comm k A.carrier A.carrier)
        (((codimOneLower A' A).subtype.rTensor A.carrier) z) := by
          clear hz hz'
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simp [hx, hy]
          | tmul x y => rfl
    _ = _ := by simpa [map_sub, Coalgebra.comm_comul] using hz'

omit [Coalgebra.IsCocomm k H] in
/-- The internal copy of `A' · C` inside `A · C`. -/
def actionLowerSubspace
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) :
    Submodule k (A.act C).carrier :=
  (actionSubspace A'.carrier C.carrier).comap (A.act C).carrier.subtype

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionLowerSubspace
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (C : FiniteSubcoalgebra k M) :
    ambientImage (A.act C).carrier (actionLowerSubspace A' A C) =
      actionSubspace A'.carrier C.carrier := by
  apply ambientImage_comap_eq_of_le
  exact actionSubspace_mono_left hAA C.carrier

omit [Coalgebra.IsCocomm k H] in
/-- The lower action subspace is a subcoalgebra of the upper action
subspace. -/
theorem actionLowerSubspace_isSubcoalgebra
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (C : FiniteSubcoalgebra k M) :
    IsSubcoalgebra (k := k) (actionLowerSubspace A' A C) := by
  apply (isSubcoalgebra_ambientImage_iff (A.act C).carrier
    (A.act C).isSubcoalgebra (actionLowerSubspace A' A C)).mp
  rw [ambientImage_actionLowerSubspace A' A hAA C]
  exact (A'.act C).isSubcoalgebra

omit [Coalgebra.IsCocomm k H] in
/-- The denominator at a codimension-one action step. -/
def actionStepDenominator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier) : Submodule k (A.act C).carrier :=
  D ⊔ actionLowerSubspace A' A C

omit [Coalgebra.IsCocomm k H] in
theorem actionStepDenominator_isSubcoalgebra
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier) (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (actionStepDenominator A' A C D) :=
  hD.sup (actionLowerSubspace_isSubcoalgebra A' A hAA C)

omit [Coalgebra.IsCocomm k H] in
/-- The restricted action with codomain its action subspace. -/
def actionToActMap
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) :
    A.carrier ⊗[k] C.carrier →ₗ[k] (A.act C).carrier :=
  LinearMap.codRestrict (A.act C).carrier
    (restrictedHopfModuleAction A.carrier C.carrier)
    (fun z => ⟨z, rfl⟩)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem actionToActMap_tmul
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (a : A.carrier) (c : C.carrier) :
    actionToActMap A C (a ⊗ₜ[k] c) =
      ⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
theorem actionToActMap_surjective
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) :
    Function.Surjective (actionToActMap A C) := by
  rintro ⟨x, hx⟩
  rcases hx with ⟨z, rfl⟩
  exact ⟨z, rfl⟩

omit [Coalgebra.IsCocomm k H] in
/-- Action by the chosen complement followed by the denominator quotient. -/
def actionStepQuotientMap
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier) (a : A.carrier) :
    C.carrier →ₗ[k] (A.act C).carrier ⧸ actionStepDenominator A' A C D :=
  (actionStepDenominator A' A C D).mkQ.comp
    (LinearMap.codRestrict (A.act C).carrier
      ((Algebra.lsmul k k M (a : H)).comp C.carrier.subtype)
      (fun c => product_mem_actionSubspace a.2 c.2))

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem actionStepQuotientMap_apply
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier) (a : A.carrier) (c : C.carrier) :
    actionStepQuotientMap A' A C D a c =
      (actionStepDenominator A' A C D).mkQ
        ⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
theorem actionStepQuotientMap_surjective
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A) (ha : ell a = 1) :
    Function.Surjective (actionStepQuotientMap A' A C D a) := by
  let Q := actionStepDenominator A' A C D
  have hlower : ∀ x : A.carrier,
      x - ell x • a ∈ codimOneLower A' A := by
    intro x
    rw [← hker, LinearMap.mem_ker]
    simp [ha]
  have htmul : ∀ (x : A.carrier) (c : C.carrier),
      Q.mkQ (actionToActMap A C (x ⊗ₜ[k] c)) =
        actionStepQuotientMap A' A C D a (ell x • c) := by
    intro x c
    rw [actionStepQuotientMap_apply]
    apply (Submodule.Quotient.eq Q).2
    change (⟨(x : H) • (c : M), product_mem_actionSubspace x.2 c.2⟩ :
        (A.act C).carrier) -
      ⟨(a : H) • ((ell x • c : C.carrier) : M),
        product_mem_actionSubspace a.2 (ell x • c).2⟩ ∈ Q
    apply Submodule.mem_sup_right
    change (x : H) • (c : M) - (a : H) • (ell x • (c : M)) ∈
      actionSubspace A'.carrier C.carrier
    have hp := product_mem_actionSubspace (hlower x) c.2
    convert hp using 1
    change (x : H) • (c : M) - (a : H) • (ell x • (c : M)) =
      ((x : H) - ell x • (a : H)) • (c : M)
    rw [sub_smul, smul_algebra_smul_comm, smul_assoc]
  intro q
  obtain ⟨y, rfl⟩ := Q.mkQ_surjective q
  obtain ⟨z, rfl⟩ := actionToActMap_surjective A C y
  induction z using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, map_zero]
  | add z w hz hw =>
      rcases hz with ⟨c, hc⟩
      rcases hw with ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      rw [map_add, hc, hd, map_add, map_add]
  | tmul x c => exact ⟨ell x • c, (htmul x c).symm⟩

omit [Coalgebra.IsCocomm k H] in
/-- The kernel produced by the codimension-one action quotient. -/
def actionStepKernel
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier) (a : A.carrier) :
    Submodule k C.carrier :=
  LinearMap.ker (actionStepQuotientMap A' A C D a)

omit [Coalgebra.IsCocomm k H] in
/-- Action by an internal coefficient, with codomain the action
subcoalgebra. -/
def groupLikeActionMap
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (g : A.carrier) : C.carrier →ₗ[k] (A.act C).carrier :=
  LinearMap.codRestrict (A.act C).carrier
    ((Algebra.lsmul k k M (g : H)).comp C.carrier.subtype)
    (fun c => product_mem_actionSubspace g.2 c.2)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem groupLikeActionMap_apply
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (g : A.carrier) (c : C.carrier) :
    ((groupLikeActionMap A C g c : (A.act C).carrier) : M) =
      (g : H) • (c : M) := rfl

omit [Coalgebra.IsCocomm k H] in
theorem groupLikeActionMap_injective
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (C : FiniteSubcoalgebra k M)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A) (ha : ell a = 1) :
    Function.Injective
      (groupLikeActionMap A C (codimOneGroupLikeCandidate A ell a)) := by
  intro x y hxy
  apply Subtype.ext
  apply groupLike_action_injective
    (codimOneGroupLikeCandidate_isGroupLike_ambient
      A' A hAA ell a hker ha)
  exact congrArg (fun z : (A.act C).carrier => (z : M)) hxy

omit [Coalgebra.IsCocomm k H] in
/-- Rank-nullity for the codimension-one action quotient. -/
theorem finrank_actionStepDenominator_difference
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A) (ha : ell a = 1) :
    finrank k (A.act C).carrier -
        sfinrank k (actionStepDenominator A' A C D) =
      finrank k C.carrier - sfinrank k (actionStepKernel A' A C D a) := by
  let φ := actionStepQuotientMap A' A C D a
  let Q := actionStepDenominator A' A C D
  have hsurj : Function.Surjective φ :=
    actionStepQuotientMap_surjective A' A C D ell a hker ha
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hφ := LinearMap.finrank_range_add_finrank_ker φ
  have hQ := Q.finrank_quotient_add_finrank
  rw [hrange, finrank_top] at hφ
  change finrank k (A.act C).carrier - finrank k Q =
    finrank k C.carrier - finrank k (LinearMap.ker φ)
  have hleft : finrank k (A.act C).carrier - finrank k Q =
      finrank k ((A.act C).carrier ⧸ Q) := by
    rw [← hQ]
    exact Nat.add_sub_cancel_right _ _
  have hright : finrank k C.carrier - finrank k (LinearMap.ker φ) =
      finrank k ((A.act C).carrier ⧸ Q) := by
    rw [← hφ]
    exact Nat.add_sub_cancel_right _ _
  exact hleft.trans hright.symm

end

end HopfAmenability
