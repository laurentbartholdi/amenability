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
  (A.actCoalgHom C).toLinearMap

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
noncomputable def comulActionMap
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) :
    (A.carrier ⊗[k] A.carrier) ⊗[k] (C.carrier ⊗[k] C.carrier) →ₗ[k]
      (A.act C).carrier ⊗[k]
        (A.act C).carrier :=
  (TensorProduct.map
      (actionToActMap A C)
      (actionToActMap A C)).comp
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      k k k k A.carrier A.carrier C.carrier C.carrier).toLinearMap

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem comulActionMap_tmul_tmul
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (x y : A.carrier) (c d : C.carrier) :
    comulActionMap A C ((x ⊗ₜ[k] y) ⊗ₜ[k] (c ⊗ₜ[k] d)) =
      actionToActMap A C (x ⊗ₜ[k] c) ⊗ₜ[k]
        actionToActMap A C (y ⊗ₜ[k] d) := rfl

omit [Coalgebra.IsCocomm k H] in
theorem comul_action_internal
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (a : A.carrier) (c : C.carrier) :
    Coalgebra.comul (R := k)
        (A := (A.act C).carrier)
        (actionToActMap A C (a ⊗ₜ[k] c)) =
      comulActionMap A C
        (Coalgebra.comul (R := k) (A := A.carrier) a ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c) := by
  change Coalgebra.comul (R := k) (A := (A.act C).carrier)
      (A.actCoalgHom C (a ⊗ₜ[k] c)) = _
  rw [← CoalgHomClass.map_comp_comul_apply
    (A.actCoalgHom C) (a ⊗ₜ[k] c)]
  rfl

omit [Coalgebra.IsCocomm k H] in
/-- After quotienting the first product leg, the error term in `Δa` dies
and the surviving second leg is multiplication by `g`. -/
theorem quotient_comul_action_eq
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) (c : C.carrier) :
    ((actionStepDenominator A' A C D).mkQ.rTensor
        (A.act C).carrier)
      (Coalgebra.comul (R := k)
        (A := (A.act C).carrier)
        (actionToActMap A C (a ⊗ₜ[k] c))) =
    ((groupLikeActionMap A C
        (codimOneGroupLikeCandidate A ell a)).lTensor
          ((A.act C).carrier ⧸
            actionStepDenominator A' A C D))
      ((actionStepQuotientMap A' A C D a).rTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) := by
  let AC := A.act C
  let Q := actionStepDenominator A' A C D
  let g := codimOneGroupLikeCandidate A ell a
  let r := Coalgebra.comul (R := k) (A := A.carrier) a - a ⊗ₜ[k] g
  obtain ⟨r0, hr0⟩ :=
    comul_sub_tmul_codimOneGroupLikeCandidate_mem
      A' A hAA ell a hker ha
  have hr : r = ((codimOneLower A' A).subtype.rTensor A.carrier) r0 := hr0.symm
  have hlowerAmbient : ∀ x : codimOneLower A' A,
      (x.1 : H) ∈ A'.carrier := fun x => x.2
  have herror : ∀ z : (codimOneLower A' A) ⊗[k] A.carrier,
      ∀ w : C.carrier ⊗[k] C.carrier,
      (Q.mkQ.rTensor AC.carrier)
        (comulActionMap A C
          (((codimOneLower A' A).subtype.rTensor A.carrier z) ⊗ₜ[k] w)) = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        intro w
        rw [map_zero, zero_tmul, map_zero, map_zero]
    | add z z' hz hz' =>
        intro w
        rw [map_add, add_tmul, map_add, map_add, hz w, hz' w, add_zero]
    | tmul x y =>
      rw [LinearMap.rTensor_tmul]
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [tmul_zero, map_zero, map_zero]
      | add w w' hw hw' =>
        simp only [tmul_add, map_add]
        have hz : (Q.mkQ.rTensor AC.carrier)
            (comulActionMap A C
              (((codimOneLower A' A).subtype x ⊗ₜ[k] y) ⊗ₜ[k] w)) = 0 := hw
        have hz' : (Q.mkQ.rTensor AC.carrier)
            (comulActionMap A C
              (((codimOneLower A' A).subtype x ⊗ₜ[k] y) ⊗ₜ[k] w')) = 0 := hw'
        rw [hz, hz', add_zero]
      | tmul c d =>
        have hprod : (⟨(x.1 : H) • (c : M),
            product_mem_actionSubspace (hAA (hlowerAmbient x)) c.2⟩ : AC.carrier) ∈ Q := by
          apply Submodule.mem_sup_right
          exact product_mem_actionSubspace (hlowerAmbient x) c.2
        rw [comulActionMap_tmul_tmul, LinearMap.rTensor_tmul]
        have hzero : Q.mkQ
            (actionToActMap A C
              ((codimOneLower A' A).subtype x ⊗ₜ[k] c)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero Q).2
          exact hprod
        rw [hzero, zero_tmul]
  have hmain : ∀ w : C.carrier ⊗[k] C.carrier,
      (Q.mkQ.rTensor AC.carrier)
          (comulActionMap A C ((a ⊗ₜ[k] g) ⊗ₜ[k] w)) =
        ((groupLikeActionMap A C g).lTensor (AC.carrier ⧸ Q))
          ((actionStepQuotientMap A' A C D a).rTensor C.carrier w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero, map_zero, map_zero, map_zero]
    | add w w' hw hw' =>
        simpa only [tmul_add, map_add] using
          congrArg₂ (fun x y => x + y) hw hw'
    | tmul c d => rfl
  rw [comul_action_internal]
  have hsplit : Coalgebra.comul (R := k) (A := A.carrier) a =
      a ⊗ₜ[k] g + r := by dsimp [r]; abel
  rw [hsplit, add_tmul, map_add, map_add]
  have hfirst := hmain (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond := herror r0 (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond' : (Q.mkQ.rTensor AC.carrier)
      (comulActionMap A C (r ⊗ₜ[k]
        Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [hr]
    exact hsecond
  change
    (Q.mkQ.rTensor AC.carrier)
        (comulActionMap A C ((a ⊗ₜ[k] g) ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) +
      (Q.mkQ.rTensor AC.carrier)
        (comulActionMap A C (r ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) = _
  rw [hfirst, hsecond', add_zero]

omit [Coalgebra.IsCocomm k H] in
/-- The kernel of the codimension-one quotient map is a right coideal. -/
theorem actionStepKernel_isRightSubcomodule
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (A.act C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Coalgebra.IsRightCoideal (actionStepKernel A' A C D a) := by
  let AC := A.act C
  let Q := actionStepDenominator A' A C D
  let φ := actionStepQuotientMap A' A C D a
  let B := actionStepKernel A' A C D a
  let g := codimOneGroupLikeCandidate A ell a
  have hQ : IsSubcoalgebra (k := k) Q :=
    actionStepDenominator_isSubcoalgebra A' A hAA C D hD
  have hφsurj : Function.Surjective φ :=
    actionStepQuotientMap_surjective A' A C D ell a hker ha
  have hginj : Function.Injective (groupLikeActionMap A C g) :=
    groupLikeActionMap_injective A' A hAA C ell a hker ha
  have hgtensorinj : Function.Injective
      ((groupLikeActionMap A C g).lTensor (AC.carrier ⧸ Q)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hginj
  intro c hc
  have hφc : φ c = 0 := by
    change c ∈ LinearMap.ker φ at hc
    exact (LinearMap.mem_ker).1 hc
  have hacQ : actionToActMap A C (a ⊗ₜ[k] c) ∈ Q := by
    change (⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ :
      AC.carrier) ∈ Q
    apply (Submodule.Quotient.mk_eq_zero Q).1
    change Q.mkQ
      ⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ = 0 at hφc
    exact hφc
  have hquotComul : (Q.mkQ.rTensor AC.carrier)
      (Coalgebra.comul (R := k) (A := AC.carrier)
        (actionToActMap A C (a ⊗ₜ[k] c))) = 0 := by
    rcases hQ hacQ with ⟨z, hz⟩
    have hzeroIncl : ∀ w : Q ⊗[k] Q,
        (Q.mkQ.rTensor AC.carrier) (TensorProduct.mapIncl Q Q w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
      | tmul x y =>
        change Q.mkQ x ⊗ₜ[k] (y : AC.carrier) = 0
        have hxzero : Q.mkQ (x : AC.carrier) = 0 :=
          (Submodule.Quotient.mk_eq_zero Q).2 x.2
        rw [hxzero, zero_tmul]
    rw [← hz]
    exact hzeroIncl z
  have htwisted : ((groupLikeActionMap A C g).lTensor (AC.carrier ⧸ Q))
      (φ.rTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [← quotient_comul_action_eq A' A C hAA D ell a hker ha c]
    exact hquotComul
  have hφcomul : φ.rTensor C.carrier
      (Coalgebra.comul (R := k) (A := C.carrier) c) = 0 :=
    hgtensorinj (htwisted.trans (map_zero _).symm)
  let i : B →ₗ[k] C.carrier := B.subtype
  have hexact : Function.Exact i φ := by
    change Function.Exact (LinearMap.ker φ).subtype φ
    exact φ.exact_subtype_ker_map
  have htensorExact : Function.Exact
      (B.subtype.rTensor C.carrier) (φ.rTensor C.carrier) := by
    change Function.Exact (i.rTensor C.carrier) (φ.rTensor C.carrier)
    exact rTensor_exact (M := B) C.carrier hexact hφsurj
  rw [← htensorExact.linearMap_ker_eq, LinearMap.mem_ker]
  exact hφcomul

/-- After quotienting the first product leg, the error term in `Δa` dies
and the surviving second leg is multiplication by `g`. -/
theorem quotient_comul_action_eq_left
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) (c : C.carrier) :
    ((actionStepDenominator A' A C D).mkQ.lTensor
        (A.act C).carrier)
      (Coalgebra.comul (R := k)
        (A := (A.act C).carrier)
        (actionToActMap A C (a ⊗ₜ[k] c))) =
    ((groupLikeActionMap A C
        (codimOneGroupLikeCandidate A ell a)).rTensor
          ((A.act C).carrier ⧸
            actionStepDenominator A' A C D))
      ((actionStepQuotientMap A' A C D a).lTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) := by
  let AC := A.act C
  let Q := actionStepDenominator A' A C D
  let g := codimOneGroupLikeCandidate A ell a
  let r := Coalgebra.comul (R := k) (A := A.carrier) a - g ⊗ₜ[k] a
  obtain ⟨r0, hr0⟩ :=
    comul_sub_codimOneGroupLikeCandidate_tmul_mem
      A' A hAA ell a hker ha
  have hr : r = ((codimOneLower A' A).subtype.lTensor A.carrier) r0 := hr0.symm
  have hlowerAmbient : ∀ x : codimOneLower A' A,
      (x.1 : H) ∈ A'.carrier := fun x => x.2
  have herror : ∀ z : A.carrier ⊗[k] (codimOneLower A' A),
      ∀ w : C.carrier ⊗[k] C.carrier,
      (Q.mkQ.lTensor AC.carrier)
        (comulActionMap A C
          (((codimOneLower A' A).subtype.lTensor A.carrier z) ⊗ₜ[k] w)) = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        intro w
        rw [map_zero, zero_tmul, map_zero, map_zero]
    | add z z' hz hz' =>
        intro w
        rw [map_add, add_tmul, map_add, map_add, hz w, hz' w, add_zero]
    | tmul x y =>
      rw [LinearMap.lTensor_tmul]
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [tmul_zero, map_zero, map_zero]
      | add w w' hw hw' =>
        simp only [tmul_add, map_add]
        have hz : (Q.mkQ.lTensor AC.carrier)
            (comulActionMap A C
              ((x ⊗ₜ[k] (codimOneLower A' A).subtype y) ⊗ₜ[k] w)) = 0 := hw
        have hz' : (Q.mkQ.lTensor AC.carrier)
            (comulActionMap A C
              ((x ⊗ₜ[k] (codimOneLower A' A).subtype y) ⊗ₜ[k] w')) = 0 := hw'
        rw [hz, hz', add_zero]
      | tmul c d =>
        have hprod : (⟨(y.1 : H) • (d : M),
            product_mem_actionSubspace (hAA (hlowerAmbient y)) d.2⟩ : AC.carrier) ∈ Q := by
          apply Submodule.mem_sup_right
          exact product_mem_actionSubspace (hlowerAmbient y) d.2
        rw [comulActionMap_tmul_tmul, LinearMap.lTensor_tmul]
        have hzero : Q.mkQ
            (actionToActMap A C
              ((codimOneLower A' A).subtype y ⊗ₜ[k] d)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero Q).2
          exact hprod
        rw [hzero, tmul_zero]
  have hmain : ∀ w : C.carrier ⊗[k] C.carrier,
      (Q.mkQ.lTensor AC.carrier)
          (comulActionMap A C ((g ⊗ₜ[k] a) ⊗ₜ[k] w)) =
        ((groupLikeActionMap A C g).rTensor (AC.carrier ⧸ Q))
          ((actionStepQuotientMap A' A C D a).lTensor C.carrier w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero, map_zero, map_zero, map_zero]
    | add w w' hw hw' =>
        simpa only [tmul_add, map_add] using
          congrArg₂ (fun x y => x + y) hw hw'
    | tmul c d => rfl
  rw [comul_action_internal]
  have hsplit : Coalgebra.comul (R := k) (A := A.carrier) a =
      g ⊗ₜ[k] a + r := by dsimp [r]; abel
  rw [hsplit, add_tmul, map_add, map_add]
  have hfirst := hmain (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond := herror r0 (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond' : (Q.mkQ.lTensor AC.carrier)
      (comulActionMap A C (r ⊗ₜ[k]
        Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [hr]
    exact hsecond
  change
    (Q.mkQ.lTensor AC.carrier)
        (comulActionMap A C ((g ⊗ₜ[k] a) ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) +
      (Q.mkQ.lTensor AC.carrier)
        (comulActionMap A C (r ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) = _
  rw [hfirst, hsecond', add_zero]

/-- The kernel of the codimension-one quotient map is a left coideal. -/
theorem actionStepKernel_isLeftCoideal
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (A.act C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Coalgebra.IsLeftCoideal (actionStepKernel A' A C D a) := by
  let AC := A.act C
  let Q := actionStepDenominator A' A C D
  let φ := actionStepQuotientMap A' A C D a
  let B := actionStepKernel A' A C D a
  let g := codimOneGroupLikeCandidate A ell a
  have hQ : IsSubcoalgebra (k := k) Q :=
    actionStepDenominator_isSubcoalgebra A' A hAA C D hD
  have hφsurj : Function.Surjective φ :=
    actionStepQuotientMap_surjective A' A C D ell a hker ha
  have hginj : Function.Injective (groupLikeActionMap A C g) :=
    groupLikeActionMap_injective A' A hAA C ell a hker ha
  have hgtensorinj : Function.Injective
      ((groupLikeActionMap A C g).rTensor (AC.carrier ⧸ Q)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hginj
  intro c hc
  have hφc : φ c = 0 := by
    change c ∈ LinearMap.ker φ at hc
    exact (LinearMap.mem_ker).1 hc
  have hacQ : actionToActMap A C (a ⊗ₜ[k] c) ∈ Q := by
    change (⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ :
      AC.carrier) ∈ Q
    apply (Submodule.Quotient.mk_eq_zero Q).1
    change Q.mkQ
      ⟨(a : H) • (c : M), product_mem_actionSubspace a.2 c.2⟩ = 0 at hφc
    exact hφc
  have hquotComul : (Q.mkQ.lTensor AC.carrier)
      (Coalgebra.comul (R := k) (A := AC.carrier)
        (actionToActMap A C (a ⊗ₜ[k] c))) = 0 := by
    rcases hQ hacQ with ⟨z, hz⟩
    have hzeroIncl : ∀ w : Q ⊗[k] Q,
        (Q.mkQ.lTensor AC.carrier) (TensorProduct.mapIncl Q Q w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
      | tmul x y =>
        change (x : AC.carrier) ⊗ₜ[k] Q.mkQ y = 0
        have hyzero : Q.mkQ (y : AC.carrier) = 0 :=
          (Submodule.Quotient.mk_eq_zero Q).2 y.2
        rw [hyzero, tmul_zero]
    rw [← hz]
    exact hzeroIncl z
  have htwisted : ((groupLikeActionMap A C g).rTensor (AC.carrier ⧸ Q))
      (φ.lTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [← quotient_comul_action_eq_left A' A C hAA D ell a hker ha c]
    exact hquotComul
  have hφcomul : φ.lTensor C.carrier
      (Coalgebra.comul (R := k) (A := C.carrier) c) = 0 :=
    hgtensorinj (htwisted.trans (map_zero _).symm)
  let i : B →ₗ[k] C.carrier := B.subtype
  have hexact : Function.Exact i φ := by
    change Function.Exact (LinearMap.ker φ).subtype φ
    exact φ.exact_subtype_ker_map
  have htensorExact : Function.Exact
      (B.subtype.lTensor C.carrier) (φ.lTensor C.carrier) := by
    change Function.Exact (i.lTensor C.carrier) (φ.lTensor C.carrier)
    exact lTensor_exact (M := B) C.carrier hexact hφsurj
  rw [← htensorExact.linearMap_ker_eq, LinearMap.mem_ker]
  exact hφcomul

/-- The codimension-one kernel is a subcoalgebra; cocommutativity is needed
only for the acting coalgebra, not for the module coalgebra. -/
theorem actionStepKernel_isSubcoalgebra
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (A.act C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    IsSubcoalgebra (k := k) (actionStepKernel A' A C D a) :=
  Coalgebra.isSubcoalgebra_of_twoSidedCoideal
    (actionStepKernel_isRightSubcomodule A' A C hAA D hD ell a hker ha)
    (actionStepKernel_isLeftCoideal A' A C hAA D hD ell a hker ha)

omit [Coalgebra.IsCocomm k H] in
/-- The action restricted to `A ⊗ U`, with codomain `A · C`. -/
noncomputable def actionUMap
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) :
    A.carrier ⊗[k] U →ₗ[k] (A.act C).carrier :=
  (actionToActMap A C).comp (U.subtype.lTensor A.carrier)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem actionUMap_tmul
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) (a : A.carrier) (u : U) :
    actionUMap A C U (a ⊗ₜ[k] u) =
      ⟨(a : H) • (u : M), product_mem_actionSubspace a.2 u.1.2⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
/-- The internal copy of `A · U` in `A · C`. -/
noncomputable def actionUSubspace
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) : Submodule k (A.act C).carrier :=
  LinearMap.range (actionUMap A C U)

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionUSubspace
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) :
    ambientImage (A.act C).carrier (actionUSubspace A C U) =
      actionSubspace A.carrier (ambientImage C.carrier U) := by
  let e := ambientImageEquiv C.carrier U
  have hmap : ∀ z : A.carrier ⊗[k] U,
      (((actionUMap A C U z : (A.act C).carrier) : M)) =
        restrictedHopfModuleAction A.carrier (ambientImage C.carrier U)
          (TensorProduct.map LinearMap.id e.toLinearMap z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy =>
        rw [map_add, map_add, map_add]
        exact congrArg₂ (fun p q : M => p + q) hx hy
    | tmul x y => rfl
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨TensorProduct.map LinearMap.id e.toLinearMap z, (hmap z).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ :=
      (TensorProduct.map_bijective
        (f := LinearMap.id) (g := e.toLinearMap)
        Function.bijective_id e.bijective).2 z
    refine ⟨actionUMap A C U z', ⟨z', rfl⟩, ?_⟩
    change (((actionUMap A C U z' : (A.act C).carrier) : M)) =
      restrictedHopfModuleAction A.carrier (ambientImage C.carrier U) z
    rw [hmap, hz']

omit [Coalgebra.IsCocomm k H] in
/-- The internal copy of `A' · U` in `A · C`. -/
noncomputable def actionLowerUSubspace
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) : Submodule k (A.act C).carrier :=
  (actionSubspace A'.carrier (ambientImage C.carrier U)).comap
    (A.act C).carrier.subtype

omit [Coalgebra.IsCocomm k H] in
theorem actionLowerUSubspace_le_upper
    (A' A : FiniteSubcoalgebra k H) (hAA : A'.carrier ≤ A.carrier)
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier) :
    actionLowerUSubspace A' A C U ≤ actionUSubspace A C U := by
  have hUambient : ambientImage C.carrier U ≤ C.carrier := by
    rintro x ⟨u, -, rfl⟩
    exact u.2
  have hlower : actionSubspace A'.carrier (ambientImage C.carrier U) ≤
      (A.act C).carrier :=
    (actionSubspace_mono_left hAA _).trans
      (actionSubspace_mono_right A.carrier hUambient)
  have himage : ambientImage (A.act C).carrier
      (actionLowerUSubspace A' A C U) =
        actionSubspace A'.carrier (ambientImage C.carrier U) :=
    ambientImage_comap_eq_of_le _ _ hlower
  intro x hx
  have hxamb : (x : M) ∈ ambientImage (A.act C).carrier
      (actionLowerUSubspace A' A C U) := ⟨x, hx, rfl⟩
  rw [himage] at hxamb
  have hxupper := actionSubspace_mono_left hAA _ hxamb
  rw [← ambientImage_actionUSubspace A C U] at hxupper
  rcases hxupper with ⟨y, hy, hyx⟩
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy


noncomputable def actionStepUNumerator
    (_A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :
    Submodule k (A.act C).carrier :=
  D ⊔ actionUSubspace A C U

/-- The `U`-side denominator `D + A'U`. -/
noncomputable def actionStepUDenominator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :
    Submodule k (A.act C).carrier :=
  D ⊔ actionLowerUSubspace A' A C U

omit [Coalgebra.IsCocomm k H] in
theorem actionStepUDenominator_le_actionStepUNumerator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :
    actionStepUDenominator A' A C U D ≤ actionStepUNumerator A' A C U D :=
  sup_le_sup_left (actionLowerUSubspace_le_upper A' A hAA C U) D

/-- The copy of the `U`-denominator inside the `U`-numerator. -/
noncomputable def actionStepUDenominatorInNumerator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :
    Submodule k (actionStepUNumerator A' A C U D) :=
  (actionStepUDenominator A' A C U D).comap
    (actionStepUNumerator A' A C U D).subtype

/-- The projection of `D + AU` to the ambient quotient by `D + A'U`. Its
range is canonically the desired quotient. -/
noncomputable def actionStepUProjection
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :
    actionStepUNumerator A' A C U D →ₗ[k]
      (A.act C).carrier ⧸ actionStepUDenominator A' A C U D :=
  (actionStepUDenominator A' A C U D).mkQ.comp
    (actionStepUNumerator A' A C U D).subtype

/-- A concrete model of `(D + AU)/(D + A'U)`. -/
abbrev actionStepUQuotientSpace
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier) :=
  LinearMap.range (actionStepUProjection A' A C U D)

/-- Multiplication by `a` restricted to `U`. -/
noncomputable def actionStepUActionMap
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (a : A.carrier) :
    U →ₗ[k] (A.act C).carrier :=
  LinearMap.codRestrict (A.act C).carrier
    ((Algebra.lsmul k k M (a : H)).comp
      (C.carrier.subtype.comp U.subtype))
    (fun u => product_mem_actionSubspace a.2 u.1.2)

/-- The second quotient map, sending `u` to the class of `a u` in
`(D + AU)/(D + A'U)`. -/
noncomputable def actionStepUQuotientMap
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (a : A.carrier) :
    U →ₗ[k] actionStepUQuotientSpace A' A C U D :=
  LinearMap.codRestrict (actionStepUQuotientSpace A' A C U D)
    ((actionStepUDenominator A' A C U D).mkQ.comp
      (actionStepUActionMap A C U a))
    (fun u => ⟨⟨actionStepUActionMap A C U a u,
      Submodule.mem_sup_right ⟨a ⊗ₜ[k] u, rfl⟩⟩, rfl⟩)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem actionStepUQuotientMap_apply
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (a : A.carrier) (u : U) :
    actionStepUQuotientMap A' A C U D a u =
      ⟨(actionStepUDenominator A' A C U D).mkQ
          (actionStepUActionMap A C U a u),
        ⟨⟨actionStepUActionMap A C U a u,
          Submodule.mem_sup_right ⟨a ⊗ₜ[k] u, rfl⟩⟩, rfl⟩⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
theorem actionStepUQuotientMap_surjective
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (_hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Function.Surjective (actionStepUQuotientMap A' A C U D a) := by
  let Q := actionStepUDenominator A' A C U D
  have hlower : ∀ x : A.carrier,
      x - ell x • a ∈ codimOneLower A' A := by
    intro x
    rw [← hker, LinearMap.mem_ker]
    simp [ha]
  have htensor : ∀ z : A.carrier ⊗[k] U,
      ∃ u : U, Q.mkQ (actionUMap A C U z) =
        Q.mkQ (actionStepUActionMap A C U a u) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, map_zero, map_zero]
    | add z w hz hw =>
      rcases hz with ⟨u, hu⟩
      rcases hw with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      simp only [map_add]
      exact congrArg₂ (· + ·) hu hv
    | tmul x u =>
      refine ⟨ell x • u, ?_⟩
      apply (Submodule.Quotient.eq Q).2
      change actionUMap A C U (x ⊗ₜ[k] u) -
          actionStepUActionMap A C U a (ell x • u) ∈ Q
      apply Submodule.mem_sup_right
      change (x : H) • (u : M) -
          (a : H) • (ell x • (u : M)) ∈
        actionSubspace A'.carrier (ambientImage C.carrier U)
      have hp := product_mem_actionSubspace (hlower x)
        (show (u : M) ∈ ambientImage C.carrier U from ⟨u, u.2, rfl⟩)
      convert hp using 1
      change (x : H) • (u : M) - (a : H) • (ell x • (u : M)) =
        ((x : H) - ell x • (a : H)) • (u : M)
      rw [sub_smul, smul_algebra_smul_comm, smul_assoc]
  intro q
  rcases q.2 with ⟨x, hx⟩
  rcases (Submodule.mem_sup.1 x.2) with ⟨d, hd, w, hw, hdw⟩
  rcases hw with ⟨z, hz⟩
  rcases htensor z with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change Q.mkQ (actionStepUActionMap A C U a u) = q.1
  rw [← hx]
  change Q.mkQ (actionStepUActionMap A C U a u) = Q.mkQ x.1
  rw [← hdw, map_add, show Q.mkQ d = 0 by
    exact (Submodule.Quotient.mk_eq_zero Q).2 (Submodule.mem_sup_left hd),
    zero_add]
  exact hu.symm.trans (congrArg Q.mkQ hz)

omit [Coalgebra.IsCocomm k H] in
theorem actionLowerUSubspace_le_actionLowerSubspace
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier) :
    actionLowerUSubspace A' A C U ≤ actionLowerSubspace A' A C := by
  intro x hx
  change (x.1 : M) ∈ actionSubspace A'.carrier C.carrier
  change (x.1 : M) ∈
    actionSubspace A'.carrier (ambientImage C.carrier U) at hx
  apply actionSubspace_mono_right A'.carrier _ hx
  rintro y ⟨u, -, rfl⟩
  exact u.2

omit [Coalgebra.IsCocomm k H] in
theorem actionStepUQuotientMap_ker_le
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (a : A.carrier) :
    LinearMap.ker (actionStepUQuotientMap A' A C U D a) ≤
      (actionStepKernel A' A C D a).comap U.subtype := by
  intro u hu
  have hzero : (actionStepUDenominator A' A C U D).mkQ
      (actionStepUActionMap A C U a u) = 0 := by
    have hz := (LinearMap.mem_ker.1 hu)
    exact congrArg Subtype.val hz
  have hmemU : actionStepUActionMap A C U a u ∈
      actionStepUDenominator A' A C U D :=
    (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hmem : actionStepUActionMap A C U a u ∈
      actionStepDenominator A' A C D := by
    rcases (Submodule.mem_sup.1 hmemU) with ⟨d, hd, w, hw, hdw⟩
    rw [← hdw]
    exact add_mem (Submodule.mem_sup_left hd)
      (Submodule.mem_sup_right
        (actionLowerUSubspace_le_actionLowerSubspace A' A C U hw))
  change U.subtype u ∈ LinearMap.ker (actionStepQuotientMap A' A C D a)
  rw [LinearMap.mem_ker, actionStepQuotientMap_apply]
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact hmem

omit [Coalgebra.IsCocomm k H] in
/-- The gain on the `U` side dominates the codimension of the intersection
with the step kernel. -/
theorem finrank_actionStepU_difference_ge
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    (finrank k U : ℚ) -
        sfinrank k (U ⊓ actionStepKernel A' A C D a) ≤
      (sfinrank k (actionStepUNumerator A' A C U D) : ℚ) -
        sfinrank k (actionStepUDenominator A' A C U D) := by
  let N := actionStepUNumerator A' A C U D
  let P := actionStepUDenominator A' A C U D
  let Pn := actionStepUDenominatorInNumerator A' A C U D
  let π := actionStepUProjection A' A C U D
  let ψ := actionStepUQuotientMap A' A C U D a
  let B := actionStepKernel A' A C D a
  have hPN : P ≤ N := actionStepUDenominator_le_actionStepUNumerator A' A C hAA U D
  have hkerπ : LinearMap.ker π = Pn := by
    ext x
    rw [LinearMap.mem_ker]
    change P.mkQ (N.subtype x) = 0 ↔ x ∈ Pn
    change P.mkQ (N.subtype x) = 0 ↔ N.subtype x ∈ P
    exact Submodule.Quotient.mk_eq_zero P
  have hdimPn : finrank k Pn = finrank k P := by
    have himage : ambientImage N Pn = P := by
      change ambientImage N (P.comap N.subtype) = P
      exact ambientImage_comap_eq_of_le N P hPN
    rw [← himage, finrank_ambientImage]
  have hπrank := @LinearMap.finrank_range_add_finrank_ker
    k N _ (Submodule.addCommGroup N) _
    ((A.act C).carrier ⧸ P) _ _ _
    (actionStepUProjection A' A C U D)
  rw [hkerπ, hdimPn] at hπrank
  have hψsurj : Function.Surjective ψ :=
    actionStepUQuotientMap_surjective A' A C hAA U D ell a hker ha
  have hψrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hψsurj
  have hψrank := @LinearMap.finrank_range_add_finrank_ker
    k U _ (Submodule.addCommGroup U) _
    (actionStepUQuotientSpace A' A C U D)
      (Submodule.addCommGroup (actionStepUQuotientSpace A' A C U D)) _ _
    ψ
  rw [hψrange, finrank_top] at hψrank
  have hkerle : LinearMap.ker ψ ≤ B.comap U.subtype :=
    actionStepUQuotientMap_ker_le A' A C U D a
  have hkerdim : finrank k (LinearMap.ker ψ) ≤
      finrank k (B.comap U.subtype) := Submodule.finrank_mono hkerle
  have hinterImage : ambientImage U (B.comap U.subtype) = U ⊓ B := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hxU, hxB⟩
      exact ⟨⟨x, hxU⟩, hxB, rfl⟩
  have hinterDim : finrank k (B.comap U.subtype) =
      sfinrank k (U ⊓ B) := by
    rw [← hinterImage]
    simpa only [sfinrank] using
      (finrank_ambientImage U (B.comap U.subtype)).symm
  rw [hinterDim] at hkerdim
  have hπq : (finrank k (LinearMap.range π) : ℚ) + finrank k P =
      finrank k N := by exact_mod_cast hπrank
  have hψq : (finrank k (actionStepUQuotientSpace A' A C U D) : ℚ) +
      finrank k (LinearMap.ker ψ) = finrank k U := by
    exact_mod_cast hψrank
  have hkerq : (finrank k (LinearMap.ker ψ) : ℚ) ≤
      sfinrank k (U ⊓ B) := by
    exact_mod_cast hkerdim
  have hrangeEq : LinearMap.range π = actionStepUQuotientSpace A' A C U D := rfl
  rw [hrangeEq] at hπq
  change (finrank k U : ℚ) -
      sfinrank k (U ⊓ B) ≤
    (finrank k N : ℚ) - finrank k P
  linarith

/-- The transfer inequality for one codimension-one step in the acting
coalgebra. -/
theorem actionCodimOne_transfer_step
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1)
    (U : Submodule k C.carrier)
    (D : Submodule k (A.act C).carrier)
    (hD : IsSubcoalgebra (k := k) D) (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (finrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((finrank k (A.act C).carrier : ℚ) -
        sfinrank k (actionStepDenominator A' A C D)) ≤
      (sfinrank k (actionStepUNumerator A' A C U D) : ℚ) -
        sfinrank k (actionStepUDenominator A' A C U D) := by
  obtain ⟨ell, a, hker, ha⟩ :=
    exists_normalized_codimOne_functional A' A hAA hdim
  let B := actionStepKernel A' A C D a
  have hB : IsSubcoalgebra (k := k) B :=
    actionStepKernel_isSubcoalgebra A' A C hAA D hD ell a hker ha
  have hdimNat :=
    finrank_actionStepDenominator_difference A' A C D ell a hker ha
  have hQle : sfinrank k (actionStepDenominator A' A C D) ≤
      finrank k (A.act C).carrier := Submodule.finrank_le _
  have hBle : sfinrank k B ≤ finrank k C.carrier := Submodule.finrank_le _
  have hdimRat :
      (finrank k (A.act C).carrier : ℚ) -
          sfinrank k (actionStepDenominator A' A C D) =
        (finrank k C.carrier : ℚ) - sfinrank k B := by
    rw [← Nat.cast_sub hQle, ← Nat.cast_sub hBle]
    exact_mod_cast hdimNat
  have hU := finrank_actionStepU_difference_ge
    A' A C hAA U D ell a hker ha
  calc
    t * ((finrank k (A.act C).carrier : ℚ) -
          sfinrank k (actionStepDenominator A' A C D)) =
        t * ((finrank k C.carrier : ℚ) - sfinrank k B) := by rw [hdimRat]
    _ ≤ (finrank k U : ℚ) - sfinrank k (U ⊓ B) := hsem B hB
    _ ≤ (sfinrank k (actionStepUNumerator A' A C U D) : ℚ) -
          sfinrank k (actionStepUDenominator A' A C U D) := hU

end

end HopfAmenability
