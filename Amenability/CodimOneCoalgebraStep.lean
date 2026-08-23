/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.RightCoideal
import Amenability.CoefficientCoalgebra
import Amenability.SubcoalgebraAmbient
import Amenability.FiniteSubcoalgebraMul
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# A primal codimension-one coalgebra transfer step
-/

open Coalgebra Module TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/-- The copy of `A'` inside `A`. -/
def codimOneLower
    (A' A : FiniteSubcoalgebra k H) : Submodule k A.carrier :=
  A'.carrier.comap A.carrier.subtype

omit [Coalgebra.IsCocomm k H] in
/-- A normalized functional cutting out a codimension-one subcoalgebra. -/
theorem exists_normalized_codimOne_functional
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1) :
    ∃ (ell : A.carrier →ₗ[k] k) (a : A.carrier),
      LinearMap.ker ell = codimOneLower A' A ∧ ell a = 1 := by
  let L : Submodule k A.carrier := codimOneLower A' A
  have hLimage : ambientImage A.carrier L = A'.carrier :=
    ambientImage_comap_eq_of_le A.carrier A'.carrier hAA
  have hdimL : finrank k L = finrank k A'.carrier := by
    rw [← hLimage, finrank_ambientImage]
  have hquot : finrank k (A.carrier ⧸ L) = 1 := by
    have hq := L.finrank_quotient_add_finrank
    rw [hdimL, hdim] at hq
    omega
  let e : (A.carrier ⧸ L) ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hquot)
  let ell : A.carrier →ₗ[k] k := e.toLinearMap.comp L.mkQ
  have hellSurj : Function.Surjective ell :=
    e.surjective.comp L.mkQ_surjective
  obtain ⟨a, ha⟩ := hellSurj 1
  refine ⟨ell, a, ?_, ha⟩
  ext x
  constructor
  · intro hx
    change x ∈ L
    rw [LinearMap.mem_ker] at hx
    change e (L.mkQ x) = 0 at hx
    have hq : L.mkQ x = 0 :=
      e.injective (hx.trans e.map_zero.symm)
    rw [← L.ker_mkQ, LinearMap.mem_ker]
    exact hq
  · intro hx
    change x ∈ L at hx
    rw [LinearMap.mem_ker]
    have hq : L.mkQ x = 0 := by
      rw [← LinearMap.mem_ker, L.ker_mkQ]
      exact hx
    simp [ell, hq]

/-- The coefficient selected from the first tensor factor of `comul a`. -/
noncomputable def codimOneGroupLikeCandidate
    (A : FiniteSubcoalgebra k H)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier) : A.carrier :=
  TensorProduct.leftContract ell
    (Coalgebra.comul (R := k) (A := A.carrier) a)

omit [Coalgebra.IsCocomm k H] in
/-- Contraction by the normalized codimension-one functional has rank one. -/
theorem leftContract_comul_eq_smul_codimOneGroupLikeCandidate
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1)
    (x : A.carrier) :
    TensorProduct.leftContract ell
        (Coalgebra.comul (R := k) (A := A.carrier) x) =
      ell x • codimOneGroupLikeCandidate A ell a := by
  let L : Submodule k A.carrier := codimOneLower A' A
  have hLimage : ambientImage A.carrier L = A'.carrier :=
    ambientImage_comap_eq_of_le A.carrier A'.carrier hAA
  have hL : IsSubcoalgebra (k := k) L := by
    apply (isSubcoalgebra_ambientImage_iff A.carrier A.isSubcoalgebra L).1
    rw [hLimage]
    exact A'.isSubcoalgebra
  let f : A.carrier →ₗ[k] A.carrier :=
    (TensorProduct.leftContract ell).comp
      (Coalgebra.comul (R := k) (A := A.carrier))
  have hfL : ∀ y : A.carrier, y ∈ L → f y = 0 := by
    intro y hy
    have hellL : ∀ l : L, ell (l : A.carrier) = 0 := by
      intro l
      rw [← LinearMap.mem_ker, hker]
      exact l.2
    have hcontractZero : ∀ z : L ⊗[k] L,
        TensorProduct.leftContract ell (TensorProduct.mapIncl L L z) = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [hz, hw]
      | tmul l r => simp [TensorProduct.mapIncl, hellL]
    rcases hL hy with ⟨z, hz⟩
    change TensorProduct.leftContract ell
      (Coalgebra.comul (R := k) (A := A.carrier) y) = 0
    rw [← hz]
    exact hcontractZero z
  have hyker : x - (ell x) • a ∈ L := by
    change x - (ell x) • a ∈ codimOneLower A' A
    rw [← hker, LinearMap.mem_ker]
    simp [ha]
  have hzero := hfL (x - (ell x) • a) hyker
  change f x = ell x • f a
  rw [map_sub, map_smul] at hzero
  exact sub_eq_zero.mp hzero

omit [Coalgebra.IsCocomm k H] in
/-- The normalized coefficient selected from a codimension-one coalgebra step
is group-like in the internal coalgebra `A`. -/
theorem codimOneGroupLikeCandidate_isGroupLike
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    IsGroupLikeElem k (codimOneGroupLikeCandidate A ell a) := by
  let g : A.carrier := codimOneGroupLikeCandidate A ell a
  have hcounitNatural : ∀ z : A.carrier ⊗[k] A.carrier,
      Coalgebra.counit (R := k) (A := A.carrier)
          (TensorProduct.leftContract ell z) =
        ell (TensorProduct.rid k A.carrier
          ((Coalgebra.counit (R := k) (A := A.carrier)).lTensor A.carrier z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul x y => simp [mul_comm]
  have hgCounit : Coalgebra.counit (R := k) (A := A.carrier) g = 1 := by
    rw [show g = TensorProduct.leftContract ell
      (Coalgebra.comul (R := k) (A := A.carrier) a) from rfl,
      hcounitNatural]
    rw [Coalgebra.lTensor_counit_comul]
    simpa using ha
  have hcontractAssoc : ∀ (q : A.carrier ⊗[k] A.carrier) (y : A.carrier),
      TensorProduct.leftContract ell
          (TensorProduct.assoc k A.carrier A.carrier A.carrier
            (q ⊗ₜ[k] y)) =
        TensorProduct.leftContract ell q ⊗ₜ[k] y := by
    intro q y
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add q r hq hr => simp [hq, hr, add_tmul]
    | tmul x z => rfl
  have hleftEval : ∀ z : A.carrier ⊗[k] A.carrier,
      TensorProduct.leftContract ell
          (TensorProduct.assoc k A.carrier A.carrier A.carrier
            ((Coalgebra.comul (R := k) (A := A.carrier)).rTensor A.carrier z)) =
        g ⊗ₜ[k] TensorProduct.leftContract ell z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw, tmul_add]
    | tmul x y =>
        rw [LinearMap.rTensor_tmul, hcontractAssoc]
        rw [leftContract_comul_eq_smul_codimOneGroupLikeCandidate
          A' A hAA ell a hker ha x]
        simp [g, smul_tmul']
  have hrightEval : ∀ z : A.carrier ⊗[k] A.carrier,
      TensorProduct.leftContract ell
          ((Coalgebra.comul (R := k) (A := A.carrier)).lTensor A.carrier z) =
        Coalgebra.comul (R := k) (A := A.carrier)
          (TensorProduct.leftContract ell z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul x y => simp
  have hcoassoc := Coalgebra.coassoc_apply (R := k) (A := A.carrier) a
  have hcontract := congrArg
    (fun z : A.carrier ⊗[k] (A.carrier ⊗[k] A.carrier) =>
      TensorProduct.leftContract ell z) hcoassoc
  have hgComul : Coalgebra.comul (R := k) (A := A.carrier) g = g ⊗ₜ[k] g := by
    rw [hleftEval, hrightEval] at hcontract
    exact hcontract.symm
  exact ⟨hgCounit, hgComul⟩

omit [Coalgebra.IsCocomm k H] in
/-- The group-like coefficient remains group-like in the ambient Hopf algebra. -/
theorem codimOneGroupLikeCandidate_isGroupLike_ambient
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    IsGroupLikeElem k ((codimOneGroupLikeCandidate A ell a : A.carrier) : H) :=
  (codimOneGroupLikeCandidate_isGroupLike A' A hAA ell a hker ha).map
    (subcoalgebraInclusion A.carrier A.isSubcoalgebra)

/-- Ambient left multiplication by an element of the Hopf algebra. -/
def ambientLeftMul (g : H) : H →ₗ[k] H where
  toFun x := g * x
  map_add' x y := mul_add g x y
  map_smul' r x := by simp

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem ambientLeftMul_apply (g x : H) : ambientLeftMul (k := k) g x = g * x := rfl

omit [Coalgebra.IsCocomm k H] in
/-- Left multiplication by a group-like element is injective. -/
theorem ambientLeftMul_injective {g : H} (hg : IsGroupLikeElem k g) :
    Function.Injective (ambientLeftMul (k := k) g) := by
  intro x y hxy
  have hxy' : g * x = g * y := hxy
  calc
    x = 1 * x := by simp
    _ = (HopfAlgebra.antipode k g * g) * x := by rw [hg.antipode_mul_cancel]
    _ = HopfAlgebra.antipode k g * (g * x) := by rw [mul_assoc]
    _ = HopfAlgebra.antipode k g * (g * y) := by rw [hxy']
    _ = (HopfAlgebra.antipode k g * g) * y := by rw [mul_assoc]
    _ = 1 * y := by rw [hg.antipode_mul_cancel]
    _ = y := by simp

omit [Coalgebra.IsCocomm k H] in
/-- The error term in `comul a = a ⊗ g + r` has its first factor in `A'`. -/
theorem comul_sub_tmul_codimOneGroupLikeCandidate_mem
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Coalgebra.comul (R := k) (A := A.carrier) a -
        a ⊗ₜ[k] codimOneGroupLikeCandidate A ell a ∈
      LinearMap.range ((codimOneLower A' A).subtype.rTensor A.carrier) := by
  let g := codimOneGroupLikeCandidate A ell a
  let r := Coalgebra.comul (R := k) (A := A.carrier) a - a ⊗ₜ[k] g
  have hleftzero : TensorProduct.leftContract ell r = 0 := by
    dsimp [r]
    rw [map_sub, leftContract_comul_eq_smul_codimOneGroupLikeCandidate
      A' A hAA ell a hker ha a]
    simp [g, ha]
  let L : Submodule k A.carrier := codimOneLower A' A
  let p : A.carrier →ₗ[k] L := {
    toFun := fun x => ⟨x - ell x • a, by
      change x - ell x • a ∈ codimOneLower A' A
      rw [← hker, LinearMap.mem_ker]
      simp [ha]⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp [add_smul]
      abel
    map_smul' := by
      intro q x
      apply Subtype.ext
      simp [smul_sub, smul_smul] }
  have hdecomp : ∀ z : A.carrier ⊗[k] A.carrier,
      (L.subtype.rTensor A.carrier) (p.rTensor A.carrier z) +
          a ⊗ₜ[k] TensorProduct.leftContract ell z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw =>
      simp only [map_add, tmul_add]
      calc
        _ = ((L.subtype.rTensor A.carrier) (p.rTensor A.carrier z) +
              a ⊗ₜ[k] TensorProduct.leftContract ell z) +
            ((L.subtype.rTensor A.carrier) (p.rTensor A.carrier w) +
              a ⊗ₜ[k] TensorProduct.leftContract ell w) := by abel
        _ = z + w := congrArg₂ (· + ·) hz hw
    | tmul x y =>
        simp [p, TensorProduct.leftContract_tmul, sub_tmul, smul_tmul']
  change r ∈ LinearMap.range (L.subtype.rTensor A.carrier)
  refine ⟨p.rTensor A.carrier r, ?_⟩
  have hd := hdecomp r
  rw [hleftzero, tmul_zero, add_zero] at hd
  exact hd

namespace PrimalTransfer

/-- Multiplication restricted to `F ⊗ U`, defined independently of the
dual-transfer development. -/
noncomputable def leftProductMap
    (F C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    F.carrier ⊗[k] U →ₗ[k] (FiniteSubcoalgebra.mul F C).carrier :=
  (FiniteSubcoalgebra.mulCoalgHom F C).toLinearMap.comp
    (U.subtype.lTensor F.carrier)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem leftProductMap_tmul
    (F C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (f : F.carrier) (u : U) :
    leftProductMap F C U (f ⊗ₜ[k] u) =
      ⟨(f : H) * (u : H), Submodule.mul_mem_mul f.2 u.1.2⟩ := rfl

/-- The internal copy of the product `F U` inside `F C`. -/
noncomputable def leftProductSubspace
    (F C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    Submodule k (FiniteSubcoalgebra.mul F C).carrier :=
  LinearMap.range (leftProductMap F C U)

omit [Coalgebra.IsCocomm k H] in
theorem leftProductSubspace_mono
    (F C : FiniteSubcoalgebra k H) {U W : Submodule k C.carrier}
    (hUW : U ≤ W) :
    leftProductSubspace F C U ≤ leftProductSubspace F C W := by
  rintro x ⟨z, rfl⟩
  let inclusion : U →ₗ[k] W := U.subtype.codRestrict W (fun u => hUW u.2)
  refine ⟨(inclusion.lTensor F.carrier) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul f u => rfl

omit [Coalgebra.IsCocomm k H] in
theorem leftProductSubspace_top
    (F C : FiniteSubcoalgebra k H) :
    leftProductSubspace F C ⊤ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨z, rfl⟩ := FiniteSubcoalgebra.mulCoalgHom_surjective F C x
  refine ⟨(Submodule.topEquiv.symm.lTensor F.carrier) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul f c =>
      apply Subtype.ext
      rfl

/-- The internal copy of `A' C` inside `A C`. -/
noncomputable def lowerProductSubspace
    (A' A C : FiniteSubcoalgebra k H) :
    Submodule k (FiniteSubcoalgebra.mul A C).carrier :=
  (A'.carrier * C.carrier).comap
    (FiniteSubcoalgebra.mul A C).carrier.subtype

/-- The denominator used at a codimension-one step. -/
noncomputable def stepDenominator
    (A' A C : FiniteSubcoalgebra k H)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    Submodule k (FiniteSubcoalgebra.mul A C).carrier :=
  D ⊔ lowerProductSubspace A' A C

omit [Coalgebra.IsCocomm k H] in
/-- The internal copy of `A' C` is a subcoalgebra of `A C`. -/
theorem lowerProductSubspace_isSubcoalgebra
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) :
    IsSubcoalgebra (k := k) (lowerProductSubspace A' A C) := by
  let AC := FiniteSubcoalgebra.mul A C
  have hmul : A'.carrier * C.carrier ≤ A.carrier * C.carrier :=
    subcoalgebra_mul_mono hAA le_rfl
  apply (isSubcoalgebra_ambientImage_iff AC.carrier AC.isSubcoalgebra
    (lowerProductSubspace A' A C)).1
  rw [show ambientImage AC.carrier (lowerProductSubspace A' A C) =
      A'.carrier * C.carrier by
    unfold lowerProductSubspace
    exact ambientImage_comap_eq_of_le AC.carrier
      (A'.carrier * C.carrier) hmul]
  exact (FiniteSubcoalgebra.mul A' C).isSubcoalgebra

/-- Adding an internal subcoalgebra `D` preserves the subcoalgebra property
of the step denominator. -/
theorem stepDenominator_isSubcoalgebra
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (stepDenominator A' A C D) := by
  exact hD.sup (lowerProductSubspace_isSubcoalgebra A' A C hAA)

/-- Multiplication by the chosen complement vector, followed by the quotient
by `D + A'C`. -/
noncomputable def stepQuotientMap
    (A' A C : FiniteSubcoalgebra k H)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) :
    C.carrier →ₗ[k]
      (FiniteSubcoalgebra.mul A C).carrier ⧸ stepDenominator A' A C D :=
  (stepDenominator A' A C D).mkQ.comp
    (LinearMap.codRestrict (FiniteSubcoalgebra.mul A C).carrier
      ((LinearMap.mulLeft k (a : H)).comp C.carrier.subtype)
      (fun c => Submodule.mul_mem_mul a.2 c.2))

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem stepQuotientMap_apply
    (A' A C : FiniteSubcoalgebra k H)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) (c : C.carrier) :
    stepQuotientMap A' A C D a c =
      (stepDenominator A' A C D).mkQ
        ⟨(a : H) * (c : H), Submodule.mul_mem_mul a.2 c.2⟩ := by
  rfl

omit [Coalgebra.IsCocomm k H] in
theorem stepQuotientMap_surjective
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Function.Surjective (stepQuotientMap A' A C D a) := by
  let Q := stepDenominator A' A C D
  have hlower : ∀ x : A.carrier,
      x - ell x • a ∈ codimOneLower A' A := by
    intro x
    rw [← hker, LinearMap.mem_ker]
    simp [ha]
  have htmul : ∀ (x : A.carrier) (c : C.carrier),
      Q.mkQ (FiniteSubcoalgebra.mulCoalgHom A C (x ⊗ₜ[k] c)) =
        stepQuotientMap A' A C D a (ell x • c) := by
    intro x c
    rw [stepQuotientMap_apply]
    apply (Submodule.Quotient.eq Q).2
    change (⟨(x : H) * (c : H), Submodule.mul_mem_mul x.2 c.2⟩ :
        (FiniteSubcoalgebra.mul A C).carrier) -
      ⟨(a : H) * ((ell x • c : C.carrier) : H),
        Submodule.mul_mem_mul a.2 (ell x • c).2⟩ ∈ Q
    apply Submodule.mem_sup_right
    change (x : H) * (c : H) - (a : H) * (ell x • (c : H)) ∈
      A'.carrier * C.carrier
    have hp := Submodule.mul_mem_mul (hlower x) c.2
    convert hp using 1 <;> simp [sub_mul, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
  intro q
  obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
  obtain ⟨z, rfl⟩ := FiniteSubcoalgebra.mulCoalgHom_surjective A C x
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [stepQuotientMap]⟩
  | add z w hz hw =>
      rcases hz with ⟨c, hc⟩
      rcases hw with ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      rw [map_add, hc, hd, map_add, map_add]
  | tmul x c => exact ⟨ell x • c, (htmul x c).symm⟩

/-- The kernel subspace in `C` produced by the codimension-one quotient map. -/
noncomputable def stepKernel
    (A' A C : FiniteSubcoalgebra k H)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) : Submodule k C.carrier :=
  LinearMap.ker (stepQuotientMap A' A C D a)

/-- Internal multiplication by the group-like coefficient `g`. -/
noncomputable def groupLikeLeftProductMap
    (A C : FiniteSubcoalgebra k H) (g : A.carrier) :
    C.carrier →ₗ[k] (FiniteSubcoalgebra.mul A C).carrier :=
  LinearMap.codRestrict (FiniteSubcoalgebra.mul A C).carrier
    ((LinearMap.mulLeft k (g : H)).comp C.carrier.subtype)
    (fun c => Submodule.mul_mem_mul g.2 c.2)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem groupLikeLeftProductMap_apply
    (A C : FiniteSubcoalgebra k H) (g : A.carrier) (c : C.carrier) :
    groupLikeLeftProductMap A C g c =
      ⟨(g : H) * (c : H), Submodule.mul_mem_mul g.2 c.2⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
theorem groupLikeLeftProductMap_injective
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Function.Injective
      (groupLikeLeftProductMap A C (codimOneGroupLikeCandidate A ell a)) := by
  intro x y hxy
  apply Subtype.ext
  apply ambientLeftMul_injective
    (codimOneGroupLikeCandidate_isGroupLike_ambient
      A' A hAA ell a hker ha)
  exact congrArg (fun z : (FiniteSubcoalgebra.mul A C).carrier => (z : H)) hxy

/-- Pair the two legs of tensors in `A ⊗ A` and `C ⊗ C` by multiplication. -/
noncomputable def comulProductMap
    (A C : FiniteSubcoalgebra k H) :
    (A.carrier ⊗[k] A.carrier) ⊗[k] (C.carrier ⊗[k] C.carrier) →ₗ[k]
      (FiniteSubcoalgebra.mul A C).carrier ⊗[k]
        (FiniteSubcoalgebra.mul A C).carrier :=
  (TensorProduct.map
      (FiniteSubcoalgebra.mulCoalgHom A C).toLinearMap
      (FiniteSubcoalgebra.mulCoalgHom A C).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      k k k k A.carrier A.carrier C.carrier C.carrier).toLinearMap

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem comulProductMap_tmul_tmul
    (A C : FiniteSubcoalgebra k H)
    (x y : A.carrier) (c d : C.carrier) :
    comulProductMap A C ((x ⊗ₜ[k] y) ⊗ₜ[k] (c ⊗ₜ[k] d)) =
      FiniteSubcoalgebra.mulCoalgHom A C (x ⊗ₜ[k] c) ⊗ₜ[k]
        FiniteSubcoalgebra.mulCoalgHom A C (y ⊗ₜ[k] d) := rfl

omit [Coalgebra.IsCocomm k H] in
theorem comul_mul_internal
    (A C : FiniteSubcoalgebra k H) (a : A.carrier) (c : C.carrier) :
    Coalgebra.comul (R := k)
        (A := (FiniteSubcoalgebra.mul A C).carrier)
        (FiniteSubcoalgebra.mulCoalgHom A C (a ⊗ₜ[k] c)) =
      comulProductMap A C
        (Coalgebra.comul (R := k) (A := A.carrier) a ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c) := by
  rw [← CoalgHomClass.map_comp_comul_apply
    (FiniteSubcoalgebra.mulCoalgHom A C) (a ⊗ₜ[k] c)]
  rfl

omit [Coalgebra.IsCocomm k H] in
/-- After quotienting the first product leg, the error term in `Δa` dies
and the surviving second leg is multiplication by `g`. -/
theorem quotient_comul_mul_eq
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) (c : C.carrier) :
    ((stepDenominator A' A C D).mkQ.rTensor
        (FiniteSubcoalgebra.mul A C).carrier)
      (Coalgebra.comul (R := k)
        (A := (FiniteSubcoalgebra.mul A C).carrier)
        (FiniteSubcoalgebra.mulCoalgHom A C (a ⊗ₜ[k] c))) =
    ((groupLikeLeftProductMap A C
        (codimOneGroupLikeCandidate A ell a)).lTensor
          ((FiniteSubcoalgebra.mul A C).carrier ⧸
            stepDenominator A' A C D))
      ((stepQuotientMap A' A C D a).rTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) := by
  let AC := FiniteSubcoalgebra.mul A C
  let Q := stepDenominator A' A C D
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
        (comulProductMap A C
          (((codimOneLower A' A).subtype.rTensor A.carrier z) ⊗ₜ[k] w)) = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => intro w; simp
    | add z z' hz hz' => intro w; simp [hz w, hz' w, add_tmul]
    | tmul x y =>
      rw [LinearMap.rTensor_tmul]
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' =>
        simp only [tmul_add, map_add]
        have hz : (Q.mkQ.rTensor AC.carrier)
            (comulProductMap A C
              (((codimOneLower A' A).subtype x ⊗ₜ[k] y) ⊗ₜ[k] w)) = 0 := hw
        have hz' : (Q.mkQ.rTensor AC.carrier)
            (comulProductMap A C
              (((codimOneLower A' A).subtype x ⊗ₜ[k] y) ⊗ₜ[k] w')) = 0 := hw'
        rw [hz, hz', add_zero]
      | tmul c d =>
        have hprod : (⟨(x.1 : H) * (c : H),
            Submodule.mul_mem_mul (hAA (hlowerAmbient x)) c.2⟩ : AC.carrier) ∈ Q := by
          apply Submodule.mem_sup_right
          exact Submodule.mul_mem_mul (hlowerAmbient x) c.2
        rw [comulProductMap_tmul_tmul, LinearMap.rTensor_tmul]
        have hzero : Q.mkQ
            (FiniteSubcoalgebra.mulCoalgHom A C
              ((codimOneLower A' A).subtype x ⊗ₜ[k] c)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero Q).2
          exact hprod
        rw [hzero, zero_tmul]
  have hmain : ∀ w : C.carrier ⊗[k] C.carrier,
      (Q.mkQ.rTensor AC.carrier)
          (comulProductMap A C ((a ⊗ₜ[k] g) ⊗ₜ[k] w)) =
        ((groupLikeLeftProductMap A C g).lTensor (AC.carrier ⧸ Q))
          ((stepQuotientMap A' A C D a).rTensor C.carrier w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp [hw, hw', tmul_add]
    | tmul c d => rfl
  rw [comul_mul_internal]
  have hsplit : Coalgebra.comul (R := k) (A := A.carrier) a =
      a ⊗ₜ[k] g + r := by dsimp [r]; abel
  rw [hsplit, add_tmul, map_add, map_add]
  have hfirst := hmain (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond := herror r0 (Coalgebra.comul (R := k) (A := C.carrier) c)
  have hsecond' : (Q.mkQ.rTensor AC.carrier)
      (comulProductMap A C (r ⊗ₜ[k]
        Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [hr]
    exact hsecond
  change
    (Q.mkQ.rTensor AC.carrier)
        (comulProductMap A C ((a ⊗ₜ[k] g) ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) +
      (Q.mkQ.rTensor AC.carrier)
        (comulProductMap A C (r ⊗ₜ[k]
          Coalgebra.comul (R := k) (A := C.carrier) c)) = _
  rw [hfirst, hsecond', add_zero]

/-- The kernel of the codimension-one quotient map is a right coideal. -/
theorem stepKernel_isRightSubcomodule
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    IsRightSubcomodule (C := C.carrier) (stepKernel A' A C D a) := by
  let AC := FiniteSubcoalgebra.mul A C
  let Q := stepDenominator A' A C D
  let φ := stepQuotientMap A' A C D a
  let B := stepKernel A' A C D a
  let g := codimOneGroupLikeCandidate A ell a
  have hQ : IsSubcoalgebra (k := k) Q :=
    stepDenominator_isSubcoalgebra A' A C hAA D hD
  have hφsurj : Function.Surjective φ :=
    stepQuotientMap_surjective A' A C hAA D ell a hker ha
  have hginj : Function.Injective (groupLikeLeftProductMap A C g) :=
    groupLikeLeftProductMap_injective A' A C hAA ell a hker ha
  have hgtensorinj : Function.Injective
      ((groupLikeLeftProductMap A C g).lTensor (AC.carrier ⧸ Q)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hginj
  intro c hc
  have hφc : φ c = 0 := by
    change c ∈ LinearMap.ker φ at hc
    exact (LinearMap.mem_ker).1 hc
  have hacQ : FiniteSubcoalgebra.mulCoalgHom A C (a ⊗ₜ[k] c) ∈ Q := by
    change (⟨(a : H) * (c : H), Submodule.mul_mem_mul a.2 c.2⟩ :
      AC.carrier) ∈ Q
    apply (Submodule.Quotient.mk_eq_zero Q).1
    simpa [φ] using hφc
  have hquotComul : (Q.mkQ.rTensor AC.carrier)
      (Coalgebra.comul (R := k) (A := AC.carrier)
        (FiniteSubcoalgebra.mulCoalgHom A C (a ⊗ₜ[k] c))) = 0 := by
    rcases hQ hacQ with ⟨z, hz⟩
    have hzeroIncl : ∀ w : Q ⊗[k] Q,
        (Q.mkQ.rTensor AC.carrier) (TensorProduct.mapIncl Q Q w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [hz, hw]
      | tmul x y =>
        simp [TensorProduct.mapIncl,
          (Submodule.Quotient.mk_eq_zero Q).2 x.2]
    rw [← hz]
    exact hzeroIncl z
  have htwisted : ((groupLikeLeftProductMap A C g).lTensor (AC.carrier ⧸ Q))
      (φ.rTensor C.carrier
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [← quotient_comul_mul_eq A' A C hAA D ell a hker ha c]
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

/-- In the cocommutative coalgebra `C`, the kernel right coideal is a
subcoalgebra. -/
theorem stepKernel_isSubcoalgebra
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    IsSubcoalgebra (k := k) (stepKernel A' A C D a) :=
  isSubcoalgebra_of_isRightSubcomodule
    (stepKernel_isRightSubcomodule A' A C hAA D hD ell a hker ha)

omit [Coalgebra.IsCocomm k H] in
/-- The independently defined primal product subspace has its expected
ambient image. -/
theorem ambientImage_leftProductSubspace
    (F C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    ambientImage (FiniteSubcoalgebra.mul F C).carrier
        (leftProductSubspace F C U) =
      F.carrier * ambientImage C.carrier U := by
  let e := ambientImageEquiv C.carrier U
  have hmap : ∀ z : F.carrier ⊗[k] U,
      (((leftProductMap F C U z :
          (FiniteSubcoalgebra.mul F C).carrier) : H)) =
        Submodule.mulMap' F.carrier (ambientImage C.carrier U)
          (TensorProduct.map LinearMap.id e.toLinearMap z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y => rfl
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    rw [← Submodule.mulMap_range]
    exact ⟨TensorProduct.map LinearMap.id e.toLinearMap z, (hmap z).symm⟩
  · intro hx
    rw [← Submodule.mulMap_range] at hx
    rcases hx with ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ :=
      (TensorProduct.map_bijective
        (f := LinearMap.id) (g := e.toLinearMap)
        Function.bijective_id e.bijective).2 z
    refine ⟨leftProductMap F C U z', ⟨z', rfl⟩, ?_⟩
    change (((leftProductMap F C U z' :
      (FiniteSubcoalgebra.mul F C).carrier) : H)) =
        Submodule.mulMap' F.carrier (ambientImage C.carrier U) z
    rw [hmap, hz']

/-- The internal copy of `A' U` in `A C`. -/
noncomputable def lowerUSubspace
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    Submodule k (FiniteSubcoalgebra.mul A C).carrier :=
  (A'.carrier * ambientImage C.carrier U).comap
    (FiniteSubcoalgebra.mul A C).carrier.subtype

omit [Coalgebra.IsCocomm k H] in
theorem lowerUSubspace_le_upper
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier) :
    lowerUSubspace A' A C U ≤ leftProductSubspace A C U := by
  let AC := FiniteSubcoalgebra.mul A C
  have hUambient : ambientImage C.carrier U ≤ C.carrier := by
    rintro x ⟨u, -, rfl⟩
    exact u.2
  have hlower : A'.carrier * ambientImage C.carrier U ≤ AC.carrier :=
    (subcoalgebra_mul_mono hAA le_rfl).trans
      (subcoalgebra_mul_mono le_rfl hUambient)
  have himage : ambientImage AC.carrier (lowerUSubspace A' A C U) =
      A'.carrier * ambientImage C.carrier U := by
    unfold lowerUSubspace
    exact ambientImage_comap_eq_of_le AC.carrier _ hlower
  intro x hx
  have hxamb : (x : H) ∈
      ambientImage AC.carrier (lowerUSubspace A' A C U) := ⟨x, hx, rfl⟩
  rw [himage] at hxamb
  have hxupper : (x : H) ∈
      A.carrier * ambientImage C.carrier U :=
    subcoalgebra_mul_mono hAA le_rfl hxamb
  rw [← ambientImage_leftProductSubspace A C U] at hxupper
  rcases hxupper with ⟨y, hy, hyx⟩
  have : y = x := Subtype.ext hyx
  simpa [this] using hy

/-- The `U`-side numerator `D + AU`. -/
noncomputable def stepUNumerator
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    Submodule k (FiniteSubcoalgebra.mul A C).carrier :=
  D ⊔ leftProductSubspace A C U

/-- The `U`-side denominator `D + A'U`. -/
noncomputable def stepUDenominator
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    Submodule k (FiniteSubcoalgebra.mul A C).carrier :=
  D ⊔ lowerUSubspace A' A C U

omit [Coalgebra.IsCocomm k H] in
theorem stepUDenominator_le_stepUNumerator
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    stepUDenominator A' A C U D ≤ stepUNumerator A' A C U D :=
  sup_le_sup_left (lowerUSubspace_le_upper A' A C hAA U) D

/-- The copy of the `U`-denominator inside the `U`-numerator. -/
noncomputable def stepUDenominatorInNumerator
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    Submodule k (stepUNumerator A' A C U D) :=
  (stepUDenominator A' A C U D).comap
    (stepUNumerator A' A C U D).subtype

/-- The projection of `D + AU` to the ambient quotient by `D + A'U`. Its
range is canonically the desired quotient. -/
noncomputable def stepUProjection
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :
    stepUNumerator A' A C U D →ₗ[k]
      (FiniteSubcoalgebra.mul A C).carrier ⧸ stepUDenominator A' A C U D :=
  (stepUDenominator A' A C U D).mkQ.comp
    (stepUNumerator A' A C U D).subtype

/-- A concrete model of `(D + AU)/(D + A'U)`. -/
abbrev stepUQuotientSpace
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier) :=
  LinearMap.range (stepUProjection A' A C U D)

/-- Multiplication by `a` restricted to `U`. -/
noncomputable def stepUProductMap
    (A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (a : A.carrier) :
    U →ₗ[k] (FiniteSubcoalgebra.mul A C).carrier :=
  LinearMap.codRestrict (FiniteSubcoalgebra.mul A C).carrier
    ((LinearMap.mulLeft k (a : H)).comp
      (C.carrier.subtype.comp U.subtype))
    (fun u => Submodule.mul_mem_mul a.2 u.1.2)

/-- The second quotient map, sending `u` to the class of `a u` in
`(D + AU)/(D + A'U)`. -/
noncomputable def stepUQuotientMap
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) :
    U →ₗ[k] stepUQuotientSpace A' A C U D :=
  LinearMap.codRestrict (stepUQuotientSpace A' A C U D)
    ((stepUDenominator A' A C U D).mkQ.comp
      (stepUProductMap A C U a))
    (fun u => ⟨⟨stepUProductMap A C U a u,
      Submodule.mem_sup_right ⟨a ⊗ₜ[k] u, rfl⟩⟩, rfl⟩)

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem stepUQuotientMap_apply
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) (u : U) :
    stepUQuotientMap A' A C U D a u =
      ⟨(stepUDenominator A' A C U D).mkQ
          (stepUProductMap A C U a u),
        ⟨⟨stepUProductMap A C U a u,
          Submodule.mem_sup_right ⟨a ⊗ₜ[k] u, rfl⟩⟩, rfl⟩⟩ := rfl

omit [Coalgebra.IsCocomm k H] in
theorem stepUQuotientMap_surjective
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    Function.Surjective (stepUQuotientMap A' A C U D a) := by
  let Q := stepUDenominator A' A C U D
  have hlower : ∀ x : A.carrier,
      x - ell x • a ∈ codimOneLower A' A := by
    intro x
    rw [← hker, LinearMap.mem_ker]
    simp [ha]
  have htensor : ∀ z : A.carrier ⊗[k] U,
      ∃ u : U, Q.mkQ (leftProductMap A C U z) =
        Q.mkQ (stepUProductMap A C U a u) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add z w hz hw =>
      rcases hz with ⟨u, hu⟩
      rcases hw with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      simp only [map_add]
      exact congrArg₂ (· + ·) hu hv
    | tmul x u =>
      refine ⟨ell x • u, ?_⟩
      apply (Submodule.Quotient.eq Q).2
      change leftProductMap A C U (x ⊗ₜ[k] u) -
          stepUProductMap A C U a (ell x • u) ∈ Q
      apply Submodule.mem_sup_right
      change (x : H) * (u : H) -
          (a : H) * (ell x • (u : H)) ∈
        A'.carrier * ambientImage C.carrier U
      have hp := Submodule.mul_mem_mul (hlower x)
        (show (u : H) ∈ ambientImage C.carrier U from ⟨u, u.2, rfl⟩)
      convert hp using 1 <;> simp [sub_mul, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm]
  intro q
  rcases q.2 with ⟨x, hx⟩
  rcases (Submodule.mem_sup.1 x.2) with ⟨d, hd, w, hw, hdw⟩
  rcases hw with ⟨z, hz⟩
  rcases htensor z with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change Q.mkQ (stepUProductMap A C U a u) = q.1
  rw [← hx]
  change Q.mkQ (stepUProductMap A C U a u) = Q.mkQ x.1
  rw [← hdw, map_add, show Q.mkQ d = 0 by
    exact (Submodule.Quotient.mk_eq_zero Q).2 (Submodule.mem_sup_left hd),
    zero_add]
  exact hu.symm.trans (congrArg Q.mkQ hz)

omit [Coalgebra.IsCocomm k H] in
theorem lowerUSubspace_le_lowerProductSubspace
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    lowerUSubspace A' A C U ≤ lowerProductSubspace A' A C := by
  intro x hx
  change (x.1 : H) ∈ A'.carrier * C.carrier
  change (x.1 : H) ∈ A'.carrier * ambientImage C.carrier U at hx
  apply subcoalgebra_mul_mono le_rfl _ hx
  rintro y ⟨u, -, rfl⟩
  exact u.2

omit [Coalgebra.IsCocomm k H] in
theorem stepUQuotientMap_ker_le
    (A' A C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (a : A.carrier) :
    LinearMap.ker (stepUQuotientMap A' A C U D a) ≤
      (stepKernel A' A C D a).comap U.subtype := by
  intro u hu
  have hzero : (stepUDenominator A' A C U D).mkQ
      (stepUProductMap A C U a u) = 0 := by
    have hz := (LinearMap.mem_ker.1 hu)
    exact congrArg Subtype.val hz
  have hmemU : stepUProductMap A C U a u ∈
      stepUDenominator A' A C U D :=
    (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hmem : stepUProductMap A C U a u ∈
      stepDenominator A' A C D := by
    rcases (Submodule.mem_sup.1 hmemU) with ⟨d, hd, w, hw, hdw⟩
    rw [← hdw]
    exact add_mem (Submodule.mem_sup_left hd)
      (Submodule.mem_sup_right
        (lowerUSubspace_le_lowerProductSubspace A' A C U hw))
  change U.subtype u ∈ LinearMap.ker (stepQuotientMap A' A C D a)
  rw [LinearMap.mem_ker, stepQuotientMap_apply]
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact hmem

omit [Coalgebra.IsCocomm k H] in
/-- The gain on the `U` side dominates the codimension of the intersection
with the step kernel. -/
theorem finrank_stepU_difference_ge
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    (finrank k U : ℚ) -
        finrank k (U ⊓ stepKernel A' A C D a : Submodule k C.carrier) ≤
      (finrank k (stepUNumerator A' A C U D) : ℚ) -
        finrank k (stepUDenominator A' A C U D) := by
  let N := stepUNumerator A' A C U D
  let P := stepUDenominator A' A C U D
  let Pn := stepUDenominatorInNumerator A' A C U D
  let π := stepUProjection A' A C U D
  let ψ := stepUQuotientMap A' A C U D a
  let B := stepKernel A' A C D a
  have hPN : P ≤ N := stepUDenominator_le_stepUNumerator A' A C hAA U D
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
    ((FiniteSubcoalgebra.mul A C).carrier ⧸ P) _ _ _
    (stepUProjection A' A C U D)
  rw [hkerπ, hdimPn] at hπrank
  have hψsurj : Function.Surjective ψ :=
    stepUQuotientMap_surjective A' A C hAA U D ell a hker ha
  have hψrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hψsurj
  have hψrank := @LinearMap.finrank_range_add_finrank_ker
    k U _ (Submodule.addCommGroup U) _
    (stepUQuotientSpace A' A C U D)
      (Submodule.addCommGroup (stepUQuotientSpace A' A C U D)) _ _
    ψ
  rw [hψrange, finrank_top] at hψrank
  have hkerle : LinearMap.ker ψ ≤ B.comap U.subtype :=
    stepUQuotientMap_ker_le A' A C U D a
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
      finrank k (U ⊓ B : Submodule k C.carrier) := by
    rw [← hinterImage, finrank_ambientImage]
  rw [hinterDim] at hkerdim
  have hπq : (finrank k (LinearMap.range π) : ℚ) + finrank k P =
      finrank k N := by exact_mod_cast hπrank
  have hψq : (finrank k (stepUQuotientSpace A' A C U D) : ℚ) +
      finrank k (LinearMap.ker ψ) = finrank k U := by
    exact_mod_cast hψrank
  have hkerq : (finrank k (LinearMap.ker ψ) : ℚ) ≤
      finrank k (U ⊓ B : Submodule k C.carrier) := by
    exact_mod_cast hkerdim
  have hrangeEq : LinearMap.range π = stepUQuotientSpace A' A C U D := rfl
  rw [hrangeEq] at hπq
  change (finrank k U : ℚ) -
      finrank k (U ⊓ B : Submodule k C.carrier) ≤
    (finrank k N : ℚ) - finrank k P
  linarith

omit [Coalgebra.IsCocomm k H] in
/-- Rank-nullity for the first quotient map. -/
theorem finrank_stepDenominator_difference
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1) :
    finrank k (FiniteSubcoalgebra.mul A C).carrier -
        finrank k (stepDenominator A' A C D) =
      finrank k C.carrier - finrank k (stepKernel A' A C D a) := by
  let φ := stepQuotientMap A' A C D a
  let Q := stepDenominator A' A C D
  have hsurj : Function.Surjective φ :=
    stepQuotientMap_surjective A' A C hAA D ell a hker ha
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hφ := LinearMap.finrank_range_add_finrank_ker φ
  have hQ := Q.finrank_quotient_add_finrank
  rw [hrange, finrank_top] at hφ
  change finrank k (FiniteSubcoalgebra.mul A C).carrier - finrank k Q =
    finrank k C.carrier - finrank k (LinearMap.ker φ)
  have hleft : finrank k (FiniteSubcoalgebra.mul A C).carrier - finrank k Q =
      finrank k ((FiniteSubcoalgebra.mul A C).carrier ⧸ Q) := by
    rw [← hQ]
    exact Nat.add_sub_cancel_right _ _
  have hright : finrank k C.carrier - finrank k (LinearMap.ker φ) =
      finrank k ((FiniteSubcoalgebra.mul A C).carrier ⧸ Q) := by
    rw [← hφ]
    exact Nat.add_sub_cancel_right _ _
  exact hleft.trans hright.symm

/-- The primal transfer inequality for one codimension-one subcoalgebra
step. -/
theorem codimOne_transfer_step
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1)
    (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - finrank k B) ≤
        (finrank k U : ℚ) -
          finrank k (U ⊓ B : Submodule k C.carrier)) :
    t * ((finrank k (FiniteSubcoalgebra.mul A C).carrier : ℚ) -
        finrank k (stepDenominator A' A C D)) ≤
      (finrank k (stepUNumerator A' A C U D) : ℚ) -
        finrank k (stepUDenominator A' A C U D) := by
  obtain ⟨ell, a, hker, ha⟩ :=
    exists_normalized_codimOne_functional A' A hAA hdim
  let B := stepKernel A' A C D a
  have hB : IsSubcoalgebra (k := k) B :=
    stepKernel_isSubcoalgebra A' A C hAA D hD ell a hker ha
  have hdimNat :=
    finrank_stepDenominator_difference A' A C hAA D ell a hker ha
  have hQle : finrank k (stepDenominator A' A C D) ≤
      finrank k (FiniteSubcoalgebra.mul A C).carrier := by
    simpa using Submodule.finrank_mono
      (show stepDenominator A' A C D ≤
        (⊤ : Submodule k (FiniteSubcoalgebra.mul A C).carrier) from le_top)
  have hBle : finrank k B ≤ finrank k C.carrier :=
    by
      simpa using Submodule.finrank_mono
        (show B ≤ (⊤ : Submodule k C.carrier) from le_top)
  have hdimRat :
      (finrank k (FiniteSubcoalgebra.mul A C).carrier : ℚ) -
          finrank k (stepDenominator A' A C D) =
        (finrank k C.carrier : ℚ) - finrank k B := by
    rw [← Nat.cast_sub hQle, ← Nat.cast_sub hBle]
    exact_mod_cast hdimNat
  have hU := finrank_stepU_difference_ge
    A' A C hAA U D ell a hker ha
  calc
    t * ((finrank k (FiniteSubcoalgebra.mul A C).carrier : ℚ) -
          finrank k (stepDenominator A' A C D)) =
        t * ((finrank k C.carrier : ℚ) - finrank k B) := by rw [hdimRat]
    _ ≤ (finrank k U : ℚ) -
          finrank k (U ⊓ B : Submodule k C.carrier) := hsem B hB
    _ ≤ (finrank k (stepUNumerator A' A C U D) : ℚ) -
          finrank k (stepUDenominator A' A C U D) := hU

end PrimalTransfer

end

end UnifiedRounding
