/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.LieExpansion
import Amenability.TwoSidedCoideal
import Amenability.SubcoalgebraAmbient
import Amenability.FiniteSubcoalgebra
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The codimension-one transfer step for Lie-module coalgebras
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k]
variable [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
variable [Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M]

/-- The copy of `F'` inside a containing subspace `F`. -/
def lieCodimOneLower (F' F : Submodule k L) : Submodule k F :=
  F'.comap F.subtype

/-- A normalized functional cutting out a codimension-one inclusion of
finite-dimensional subspaces. -/
theorem exists_normalized_lieCodimOne_functional
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F)
    (hdim : sfinrank k F = sfinrank k F' + 1) :
    ∃ (ell : F →ₗ[k] k) (x : F),
      LinearMap.ker ell = lieCodimOneLower F' F ∧ ell x = 1 := by
  let P : Submodule k F := lieCodimOneLower F' F
  have hPimage : ambientImage F P = F' :=
    ambientImage_comap_eq_of_le F F' hFF
  have hdimP : finrank k P = finrank k F' := by
    rw [← hPimage, finrank_ambientImage]
  have hquot : finrank k (F ⧸ P) = 1 := by
    have hq := P.finrank_quotient_add_finrank
    change finrank k (F ⧸ P) + finrank k P = finrank k F at hq
    rw [hdimP] at hq
    change finrank k F = finrank k F' + 1 at hdim
    omega
  let e : (F ⧸ P) ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hquot)
  let ell : F →ₗ[k] k := e.toLinearMap.comp P.mkQ
  have hellSurj : Function.Surjective ell :=
    e.surjective.comp P.mkQ_surjective
  obtain ⟨x, hx⟩ := hellSurj 1
  refine ⟨ell, x, ?_, hx⟩
  ext y
  constructor
  · intro hy
    change y ∈ P
    rw [LinearMap.mem_ker] at hy
    change e (P.mkQ y) = 0 at hy
    have hq : P.mkQ y = 0 :=
      e.injective (hy.trans e.map_zero.symm)
    rw [← P.ker_mkQ, LinearMap.mem_ker]
    exact hq
  · intro hy
    change y ∈ P at hy
    rw [LinearMap.mem_ker]
    have hq : P.mkQ y = 0 := by
      rw [← LinearMap.mem_ker, P.ker_mkQ]
      exact hy
    simp [ell, hq]

/-- Projection along a normalized codimension-one complement lands in the
lower subspace. -/
theorem sub_smul_mem_lieCodimOneLower
    (F' F : Submodule k L)
    (ell : F →ₗ[k] k) (x y : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (hx : ell x = 1) :
    y - ell y • x ∈ lieCodimOneLower F' F := by
  rw [← hker, LinearMap.mem_ker]
  simp [hx]

/-- A normalized complement spans the codimension-one extension. -/
theorem le_sup_span_of_normalized_lieCodimOne
    (F' F : Submodule k L)
    (ell : F →ₗ[k] k) (x : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (hx : ell x = 1) :
    F ≤ F' ⊔ k ∙ (x : L) := by
  intro y hy
  let yF : F := ⟨y, hy⟩
  let p : F := yF - ell yF • x
  have hp : p ∈ lieCodimOneLower F' F :=
    sub_smul_mem_lieCodimOneLower F' F ell x yF hker hx
  apply Submodule.mem_sup.2
  refine ⟨(p : L), hp, ell yF • (x : L), ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (x : L))
  · simp [p, yF]

/-- The internal copy of the lower Lie expansion in the upper expansion. -/
def lieLowerExpansionSubspace
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) :
    Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier :=
  (lieExpansion F' C.carrier).comap
    (lieExpansionFiniteSubcoalgebra F C).carrier.subtype

theorem ambientImage_lieLowerExpansionSubspace
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M) :
    ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
        (lieLowerExpansionSubspace F' F C) =
      lieExpansion F' C.carrier := by
  apply ambientImage_comap_eq_of_le
  exact lieExpansion_mono_left hFF C.carrier

theorem lieLowerExpansionSubspace_isSubcoalgebra
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M) :
    IsSubcoalgebra (k := k) (lieLowerExpansionSubspace F' F C) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  apply (isSubcoalgebra_ambientImage_iff A.carrier A.isSubcoalgebra
    (lieLowerExpansionSubspace F' F C)).mp
  rw [ambientImage_lieLowerExpansionSubspace F' F hFF C]
  exact C.isSubcoalgebra.lieExpansion F'

/-- The denominator `D + F'⁺C` inside `F⁺C`. -/
def lieStepDenominator
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier :=
  D ⊔ lieLowerExpansionSubspace F' F C

theorem lieStepDenominator_isSubcoalgebra
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (lieStepDenominator F' F C D) := by
  exact hD.sup (lieLowerExpansionSubspace_isSubcoalgebra F' F hFF C)

/-- Action by a member of `F`, with codomain restricted to `F⁺C`. -/
def lieStepActionMap
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (a : F) :
    C.carrier →ₗ[k] (lieExpansionFiniteSubcoalgebra F C).carrier :=
  LinearMap.codRestrict (lieExpansionFiniteSubcoalgebra F C).carrier
    ((LieModule.toEnd k L M (a : L)).comp C.carrier.subtype)
    (fun c => lieActionSubspace_le_lieExpansion F C.carrier
      (lie_mem_lieActionSubspace a.2 c.2))

/-- Inclusion of `C` into its Lie expansion. -/
def lieStepInclusionMap
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) :
    C.carrier →ₗ[k] (lieExpansionFiniteSubcoalgebra F C).carrier :=
  LinearMap.codRestrict (lieExpansionFiniteSubcoalgebra F C).carrier
    C.carrier.subtype (fun c => le_lieExpansion F C.carrier c.2)

@[simp]
theorem lieStepActionMap_apply
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (a : F) (c : C.carrier) :
    (lieStepActionMap F C a c : M) = ⁅(a : L), (c : M)⁆ := rfl

@[simp]
theorem lieStepInclusionMap_apply
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (c : C.carrier) :
    (lieStepInclusionMap F C c : M) = (c : M) := rfl

/-- Internal form of the coderivation identity in `F⁺C`. -/
theorem lieStep_comul_action
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (a : F) (c : C.carrier) :
    Coalgebra.comul (R := k)
        (A := (lieExpansionFiniteSubcoalgebra F C).carrier)
        (lieStepActionMap F C a c) =
      TensorProduct.map (lieStepActionMap F C a)
          (lieStepInclusionMap F C)
          (Coalgebra.comul (R := k) (A := C.carrier) c) +
        TensorProduct.map (lieStepInclusionMap F C)
          (lieStepActionMap F C a)
          (Coalgebra.comul (R := k) (A := C.carrier) c) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  apply tensorProduct_mapIncl_injective A.carrier A.carrier
  change TensorProduct.mapIncl A.carrier A.carrier
      (subcoalgebraComul A.carrier A.isSubcoalgebra
        (lieStepActionMap F C a c)) = _
  rw [map_add, mapIncl_subcoalgebraComul A.carrier A.isSubcoalgebra]
  change Coalgebra.comul (R := k) (A := M) ⁅(a : L), (c : M)⁆ = _
  rw [Coalgebra.comul_lie_apply,
    ← mapIncl_subcoalgebraComul C.carrier C.isSubcoalgebra]
  congr 1
  · induction Coalgebra.comul (R := k) (A := C.carrier) c using
        TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
    | tmul x y => rfl
  · induction Coalgebra.comul (R := k) (A := C.carrier) c using
        TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
    | tmul x y => rfl

/-- Action by the chosen complement, followed by the denominator quotient. -/
def lieStepQuotientMap
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) :
    C.carrier →ₗ[k]
      (lieExpansionFiniteSubcoalgebra F C).carrier ⧸
        lieStepDenominator F' F C D :=
  (lieStepDenominator F' F C D).mkQ.comp
    (lieStepActionMap F C a)

@[simp]
theorem lieStepQuotientMap_apply
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) (c : C.carrier) :
    lieStepQuotientMap F' F C D a c =
      (lieStepDenominator F' F C D).mkQ
        ⟨⁅(a : L), (c : M)⁆,
          lieActionSubspace_le_lieExpansion F C.carrier
            (lie_mem_lieActionSubspace a.2 c.2)⟩ := rfl

theorem lieStepQuotientMap_surjective
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (_hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    Function.Surjective (lieStepQuotientMap F' F C D a) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  let Q := lieStepDenominator F' F C D
  let φ := lieStepQuotientMap F' F C D a
  let action : F ⊗[k] C.carrier →ₗ[k] A.carrier :=
    LinearMap.codRestrict A.carrier (lieActionMap F C.carrier)
      (fun z => lieActionSubspace_le_lieExpansion F C.carrier ⟨z, rfl⟩)
  have hCmem : ∀ c : C.carrier,
      (⟨(c : M), le_lieExpansion F C.carrier c.2⟩ : A.carrier) ∈ Q := by
    intro c
    apply Submodule.mem_sup_right
    change (c : M) ∈ lieExpansion F' C.carrier
    exact le_lieExpansion F' C.carrier c.2
  have haction : ∀ z : F ⊗[k] C.carrier,
      ∃ c : C.carrier, Q.mkQ (action z) = φ c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
    | add z w hz hw =>
        rcases hz with ⟨c, hc⟩
        rcases hw with ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        rw [map_add, map_add, hc, hd]
        exact (map_add φ c d).symm
    | tmul x c =>
        refine ⟨ell x • c, ?_⟩
        rw [lieStepQuotientMap_apply]
        apply (Submodule.Quotient.eq Q).2
        change (action (x ⊗ₜ[k] c) : A.carrier) -
          ⟨⁅(a : L), ((ell x • c : C.carrier) : M)⁆,
            lieActionSubspace_le_lieExpansion F C.carrier
              (lie_mem_lieActionSubspace a.2 (ell x • c).2)⟩ ∈ Q
        apply Submodule.mem_sup_right
        change ⁅(x : L), (c : M)⁆ - ⁅(a : L), ell x • (c : M)⁆ ∈
          lieExpansion F' C.carrier
        have hp := sub_smul_mem_lieCodimOneLower F' F ell a x hker ha
        have hlie : ⁅((x - ell x • a : F) : L), (c : M)⁆ ∈
            lieActionSubspace F' C.carrier :=
          lie_mem_lieActionSubspace hp c.2
        apply lieActionSubspace_le_lieExpansion F' C.carrier
        simpa using hlie
  intro q
  obtain ⟨y, rfl⟩ := Q.mkQ_surjective q
  rcases Submodule.mem_sup.1 y.2 with ⟨c, hc, v, hv, hyv⟩
  rcases hv with ⟨z, hz⟩
  rcases haction z with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  change φ d = Q.mkQ y
  rw [← hd]
  let cA : A.carrier := ⟨c, le_lieExpansion F C.carrier hc⟩
  have hcQ : cA ∈ Q := hCmem ⟨c, hc⟩
  have hcZero : Q.mkQ cA = 0 :=
    (Submodule.Quotient.mk_eq_zero Q).2 hcQ
  have hyA : y = cA + action z := by
    apply Subtype.ext
    change (y : M) = c + lieActionMap F C.carrier z
    exact hyv.symm.trans (congrArg (c + ·) hz.symm)
  calc
    Q.mkQ (action z) = 0 + Q.mkQ (action z) := by rw [zero_add]
    _ = Q.mkQ cA + Q.mkQ (action z) := by
      rw [hcZero]
    _ = Q.mkQ (cA + action z) := (map_add Q.mkQ cA (action z)).symm
    _ = Q.mkQ y := congrArg Q.mkQ hyA.symm

/-- The kernel produced by the codimension-one quotient map. -/
def lieStepKernel
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) : Submodule k C.carrier :=
  LinearMap.ker (lieStepQuotientMap F' F C D a)

/-- Rank-nullity for the denominator quotient. -/
theorem finrank_lieStepDenominator_difference
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    finrank k (lieExpansionFiniteSubcoalgebra F C).carrier -
        sfinrank k (lieStepDenominator F' F C D) =
      finrank k C.carrier - sfinrank k (lieStepKernel F' F C D a) := by
  let φ := lieStepQuotientMap F' F C D a
  let Q := lieStepDenominator F' F C D
  have hsurj : Function.Surjective φ :=
    lieStepQuotientMap_surjective F' F hFF C D ell a hker ha
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hφ := LinearMap.finrank_range_add_finrank_ker φ
  have hQ := Q.finrank_quotient_add_finrank
  rw [hrange, finrank_top] at hφ
  change finrank k (lieExpansionFiniteSubcoalgebra F C).carrier - finrank k Q =
    finrank k C.carrier - finrank k (LinearMap.ker φ)
  have hleft : finrank k (lieExpansionFiniteSubcoalgebra F C).carrier -
      finrank k Q =
      finrank k ((lieExpansionFiniteSubcoalgebra F C).carrier ⧸ Q) := by
    rw [← hQ]
    exact Nat.add_sub_cancel_right _ _
  have hright : finrank k C.carrier - finrank k (LinearMap.ker φ) =
      finrank k ((lieExpansionFiniteSubcoalgebra F C).carrier ⧸ Q) := by
    rw [← hφ]
    exact Nat.add_sub_cancel_right _ _
  exact hleft.trans hright.symm

/-- The kernel of the Lie quotient map is a right coideal of `C`. -/
theorem lieStepKernel_isRightCoideal
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    Coalgebra.IsRightCoideal (lieStepKernel F' F C D a) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  let Q := lieStepDenominator F' F C D
  let φ := lieStepQuotientMap F' F C D a
  let B := lieStepKernel F' F C D a
  let act := lieStepActionMap F C a
  let inc := lieStepInclusionMap F C
  have hQ : IsSubcoalgebra (k := k) Q :=
    lieStepDenominator_isSubcoalgebra F' F hFF C D hD
  have hφsurj : Function.Surjective φ :=
    lieStepQuotientMap_surjective F' F hFF C D ell a hker ha
  have hincinj : Function.Injective inc := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : A.carrier => (z : M)) hxy)
  have hinctensor : Function.Injective (inc.lTensor (A.carrier ⧸ Q)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hincinj
  intro c hc
  have hφc : φ c = 0 := (LinearMap.mem_ker).1 hc
  have hactQ : act c ∈ Q := by
    apply (Submodule.Quotient.mk_eq_zero Q).1
    exact hφc
  have hcomulZero : (Q.mkQ.rTensor A.carrier)
      (Coalgebra.comul (R := k) (A := A.carrier) (act c)) = 0 := by
    rcases hQ hactQ with ⟨z, hz⟩
    have hkill : ∀ w : Q ⊗[k] Q,
        (Q.mkQ.rTensor A.carrier) (TensorProduct.mapIncl Q Q w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
      | tmul x y =>
          change Q.mkQ x ⊗ₜ[k] (y : A.carrier) = 0
          have hxzero : Q.mkQ (x : A.carrier) = 0 :=
            (Submodule.Quotient.mk_eq_zero Q).2 x.2
          rw [hxzero, zero_tmul]
    rw [← hz]
    exact hkill z
  have hincQ : ∀ x : C.carrier, Q.mkQ (inc x) = 0 := by
    intro x
    apply (Submodule.Quotient.mk_eq_zero Q).2
    apply Submodule.mem_sup_right
    exact le_lieExpansion F' C.carrier x.2
  have hsecond : (Q.mkQ.rTensor A.carrier)
      (TensorProduct.map inc act
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    induction Coalgebra.comul (R := k) (A := C.carrier) c using
        TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add z w hz hw =>
        rw [map_add, map_add]
        rw [hz, hw, add_zero]
    | tmul x y =>
        change Q.mkQ (inc x) ⊗ₜ[k] act y = 0
        rw [hincQ x, zero_tmul]
  have hfirst : (Q.mkQ.rTensor A.carrier)
      (TensorProduct.map act inc
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [lieStep_comul_action, map_add] at hcomulZero
    rw [hsecond, add_zero] at hcomulZero
    exact hcomulZero
  have hnaturality : (inc.lTensor (A.carrier ⧸ Q))
      ((φ.rTensor C.carrier)
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    have hnat : ∀ z : C.carrier ⊗[k] C.carrier,
        (inc.lTensor (A.carrier ⧸ Q)) ((φ.rTensor C.carrier) z) =
          (Q.mkQ.rTensor A.carrier) (TensorProduct.map act inc z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, map_zero]
      | add z w hz hw =>
          rw [map_add, map_add, map_add, map_add]
          rw [hz, hw]
      | tmul x y => rfl
    rw [hnat, hfirst]
  have hφcomul : (φ.rTensor C.carrier)
      (Coalgebra.comul (R := k) (A := C.carrier) c) = 0 :=
    hinctensor (hnaturality.trans (map_zero _).symm)
  have hexact : Function.Exact B.subtype φ := by
    change Function.Exact (LinearMap.ker φ).subtype φ
    exact φ.exact_subtype_ker_map
  have htensorExact : Function.Exact
      (B.subtype.rTensor C.carrier) (φ.rTensor C.carrier) :=
    rTensor_exact C.carrier hexact hφsurj
  rw [← htensorExact.linearMap_ker_eq, LinearMap.mem_ker]
  exact hφcomul

/-- The kernel of the Lie quotient map is a left coideal of `C`. -/
theorem lieStepKernel_isLeftCoideal
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    Coalgebra.IsLeftCoideal (lieStepKernel F' F C D a) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  let Q := lieStepDenominator F' F C D
  let φ := lieStepQuotientMap F' F C D a
  let B := lieStepKernel F' F C D a
  let act := lieStepActionMap F C a
  let inc := lieStepInclusionMap F C
  have hQ : IsSubcoalgebra (k := k) Q :=
    lieStepDenominator_isSubcoalgebra F' F hFF C D hD
  have hφsurj : Function.Surjective φ :=
    lieStepQuotientMap_surjective F' F hFF C D ell a hker ha
  have hincinj : Function.Injective inc := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : A.carrier => (z : M)) hxy)
  have hinctensor : Function.Injective (inc.rTensor (A.carrier ⧸ Q)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hincinj
  intro c hc
  have hφc : φ c = 0 := (LinearMap.mem_ker).1 hc
  have hactQ : act c ∈ Q := by
    apply (Submodule.Quotient.mk_eq_zero Q).1
    exact hφc
  have hcomulZero : (Q.mkQ.lTensor A.carrier)
      (Coalgebra.comul (R := k) (A := A.carrier) (act c)) = 0 := by
    rcases hQ hactQ with ⟨z, hz⟩
    have hkill : ∀ w : Q ⊗[k] Q,
        (Q.mkQ.lTensor A.carrier) (TensorProduct.mapIncl Q Q w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
      | tmul x y =>
          change (x : A.carrier) ⊗ₜ[k] Q.mkQ y = 0
          have hyzero : Q.mkQ (y : A.carrier) = 0 :=
            (Submodule.Quotient.mk_eq_zero Q).2 y.2
          rw [hyzero, tmul_zero]
    rw [← hz]
    exact hkill z
  have hincQ : ∀ x : C.carrier, Q.mkQ (inc x) = 0 := by
    intro x
    apply (Submodule.Quotient.mk_eq_zero Q).2
    apply Submodule.mem_sup_right
    exact le_lieExpansion F' C.carrier x.2
  have hfirst : (Q.mkQ.lTensor A.carrier)
      (TensorProduct.map act inc
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    induction Coalgebra.comul (R := k) (A := C.carrier) c using
        TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add z w hz hw =>
        rw [map_add, map_add]
        rw [hz, hw, add_zero]
    | tmul x y =>
        change act x ⊗ₜ[k] Q.mkQ (inc y) = 0
        rw [hincQ y, tmul_zero]
  have hsecond : (Q.mkQ.lTensor A.carrier)
      (TensorProduct.map inc act
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    rw [lieStep_comul_action, map_add] at hcomulZero
    rw [hfirst, zero_add] at hcomulZero
    exact hcomulZero
  have hnaturality : (inc.rTensor (A.carrier ⧸ Q))
      ((φ.lTensor C.carrier)
        (Coalgebra.comul (R := k) (A := C.carrier) c)) = 0 := by
    have hnat : ∀ z : C.carrier ⊗[k] C.carrier,
        (inc.rTensor (A.carrier ⧸ Q)) ((φ.lTensor C.carrier) z) =
          (Q.mkQ.lTensor A.carrier) (TensorProduct.map inc act z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, map_zero]
      | add z w hz hw =>
          rw [map_add, map_add, map_add, map_add]
          rw [hz, hw]
      | tmul x y => rfl
    rw [hnat, hsecond]
  have hφcomul : (φ.lTensor C.carrier)
      (Coalgebra.comul (R := k) (A := C.carrier) c) = 0 :=
    hinctensor (hnaturality.trans (map_zero _).symm)
  have hexact : Function.Exact B.subtype φ := by
    change Function.Exact (LinearMap.ker φ).subtype φ
    exact φ.exact_subtype_ker_map
  have htensorExact : Function.Exact
      (B.subtype.lTensor C.carrier) (φ.lTensor C.carrier) :=
    lTensor_exact C.carrier hexact hφsurj
  rw [← htensorExact.linearMap_ker_eq, LinearMap.mem_ker]
  exact hφcomul

/-- The codimension-one kernel is a subcoalgebra, without cocommutativity. -/
theorem lieStepKernel_isSubcoalgebra
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    IsSubcoalgebra (k := k) (lieStepKernel F' F C D a) :=
  Coalgebra.isSubcoalgebra_of_twoSidedCoideal
    (lieStepKernel_isRightCoideal F' F hFF C D hD ell a hker ha)
    (lieStepKernel_isLeftCoideal F' F hFF C D hD ell a hker ha)

/-- The internal copy in `F⁺C` of `G⁺U`, for `G ≤ F`. -/
def lieStepUSubspace
    (G F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier) :
    Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier :=
  (lieExpansion G (ambientImage C.carrier U)).comap
    (lieExpansionFiniteSubcoalgebra F C).carrier.subtype

theorem ambientImage_lieStepUSubspace
    (G F : Submodule k L) [FiniteDimensional k F]
    (hGF : G ≤ F) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier) :
    ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
        (lieStepUSubspace G F C U) =
      lieExpansion G (ambientImage C.carrier U) := by
  apply ambientImage_comap_eq_of_le
  apply (lieExpansion_mono_left hGF (ambientImage C.carrier U)).trans
  apply lieExpansion_mono_right
  rintro x ⟨u, hu, rfl⟩
  exact u.2

/-- The U-side numerator `D + F⁺U`. -/
def lieStepUNumerator
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier :=
  D ⊔ lieStepUSubspace F F C U

/-- The U-side denominator `D + F'⁺U`. -/
def lieStepUDenominator
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier :=
  D ⊔ lieStepUSubspace F' F C U

theorem lieStepUDenominator_le_numerator
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    lieStepUDenominator F' F C U D ≤ lieStepUNumerator F C U D := by
  apply sup_le_sup_left
  intro x hx
  change (x : M) ∈ lieExpansion F (ambientImage C.carrier U)
  exact lieExpansion_mono_left hFF (ambientImage C.carrier U) hx

/-- The U-side denominator regarded inside its numerator. -/
def lieStepUDenominatorInternal
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    Submodule k (lieStepUNumerator F C U D) :=
  (lieStepUDenominator F' F C U D).comap
    (lieStepUNumerator F C U D).subtype

/-- Inclusion of `U` into the U-side numerator. -/
def lieStepUInclusionMap
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    U →ₗ[k] lieStepUNumerator F C U D :=
  LinearMap.codRestrict (lieStepUNumerator F C U D)
    ((lieStepInclusionMap F C).comp U.subtype)
    (fun u => Submodule.mem_sup_right (by
      change (u : M) ∈ lieExpansion F (ambientImage C.carrier U)
      exact le_lieExpansion F _ ⟨u, u.2, rfl⟩))

/-- The restricted action tensor map with codomain the U-side numerator. -/
def lieStepUTensorMap
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier) :
    F ⊗[k] ambientImage C.carrier U →ₗ[k] lieStepUNumerator F C U D :=
  LinearMap.codRestrict (lieStepUNumerator F C U D)
    (LinearMap.codRestrict (lieExpansionFiniteSubcoalgebra F C).carrier
      (lieActionMap F (ambientImage C.carrier U)) (fun z =>
        (lieExpansion_mono_right F (by
          rintro x ⟨ux, hux, rfl⟩
          exact ux.2))
          (lieActionSubspace_le_lieExpansion F _ ⟨z, rfl⟩)))
    (fun z => Submodule.mem_sup_right
      (lieActionSubspace_le_lieExpansion F _ ⟨z, rfl⟩))

@[simp]
theorem lieStepUInclusionMap_apply
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (u : U) :
    ((lieStepUInclusionMap F C U D u :
      (lieExpansionFiniteSubcoalgebra F C).carrier) : M) = (u : M) := rfl

@[simp]
theorem lieStepUTensorMap_tmul
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (x : F) (u : ambientImage C.carrier U) :
    (((lieStepUTensorMap F C U D (x ⊗ₜ[k] u) :
      lieStepUNumerator F C U D) :
        (lieExpansionFiniteSubcoalgebra F C).carrier) : M) =
      ⁅(x : L), (u : M)⁆ := rfl

/-- The U-side quotient map induced by action by the complement. -/
def lieStepUQuotientMap
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) :
    U →ₗ[k]
      (lieStepUNumerator F C U D) ⧸
        lieStepUDenominatorInternal F' F C U D :=
  (lieStepUDenominatorInternal F' F C U D).mkQ.comp
    (LinearMap.codRestrict (lieStepUNumerator F C U D)
      ((lieStepActionMap F C a).comp U.subtype)
      (fun u => by
        apply Submodule.mem_sup_right
        change ⁅(a : L), (u : M)⁆ ∈
          lieExpansion F (ambientImage C.carrier U)
        apply lieActionSubspace_le_lieExpansion F _
        exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩))

@[simp]
theorem lieStepUQuotientMap_apply
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) (u : U) :
    lieStepUQuotientMap F' F C U D a u =
      (lieStepUDenominatorInternal F' F C U D).mkQ
        ⟨lieStepActionMap F C a u,
          Submodule.mem_sup_right
            (by
              change ⁅(a : L), (u : M)⁆ ∈
                lieExpansion F (ambientImage C.carrier U)
              apply lieActionSubspace_le_lieExpansion F _
              exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩)⟩ := rfl

theorem lieStepUQuotientMap_surjective
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    Function.Surjective (lieStepUQuotientMap F' F C U D a) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  let N := lieStepUNumerator F C U D
  let P := lieStepUDenominator F' F C U D
  let Pint := lieStepUDenominatorInternal F' F C U D
  let ψ := lieStepUQuotientMap F' F C U D a
  let e := ambientImageEquiv C.carrier U
  let incU := lieStepUInclusionMap F C U D
  let actU := lieStepUTensorMap F C U D
  have hUambC : ambientImage C.carrier U ≤ C.carrier := by
    rintro x ⟨ux, hux, rfl⟩
    exact ux.2
  have hUAC : lieExpansion F (ambientImage C.carrier U) ≤ A.carrier :=
    lieExpansion_mono_right F hUambC
  have hDzero : ∀ d : D,
      Pint.mkQ (⟨d, Submodule.mem_sup_left d.2⟩ : N) = 0 := by
    intro d
    apply (Submodule.Quotient.mk_eq_zero Pint).2
    exact Submodule.mem_sup_left d.2
  have hUzero : ∀ u : U,
      Pint.mkQ (incU u) = 0 := by
    intro u
    apply (Submodule.Quotient.mk_eq_zero Pint).2
    apply Submodule.mem_sup_right
    change (u : M) ∈ lieExpansion F' (ambientImage C.carrier U)
    exact le_lieExpansion F' _ ⟨u, u.2, rfl⟩
  have haction : ∀ z : F ⊗[k] ambientImage C.carrier U,
      ∃ u : U,
        Pint.mkQ (actU z) = ψ u := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
    | add z w hz hw =>
        rcases hz with ⟨u, hu⟩
        rcases hw with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        rw [map_add, map_add, map_add, hu, hv]
    | tmul x uamb =>
        let u : U := e.symm uamb
        refine ⟨ell x • u, ?_⟩
        rw [lieStepUQuotientMap_apply]
        apply (Submodule.Quotient.eq Pint).2
        change actU (x ⊗ₜ[k] uamb) -
          ⟨lieStepActionMap F C a (ell x • u),
            Submodule.mem_sup_right (by
              change ⁅(a : L), ((ell x • u : U) : M)⁆ ∈
                lieExpansion F (ambientImage C.carrier U)
              apply lieActionSubspace_le_lieExpansion F _
              exact lie_mem_lieActionSubspace a.2
                ⟨ell x • u, (ell x • u).2, rfl⟩)⟩ ∈ Pint
        apply Submodule.mem_sup_right
        change ⁅(x : L), (uamb : M)⁆ -
            ⁅(a : L), ell x • (u : M)⁆ ∈
          lieExpansion F' (ambientImage C.carrier U)
        have hp := sub_smul_mem_lieCodimOneLower F' F ell a x hker ha
        have heu : (u : M) = (uamb : M) :=
          congrArg Subtype.val (e.apply_symm_apply uamb)
        rw [heu]
        apply lieActionSubspace_le_lieExpansion F' _
        simpa using lie_mem_lieActionSubspace hp uamb.2
  intro q
  obtain ⟨y, rfl⟩ := Pint.mkQ_surjective q
  rcases Submodule.mem_sup.1 y.2 with ⟨d, hd, w, hw, hy⟩
  change (w : M) ∈ lieExpansion F (ambientImage C.carrier U) at hw
  rcases Submodule.mem_sup.1 hw with ⟨u0, hu0, v, hv, huv⟩
  let u : U := e.symm ⟨u0, hu0⟩
  rcases hv with ⟨z, hz⟩
  rcases haction z with ⟨u1, hu1⟩
  refine ⟨u1, ?_⟩
  change ψ u1 = Pint.mkQ y
  rw [← hu1]
  let dD : D := ⟨d, hd⟩
  let uN : N := incU u
  have huNzero : Pint.mkQ uN = 0 := hUzero u
  let vN : N := actU z
  have hvNval : ((vN : A.carrier) : M) = v := by
    change lieActionMap F (ambientImage C.carrier U) z = v
    exact hz
  have hyN : y =
      (⟨dD, Submodule.mem_sup_left dD.2⟩ : N) + uN + vN := by
    apply Subtype.ext
    change (y : A.carrier) = (dD : A.carrier) + (uN : A.carrier) + (vN : A.carrier)
    apply Subtype.ext
    change (y : M) = d + (u : M) + (vN : M)
    rw [hvNval]
    have heu : (u : M) = u0 :=
      congrArg Subtype.val (e.apply_symm_apply ⟨u0, hu0⟩)
    rw [heu]
    calc
      (y : M) = (d : M) + (w : M) :=
        congrArg (fun q : A.carrier => (q : M)) hy.symm
      _ = (d : M) + (u0 + v) :=
        congrArg (fun q : M => (d : M) + q) huv.symm
      _ = d + u0 + v := by simp [add_assoc]
  rw [hyN, map_add, map_add, hDzero, huNzero, zero_add, zero_add]

/-- The lower expansion of `U` is contained in the lower expansion of `C`. -/
theorem lieStepUSubspace_le_lieLowerExpansionSubspace
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier) :
    lieStepUSubspace F' F C U ≤ lieLowerExpansionSubspace F' F C := by
  intro x hx
  change (x : M) ∈ lieExpansion F' C.carrier
  change (x : M) ∈ lieExpansion F' (ambientImage C.carrier U) at hx
  apply lieExpansion_mono_right F' _ hx
  rintro y ⟨u, -, rfl⟩
  exact u.2

/-- The kernel of the U-side quotient map lies in the restriction of the
codimension-one step kernel. -/
theorem lieStepUQuotientMap_ker_le
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) :
    LinearMap.ker (lieStepUQuotientMap F' F C U D a) ≤
      (lieStepKernel F' F C D a).comap U.subtype := by
  intro u hu
  let N := lieStepUNumerator F C U D
  let P := lieStepUDenominator F' F C U D
  let Pint := lieStepUDenominatorInternal F' F C U D
  have hzero : Pint.mkQ
      ⟨lieStepActionMap F C a u,
        Submodule.mem_sup_right (by
          change ⁅(a : L), (u : M)⁆ ∈
            lieExpansion F (ambientImage C.carrier U)
          apply lieActionSubspace_le_lieExpansion F _
          exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩)⟩ = 0 := by
    have hz := LinearMap.mem_ker.1 hu
    change Pint.mkQ
      ⟨lieStepActionMap F C a u,
        Submodule.mem_sup_right (by
          change ⁅(a : L), (u : M)⁆ ∈
            lieExpansion F (ambientImage C.carrier U)
          apply lieActionSubspace_le_lieExpansion F _
          exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩)⟩ = 0 at hz
    exact hz
  have hmemU :
      (⟨lieStepActionMap F C a u,
        Submodule.mem_sup_right (by
          change ⁅(a : L), (u : M)⁆ ∈
            lieExpansion F (ambientImage C.carrier U)
          apply lieActionSubspace_le_lieExpansion F _
          exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩)⟩ : N) ∈ Pint :=
    (Submodule.Quotient.mk_eq_zero Pint).1 hzero
  have hmem : lieStepActionMap F C a u ∈
      lieStepDenominator F' F C D := by
    rcases Submodule.mem_sup.1 hmemU with ⟨d, hd, w, hw, hdw⟩
    change N.subtype
      ⟨lieStepActionMap F C a u,
        Submodule.mem_sup_right (by
          change ⁅(a : L), (u : M)⁆ ∈
            lieExpansion F (ambientImage C.carrier U)
          apply lieActionSubspace_le_lieExpansion F _
          exact lie_mem_lieActionSubspace a.2 ⟨u, u.2, rfl⟩)⟩ ∈
        lieStepDenominator F' F C D
    rw [← hdw]
    exact add_mem (Submodule.mem_sup_left hd)
      (Submodule.mem_sup_right
        (lieStepUSubspace_le_lieLowerExpansionSubspace F' F C U hw))
  change U.subtype u ∈ LinearMap.ker (lieStepQuotientMap F' F C D a)
  rw [LinearMap.mem_ker, lieStepQuotientMap_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-- The gain on the `U` side dominates the codimension of its intersection
with the step kernel. -/
theorem finrank_lieStepU_difference_ge
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (ell : F →ₗ[k] k) (a : F)
    (hker : LinearMap.ker ell = lieCodimOneLower F' F)
    (ha : ell a = 1) :
    (finrank k U : ℚ) -
        sfinrank k (U ⊓ lieStepKernel F' F C D a) ≤
      (sfinrank k (lieStepUNumerator F C U D) : ℚ) -
        sfinrank k (lieStepUDenominator F' F C U D) := by
  let N := lieStepUNumerator F C U D
  let P := lieStepUDenominator F' F C U D
  let Pint := lieStepUDenominatorInternal F' F C U D
  let ψ := lieStepUQuotientMap F' F C U D a
  let B := lieStepKernel F' F C D a
  have hPN : P ≤ N :=
    lieStepUDenominator_le_numerator F' F hFF C U D
  have hPimage : ambientImage N Pint = P := by
    change ambientImage N (P.comap N.subtype) = P
    exact ambientImage_comap_eq_of_le N P hPN
  have hPdim : finrank k Pint = finrank k P := by
    rw [← hPimage, finrank_ambientImage]
  have hQ := Pint.finrank_quotient_add_finrank
  rw [hPdim] at hQ
  have hψsurj : Function.Surjective ψ :=
    lieStepUQuotientMap_surjective F' F C U D ell a hker ha
  have hψrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hψsurj
  have hψrank := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hψrange, finrank_top] at hψrank
  have hkerle : LinearMap.ker ψ ≤ B.comap U.subtype :=
    lieStepUQuotientMap_ker_le F' F C U D a
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
  have hQq : (finrank k (N ⧸ Pint) : ℚ) + finrank k P =
      finrank k N := by
    exact_mod_cast hQ
  have hψq : (finrank k (N ⧸ Pint) : ℚ) +
      finrank k (LinearMap.ker ψ) = finrank k U := by
    exact_mod_cast hψrank
  have hkerq : (finrank k (LinearMap.ker ψ) : ℚ) ≤
      sfinrank k (U ⊓ B) := by
    exact_mod_cast hkerdim
  change (finrank k U : ℚ) - sfinrank k (U ⊓ B) ≤
    (finrank k N : ℚ) - finrank k P
  linarith

/-- The codimension-one transfer inequality for Lie expansion. -/
theorem lieCodimOne_transfer_step
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F)
    (hdim : sfinrank k F = sfinrank k F' + 1)
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (hD : IsSubcoalgebra (k := k) D) (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((finrank k (lieExpansionFiniteSubcoalgebra F C).carrier : ℚ) -
        sfinrank k (lieStepDenominator F' F C D)) ≤
      (sfinrank k (lieStepUNumerator F C U D) : ℚ) -
        sfinrank k (lieStepUDenominator F' F C U D) := by
  obtain ⟨ell, a, hker, ha⟩ :=
    exists_normalized_lieCodimOne_functional F' F hFF hdim
  let B := lieStepKernel F' F C D a
  have hB : IsSubcoalgebra (k := k) B :=
    lieStepKernel_isSubcoalgebra F' F hFF C D hD ell a hker ha
  have hsemi := hsem B hB
  have hden := finrank_lieStepDenominator_difference
    F' F hFF C D ell a hker ha
  have hU := finrank_lieStepU_difference_ge
    F' F hFF C U D ell a hker ha
  change t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
    (sfinrank k U : ℚ) - sfinrank k (U ⊓ B) at hsemi
  have hdenQ :
      (finrank k (lieExpansionFiniteSubcoalgebra F C).carrier : ℚ) -
          sfinrank k (lieStepDenominator F' F C D) =
        (finrank k C.carrier : ℚ) - sfinrank k B := by
    have hdenle : sfinrank k (lieStepDenominator F' F C D) ≤
        finrank k (lieExpansionFiniteSubcoalgebra F C).carrier :=
      Submodule.finrank_le _
    have hBle : sfinrank k B ≤ finrank k C.carrier :=
      Submodule.finrank_le _
    rw [← Nat.cast_sub hdenle, ← Nat.cast_sub hBle]
    exact_mod_cast hden
  rw [hdenQ]
  exact hsemi.trans hU

end

end HopfAmenability
