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
variable [Coalgebra k M] [LieModuleCoalgebra k L M]

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
    (LinearMap.codRestrict (lieExpansionFiniteSubcoalgebra F C).carrier
      ((LieModule.toEnd k L M (a : L)).comp C.carrier.subtype)
      (fun c => lieActionSubspace_le_lieExpansion F C.carrier
        (lie_mem_lieActionSubspace a.2 c.2)))

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

/-- The kernel produced by the codimension-one quotient map. -/
def lieStepKernel
    (F' F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M)
    (D : Submodule k (lieExpansionFiniteSubcoalgebra F C).carrier)
    (a : F) : Submodule k C.carrier :=
  LinearMap.ker (lieStepQuotientMap F' F C D a)

end

end HopfAmenability
