/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremA
import Amenability.TheoremB
import Amenability.CoalgebraRounding

/-!
# Amenability of Hopf algebras

This file collects the amenability API which is intrinsic to Hopf algebras.
Lie algebras and groups use this layer through their universal enveloping and
group Hopf algebras, respectively.
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/-- A cocommutative Hopf algebra is amenable when its left regular
Hopf-module coalgebra has Følner subcoalgebras. -/
def IsAmenableHopfAlgebra : Prop :=
  IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := H)

/-- Algebraic amenability of the left regular module is the ordinary
finite-dimensional Følner-subspace formulation of Hopf amenability. -/
def IsAlgebraicallyAmenableHopfAlgebra : Prop :=
  HasActionFolnerSubspaces (k := k) (H := H) (M := H)

/-- Theorem A specialized to the regular Hopf module: coalgebraic and
algebraic amenability of a cocommutative Hopf algebra are equivalent. -/
theorem isAmenableHopfAlgebra_iff_algebraicallyAmenable :
    IsAmenableHopfAlgebra (k := k) (H := H) ↔
      IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H) :=
  isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces

/-- The quotient theorem for a Hopf algebra acting on a module coalgebra. -/
theorem IsAmenableHopfModuleCoalgebra.quotient
    {Q : Type*} [AddCommGroup Q] [Module k Q] [Module H Q]
    [IsScalarTower k H Q] [Coalgebra k Q] [IsHopfModuleCoalgebra k H Q]
    (q : H →ₗc[k] Q) (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (hqsurj : Function.Surjective q)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := Q) :=
  hH.of_surjective_coalgHom q hq hqsurj

/-! ## Hopf morphisms and permanence -/

/-- A morphism of Hopf algebras, expressed using the algebra morphism and
the two coalgebra compatibility identities needed below.  Mathlib currently
has no bundled Hopf-algebra morphism. -/
structure HopfAlgebraHom (K : Type w) [Ring K] [HopfAlgebra k K] where
  toAlgHom : H →ₐ[k] K
  map_counit : (Coalgebra.counit (R := k) (A := K)).comp
      toAlgHom.toLinearMap = Coalgebra.counit (R := k) (A := H)
  map_comul : (TensorProduct.map toAlgHom.toLinearMap toAlgHom.toLinearMap).comp
      (Coalgebra.comul (R := k) (A := H)) =
        (Coalgebra.comul (R := k) (A := K)).comp toAlgHom.toLinearMap

instance {K : Type w} [Ring K] [HopfAlgebra k K] : CoeFun
    (HopfAlgebraHom (k := k) (H := H) K) (fun _ => H → K) :=
  ⟨fun f => f.toAlgHom⟩

/-- A Hopf-subalgebra presentation is an injective Hopf morphism. -/
structure HopfSubalgebraEmbedding (K : Type w) [Ring K] [HopfAlgebra k K]
    extends HopfAlgebraHom (k := k) (H := K) H where
  injective : Function.Injective toAlgHom

/-- The projective-module descent input for cocommutative Hopf subalgebras.

This packages Takeuchi's faithful-flatness theorem, the Masuoka--Wigner
projectivity theorem, and projective-module Følner descent in exactly the form
used by the article. -/
axiom takeuchi_masuokaWigner_amenability_descent
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hH : IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H)) :
    IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := K)

omit [Coalgebra.IsCocomm k H] in
/-- Algebraic amenability descends along a cocommutative Hopf-subalgebra
embedding. -/
theorem algebraicAmenability_of_hopfSubalgebra
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hH : IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H)) :
    IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := K) :=
  takeuchi_masuokaWigner_amenability_descent i hH

/-- Every Hopf subalgebra of an amenable cocommutative Hopf algebra is
amenable. -/
theorem isAmenableHopfAlgebra_of_hopfSubalgebra
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfAlgebra (k := k) (H := K) := by
  apply isAmenableHopfAlgebra_iff_algebraicallyAmenable.mpr
  exact algebraicAmenability_of_hopfSubalgebra i
    (isAmenableHopfAlgebra_iff_algebraicallyAmenable.mp hH)

/-- The data of a cleft exact sequence `k → A → B → C → k` of
cocommutative Hopf algebras.  The coinvariants and normal-basis conditions
record exactness in the form used by the Følner proof. -/
structure CleftExactSequence
    (A : Type v) (B : Type w) (C : Type x)
    [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C] where
  inclusion : HopfAlgebraHom (k := k) (H := A) B
  projection : HopfAlgebraHom (k := k) (H := B) C
  inclusion_injective : Function.Injective inclusion
  projection_surjective : Function.Surjective projection
  projection_inclusion : ∀ a,
    projection (inclusion a) =
      algebraMap k C (Coalgebra.counit (R := k) a)
  coalgebraSection : C →ₗc[k] B
  projection_section : projection.toAlgHom.toLinearMap.comp
      coalgebraSection.toLinearMap = LinearMap.id
  section_one : coalgebraSection 1 = 1
  rightNormalBasis : (TensorProduct k C A) ≃ₗc[k] B
  rightNormalBasis_tmul : ∀ c a,
    rightNormalBasis (c ⊗ₜ[k] a) = coalgebraSection c * inclusion a

/-- Cleft exact sequences satisfy the normal-basis Følner estimate. -/
theorem cleftExactSequence_amenable_iff
    {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C]
    (e : CleftExactSequence (k := k) A B C) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) := by
  sorry

/-- A cleft extension of cocommutative Hopf algebras is amenable exactly
when its kernel and quotient Hopf algebras are amenable. -/
theorem isAmenableHopfAlgebra_cleftExtension_iff
    {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C]
    (e : CleftExactSequence (k := k) A B C) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) :=
  cleftExactSequence_amenable_iff e

/-! ## Associated graded module coalgebras -/

/-- Marker for a pair `(gr H, gr M)` carrying the structures induced by the
augmentation filtrations of a Hopf algebra and its module coalgebra.  The
construction is kept abstract so the amenability theorem is independent of
the chosen concrete direct-sum model. -/
class IsAugmentationAssociatedGraded
    (M : Type v) (grH : Type w) (grM : Type x)
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [Ring grH] [HopfAlgebra k grH] [AddCommGroup grM]
    [Module k grM] [Module grH grM] [IsScalarTower k grH grM]
    [Coalgebra k grM] [IsHopfModuleCoalgebra k grH grM] : Prop where
  amenable : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) →
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM)

omit [Coalgebra.IsCocomm k H] in
/-- The filtered-to-graded Følner argument: amenability passes from a
Hopf-module coalgebra to its augmentation-associated graded module
coalgebra. -/
theorem IsAmenableHopfModuleCoalgebra.associatedGraded
    {M : Type v} {grH : Type w} {grM : Type x}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [Ring grH] [HopfAlgebra k grH] [Coalgebra.IsCocomm k grH]
    [AddCommGroup grM] [Module k grM] [Module grH grM]
    [IsScalarTower k grH grM] [Coalgebra k grM]
    [IsHopfModuleCoalgebra k grH grM]
    [IsAugmentationAssociatedGraded (k := k) (H := H) M grH grM]
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM) :=
  IsAugmentationAssociatedGraded.amenable hM

end

end HopfAmenability
