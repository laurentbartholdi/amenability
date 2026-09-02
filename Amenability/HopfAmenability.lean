/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremA
import Amenability.TheoremB
import Amenability.CoalgebraRounding
import Amenability.TensorFiltrationIntersection

/-!
# Amenability of Hopf algebras

This file collects the amenability API which is intrinsic to Hopf algebras.
Lie algebras and groups use this layer through their universal enveloping and
group Hopf algebras, respectively.
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w x y

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

/-- Restriction of the left regular action along a Hopf-subalgebra
embedding. -/
@[instance_reducible]
noncomputable def hopfSubalgebraRestrictionModule
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K) : Module K H :=
  Module.compHom H i.toAlgHom.toRingHom

/-- The sole external project input: a cocommutative Hopf algebra is
projective as a left module over each Hopf subalgebra. -/
axiom takeuchiWigner_projective_left
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (_hcomm : Coalgebra.IsCocomm k H)
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K) :
    letI := hopfSubalgebraRestrictionModule i
    Module.Projective K H

/-- The right coinvariants of a Hopf morphism `B → C`. -/
noncomputable def rightCoinvariants
    {B : Type v} {C : Type w}
    [Ring B] [HopfAlgebra k B] [Ring C] [HopfAlgebra k C]
    (p : HopfAlgebraHom (k := k) (H := B) C) : Submodule k B :=
  LinearMap.ker
    ((TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := B)) -
      (TensorProduct.mk k B C).flip 1)

/-- Intrinsic cleft-exact-sequence data.  In contrast with the legacy
`CleftExactSequence`, this structure assumes only the Hopf maps, a normalized
coalgebra section, and the defining coinvariant equality; normal-basis maps
are derived from these fields. -/
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
  coinvariants : LinearMap.range inclusion.toAlgHom.toLinearMap =
    rightCoinvariants projection

/-! ## Associated graded module coalgebras -/

/-- The augmentation ideal of a bialgebra. -/
def augmentationIdeal : Ideal H :=
  RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom

/-- The powers of the augmentation ideal, viewed as the descending
augmentation filtration of the Hopf algebra. -/
def augmentationFiltration (n : ℕ) : Submodule k H :=
  ((augmentationIdeal (k := k) (H := H) ^ n : Ideal H) :
    Submodule H H).restrictScalars k

omit [Coalgebra.IsCocomm k H] in
theorem augmentationFiltration_antitone :
    Antitone (augmentationFiltration (k := k) (H := H)) := by
  intro m n hmn
  exact Submodule.restrictScalars_mono k (Ideal.pow_le_pow_right hmn)

/-- The augmentation filtration on a left Hopf module: `M n = ϖ^n M`. -/
def augmentationModuleFiltration
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] (n : ℕ) : Submodule k M :=
  actionSubspace (augmentationFiltration (k := k) (H := H) n) ⊤

omit [Coalgebra.IsCocomm k H] in
theorem augmentationModuleFiltration_antitone
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :
    Antitone (augmentationModuleFiltration (k := k) (H := H) (M := M)) := by
  intro m n hmn
  exact actionSubspace_mono_left
    (augmentationFiltration_antitone (k := k) (H := H) hmn) ⊤

omit [Coalgebra.IsCocomm k H] in
/-- The infinite intersection of the augmentation filtration is stable under
the original `H`-action. -/
theorem augmentationModuleFiltration_iInf_stable
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M]
    (h : H) (x : M)
    (hx : x ∈ ⨅ n, augmentationModuleFiltration
      (k := k) (H := H) (M := M) n) :
    h • x ∈ ⨅ n, augmentationModuleFiltration
      (k := k) (H := H) (M := M) n := by
  apply (Submodule.mem_iInf _).2
  intro n
  obtain ⟨z, hzx⟩ := (Submodule.mem_iInf _).1 hx n
  rw [← hzx]
  clear hx hzx x
  induction z with
  | zero => simp
  | add z z' hz hz' => simpa [smul_add] using Submodule.add_mem _ hz hz'
  | tmul a m =>
      rw [restrictedHopfModuleAction_tmul, ← mul_smul]
      apply product_mem_actionSubspace
      · change h * (a : H) ∈
          (augmentationIdeal (k := k) (H := H) ^ n : Ideal H)
        exact (augmentationIdeal (k := k) (H := H) ^ n).mul_mem_left h a.property
      · exact Submodule.mem_top

omit [Coalgebra.IsCocomm k H] in
theorem augmentationModuleFiltration_zero
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :
    augmentationModuleFiltration (k := k) (H := H) (M := M) 0 = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ actionSubspace
    (augmentationFiltration (k := k) (H := H) 0) ⊤
  simpa using product_mem_actionSubspace
    (show (1 : H) ∈ augmentationFiltration (k := k) (H := H) 0 by
      change (1 : H) ∈ (augmentationIdeal (k := k) (H := H) ^ 0 : Ideal H)
      change (1 : H) ∈ (1 : Ideal H)
      rw [Ideal.one_eq_top]
      exact Submodule.mem_top)
    (show x ∈ (⊤ : Submodule k M) from Submodule.mem_top)

omit [Coalgebra.IsCocomm k H] in
theorem augmentationModuleFiltration_counit_one
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    (x : M)
    (hx : x ∈ augmentationModuleFiltration (k := k) (H := H) (M := M) 1) :
    Coalgebra.counit (R := k) x = 0 := by
  rcases hx with ⟨z, rfl⟩
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul h m =>
      rw [restrictedHopfModuleAction_tmul, counit_smul]
      have hh : (h : H) ∈ augmentationIdeal (k := k) (H := H) := by
        have hp := h.property
        change (h : H) ∈
          ((augmentationIdeal (k := k) (H := H) : Ideal H) : Submodule H H) ^ 1 at hp
        rw [Submodule.pow_one] at hp
        exact hp
      have heps : Coalgebra.counit (R := k) (h : H) = 0 := hh
      rw [heps, zero_mul]

omit [Coalgebra.IsCocomm k H] in
/-- Every element of the infinite augmentation intersection has zero
counit, since the intersection lies in the first filtration term. -/
theorem augmentationModuleFiltration_iInf_counit
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    (x : M)
    (hx : x ∈ ⨅ n, augmentationModuleFiltration
      (k := k) (H := H) (M := M) n) :
    Coalgebra.counit (R := k) x = 0 :=
  augmentationModuleFiltration_counit_one x
    ((Submodule.mem_iInf _).1 hx 1)

/-- The underlying graded vector space of the concrete augmentation
associated graded module. -/
abbrev AugmentationGradedModule
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :=
  DirectSum ℕ fun n =>
    augmentationModuleFiltration (k := k) (H := H) (M := M) n ⧸
      (augmentationModuleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
        (augmentationModuleFiltration (k := k) (H := H) (M := M) n).subtype

/-- The underlying graded vector space of the augmentation-associated graded
Hopf algebra. -/
abbrev AugmentationGradedHopf :=
  DirectSum ℕ fun n =>
    augmentationFiltration (k := k) (H := H) n ⧸
      (augmentationFiltration (k := k) (H := H) (n + 1)).comap
        (augmentationFiltration (k := k) (H := H) n).subtype

/-- Structural data used by the augmentation-filtered-to-graded argument.

`Msep` is the separated quotient by the intersection of the augmentation
filtration.  The operations `liftActionSpace` and `initialSubspace` encode,
respectively, lifting a finite-dimensional homogeneous subspace of `grH`
degree by degree and taking the leading-symbol space of a finite-dimensional
subspace of `Msep`.  The last three fields are the standard finite-dimensional
facts for an exhaustive separated filtration.  In particular, this structure
does not assume the amenability conclusion. -/
structure AugmentationAssociatedGradedData
    (M : Type v) (Msep : Type y) (grH : Type w) (grM : Type x)
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [AddCommGroup Msep] [Module k Msep] [Module H Msep]
    [IsScalarTower k H Msep] [Coalgebra k Msep]
    [IsHopfModuleCoalgebra k H Msep]
    [Ring grH] [HopfAlgebra k grH] [AddCommGroup grM]
    [Module k grM] [Module grH grM] [IsScalarTower k grH grM]
    [Coalgebra k grM] [IsHopfModuleCoalgebra k grH grM] where
  grHLinearEquiv : grH ≃ₗ[k] AugmentationGradedHopf (k := k) (H := H)
  grMLinearEquiv : grM ≃ₗ[k]
    AugmentationGradedModule (k := k) (H := H) (M := M)
  augmentation_comul : ∀ n x,
    x ∈ augmentationModuleFiltration (k := k) (H := H) (M := M) n →
      Coalgebra.comul (R := k) x ∈ tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M)) n
  separatedQuotient : M →ₗc[k] Msep
  separatedQuotient_equivariant :
    IsHopfModuleMap (H := H) separatedQuotient.toLinearMap
  separatedQuotient_surjective : Function.Surjective separatedQuotient
  separatedKernel : LinearMap.ker separatedQuotient.toLinearMap =
    ⨅ n, augmentationModuleFiltration (k := k) (H := H) (M := M) n
  liftActionSpace : Submodule k grH → Submodule k H
  finiteDimensional_liftActionSpace : ∀ F : Submodule k grH,
    FiniteDimensional k F → FiniteDimensional k (liftActionSpace F)
  initialSubspace : Submodule k Msep → Submodule k grM
  finiteDimensional_initialSubspace : ∀ E : Submodule k Msep,
    FiniteDimensional k E → FiniteDimensional k (initialSubspace E)
  initialSubspace_ne_bot : ∀ E : Submodule k Msep,
    E ≠ ⊥ → initialSubspace E ≠ ⊥
  finrank_initialSubspace : ∀ E : Submodule k Msep,
    FiniteDimensional k E →
      sfinrank k (initialSubspace E) = sfinrank k E
  actionExpansion_initialSubspace_le :
    ∀ (F : Submodule k grH) (E : Submodule k Msep),
      actionExpansion F (initialSubspace E) ≤
        initialSubspace (actionExpansion (liftActionSpace F) E)

omit [Coalgebra.IsCocomm k H] in
/-- The tensor-intersection lemma makes the infinite augmentation
intersection a coideal; this is the key step in the nonseparated case. -/
theorem AugmentationAssociatedGradedData.infinity_isCoideal
    {M : Type v} {Msep : Type y} {grH : Type w} {grM : Type x}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [AddCommGroup Msep] [Module k Msep] [Module H Msep]
    [IsScalarTower k H Msep] [Coalgebra k Msep]
    [IsHopfModuleCoalgebra k H Msep]
    [Ring grH] [HopfAlgebra k grH] [AddCommGroup grM]
    [Module k grM] [Module grH grM] [IsScalarTower k grH grM]
    [Coalgebra k grM] [IsHopfModuleCoalgebra k grH grM]
    (gr : AugmentationAssociatedGradedData (k := k) (H := H)
      M Msep grH grM) :
    (⨅ n, augmentationModuleFiltration (k := k) (H := H) (M := M) n).IsCoideal :=
  iInf_isCoideal_of_coalgebraFiltration _
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_zero (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_counit_one (k := k) (H := H) (M := M))
    gr.augmentation_comul

/-- The filtered-to-graded Følner argument.  Amenability first descends to
the separated quotient and then passes to leading symbols; Theorem A rounds
the resulting Følner subspaces in the associated graded module coalgebra. -/
theorem IsAmenableHopfModuleCoalgebra.associatedGraded
    {M : Type v} {Msep : Type y} {grH : Type w} {grM : Type x}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [AddCommGroup Msep] [Module k Msep] [Module H Msep]
    [IsScalarTower k H Msep] [Coalgebra k Msep]
    [IsHopfModuleCoalgebra k H Msep]
    [Ring grH] [HopfAlgebra k grH] [Coalgebra.IsCocomm k grH]
    [AddCommGroup grM] [Module k grM] [Module grH grM]
    [IsScalarTower k grH grM] [Coalgebra k grM]
    [IsHopfModuleCoalgebra k grH grM]
    (gr : AugmentationAssociatedGradedData (k := k) (H := H)
      M Msep grH grM)
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM) := by
  have hsep : IsAmenableHopfModuleCoalgebra
      (k := k) (H := H) (M := Msep) :=
    hM.of_surjective_coalgHom gr.separatedQuotient
      gr.separatedQuotient_equivariant gr.separatedQuotient_surjective
  apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
  intro F hF ε hε
  let : FiniteDimensional k F := hF
  let Flift : Submodule k H := gr.liftActionSpace F
  let : FiniteDimensional k Flift :=
    gr.finiteDimensional_liftActionSpace F inferInstance
  obtain ⟨E, hE, hEfd, hEratio⟩ :=
    hsep.hasActionFolnerSubspaces Flift inferInstance ε hε
  let : FiniteDimensional k E := hEfd
  let Egr : Submodule k grM := gr.initialSubspace E
  let : FiniteDimensional k Egr :=
    gr.finiteDimensional_initialSubspace E inferInstance
  have hsourcefd : FiniteDimensional k (actionExpansion Flift E) := by
    exact finiteDimensional_actionExpansion Flift E
  have hinitialfd : FiniteDimensional k
      (gr.initialSubspace (actionExpansion Flift E)) :=
    gr.finiteDimensional_initialSubspace _ hsourcefd
  have hdimExpansion :
      sfinrank k (actionExpansion F Egr) ≤
        sfinrank k (actionExpansion Flift E) := by
    calc
      sfinrank k (actionExpansion F Egr) ≤
          sfinrank k (gr.initialSubspace (actionExpansion Flift E)) :=
        Submodule.finrank_mono (gr.actionExpansion_initialSubspace_le F E)
      _ = sfinrank k (actionExpansion Flift E) :=
        gr.finrank_initialSubspace _ hsourcefd
  refine ⟨Egr, gr.initialSubspace_ne_bot E hE, inferInstance, ?_⟩
  calc
    (sfinrank k (actionExpansion F Egr) : ℚ) ≤
        sfinrank k (actionExpansion Flift E) := by exact_mod_cast hdimExpansion
    _ ≤ (1 + ε) * sfinrank k E := hEratio
    _ = (1 + ε) * sfinrank k Egr := by
      rw [gr.finrank_initialSubspace E hEfd]

end

end HopfAmenability
