/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremE
import Amenability.TheoremF

/-! # Group permanence through group Hopf algebras -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {G : Type v}
variable [Field k] [Group G]

/-- Linearization of a group homomorphism as a Hopf-algebra morphism. -/
def groupAlgebraHopfHom {Q : Type w} [Group Q] (f : G →* Q) :
    HopfAlgebraHom (k := k) (H := MonoidAlgebra k G)
      (MonoidAlgebra k Q) where
  toAlgHom := MonoidAlgebra.mapDomainAlgHom k k f
  map_counit := (MonoidAlgebra.mapDomainBialgHom k f).counit_comp
  map_comul := (MonoidAlgebra.mapDomainBialgHom k f).map_comp_comul

/-- The group algebra of a subgroup is a Hopf subalgebra of the group
algebra of the ambient group. -/
def subgroupGroupAlgebraEmbedding (K : Subgroup G) :
    HopfSubalgebraEmbedding (k := k) (H := MonoidAlgebra k G)
      (MonoidAlgebra k K) where
  toHopfAlgebraHom := groupAlgebraHopfHom (k := k) K.subtype
  injective := by
    exact MonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- For the left regular action of `G` on itself, the permutation-module
structure on `k[G]` is the usual regular module structure. -/
theorem groupAlgebraModule_self_eq_regular :
    groupAlgebraModule (k := k) (G := G) (X := G) =
      (inferInstance : Module (MonoidAlgebra k G) (MonoidAlgebra k G)) := by
  apply Module.ext
  funext a b
  change (groupActionRepresentation (k := k) (G := G)
    (X := G)).asAlgebraHom a b = a * b
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      induction b using MonoidAlgebra.induction_on with
      | of x =>
          simp [groupActionRepresentation, Representation.ofMulAction_single,
            MonoidAlgebra.single_mul_single]
      | add x y hx hy => simp only [map_add, mul_add, hx, hy]
      | smul r x hx => simp only [map_smul, mul_smul_comm, hx]
  | add x y hx hy =>
      rw [map_add]
      change (groupActionRepresentation.asAlgebraHom x) b +
        (groupActionRepresentation.asAlgebraHom y) b = _
      rw [hx, hy, add_mul]
  | smul r x hx =>
      rw [map_smul]
      change r • (groupActionRepresentation.asAlgebraHom x) b = _
      rw [hx, Algebra.smul_mul_assoc]

/-- On the regular module, multiplying the spans of two finite sets of group
elements spans their set-theoretic product. -/
theorem regular_actionSubspace_groupActing_pointSpan
    [DecidableEq G] (S A : Finset G) :
    actionSubspace (groupActingSubcoalgebra (k := k) S).carrier
        (pointSpan (k := k) A) =
      pointSpan (k := k) (groupSetExpansion S A) := by
  rw [actionSubspace_eq_map₂, groupActingSubcoalgebra_carrier]
  simp only [pointSpan]
  rw [Submodule.map₂_span_span]
  apply congrArg (Submodule.span k)
  ext y
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨g * a, ?_, ?_⟩
    · change g * a ∈ groupSetExpansion S A
      change g * a ∈ ((insert 1 S).product A).image (fun p => p.1 * p.2)
      rw [Finset.mem_image]
      exact ⟨(g, a), Finset.mem_product.2 ⟨hg, ha⟩, rfl⟩
    · simp [groupBasis, pointBasis, MonoidAlgebra.single_mul_single]
  · rintro ⟨x, hx, rfl⟩
    change x ∈ groupSetExpansion S A at hx
    change x ∈ ((insert 1 S).product A).image (fun p => p.1 * p.2) at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨⟨g, a⟩, hga, rfl⟩
    have hg := (Finset.mem_product.mp hga).1
    have ha := (Finset.mem_product.mp hga).2
    refine ⟨groupBasis (k := k) g, ⟨g, hg, rfl⟩,
      pointBasis (k := k) a, ⟨a, ha, rfl⟩, ?_⟩
    simp [groupBasis, pointBasis, MonoidAlgebra.single_mul_single]

/-- Coalgebraic rounding for the regular group-algebra module. -/
theorem exists_finset_regular_group_ratio_le
    [DecidableEq G] (S : Finset G) (E : Submodule k (MonoidAlgebra k G))
    [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ A : Finset G, A.Nonempty ∧
      ((groupSetExpansion S A).card : ℚ) / A.card ≤
        (sfinrank k (actionSubspace
          (groupActingSubcoalgebra (k := k) S).carrier E) : ℚ) /
          Module.finrank k E := by
  classical
  obtain ⟨C, hC, hratio⟩ := exists_finiteSubcoalgebra_action_ratio_le
    (groupActingSubcoalgebra (k := k) S) E hE
  obtain ⟨A, hCA, _⟩ := exists_finset_eq_carrier C
  have hA : A.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    apply hC
    rw [hCA, hn]
    simp
  refine ⟨A, hA, ?_⟩
  simp only [sfinrank] at hratio
  rw [hCA] at hratio
  change ((Module.finrank k (actionSubspace
      (groupActingSubcoalgebra (k := k) S).carrier
      (pointSpan (k := k) A)) : ℚ) / Module.finrank k (pointSpan (k := k) A) ≤ _) at hratio
  rw [regular_actionSubspace_groupActing_pointSpan] at hratio
  simpa only [finrank_pointSpan] using hratio

/-- Amenability of a group implies amenability of its group Hopf algebra. -/
theorem isAmenableGroupAlgebra_of_isAmenableGroup
    (hG : IsAmenableGroup (G := G)) :
    IsAmenableHopfAlgebra (k := k) (H := MonoidAlgebra k G) := by
  apply isAmenableHopfAlgebra_iff_algebraicallyAmenable.mpr
  exact hasActionFolnerSubspaces_of_isAmenableGroup hG inferInstance

/-- A group is amenable exactly when its group Hopf algebra is amenable. -/
theorem isAmenableGroup_iff_groupAlgebra :
    IsAmenableGroup (G := G) ↔
      IsAmenableHopfAlgebra (k := k) (H := MonoidAlgebra k G) := by
  classical
  constructor
  · exact isAmenableGroupAlgebra_of_isAmenableGroup
  · intro h
    classical
    intro S ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := h.hasActionFolnerSubspaces
      (groupActingSubcoalgebra (k := k) S).carrier inferInstance ε hε
    let _ : FiniteDimensional k E := hEfd
    have hOne : (1 : MonoidAlgebra k G) ∈
        (groupActingSubcoalgebra (k := k) S).carrier := by
      rw [groupActingSubcoalgebra_carrier]
      exact Submodule.subset_span ⟨1, Finset.mem_insert_self 1 S, by
        simp [groupBasis, MonoidAlgebra.one_def]⟩
    rw [actionExpansion_eq_actionSubspace_of_one_mem hOne] at hratio
    obtain ⟨A, hA, hround⟩ := exists_finset_regular_group_ratio_le
      (k := k) S E hE
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    have hEpos : (0 : ℚ) < Module.finrank k E := by
      exact_mod_cast Module.finrank_pos (R := k) (M := E)
    have hApos : (0 : ℚ) < A.card := by exact_mod_cast A.card_pos.mpr hA
    have hr : ((groupSetExpansion S A).card : ℚ) / A.card ≤ 1 + ε :=
      hround.trans ((div_le_iff₀ hEpos).mpr hratio)
    exact ⟨A, hA, (div_le_iff₀ hApos).mp hr⟩

/-- Subgroups of amenable groups are amenable, obtained by applying Theorem D
to the corresponding inclusion of group Hopf algebras. -/
theorem isAmenableGroup_subgroup (k : Type u) [Field k] (K : Subgroup G)
    (hG : IsAmenableGroup (G := G)) : IsAmenableGroup (G := K) := by
  apply (isAmenableGroup_iff_groupAlgebra (k := k) (G := K)).mpr
  exact isAmenableHopfAlgebra_of_hopfSubalgebra
    (subgroupGroupAlgebraEmbedding (k := k) K)
    ((isAmenableGroup_iff_groupAlgebra (k := k) (G := G)).mp hG)

end

end HopfAmenability
