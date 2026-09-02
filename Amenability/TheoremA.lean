/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfModuleCoalgebraRounding

/-!
# Theorem A: amenability of Hopf-module coalgebras

This file states and proves Theorem A of the accompanying article: for a
cocommutative Hopf algebra, a module coalgebra has Følner subcoalgebras if and
only if its underlying module has Følner subspaces.
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- The subspace `E + F E` associated to a finite-dimensional test space `F`. -/
def actionExpansion (F : Submodule k H) (E : Submodule k M) :
    Submodule k M :=
  E ⊔ actionSubspace F E

theorem actionExpansion_mono_left {F F' : Submodule k H}
    (hFF' : F ≤ F') (E : Submodule k M) :
    actionExpansion F E ≤ actionExpansion F' E := by
  exact sup_le_sup_left (actionSubspace_mono_left hFF' E) E

theorem actionExpansion_eq_actionSubspace_of_one_mem
    {F : Submodule k H} (h1 : (1 : H) ∈ F) (E : Submodule k M) :
    actionExpansion F E = actionSubspace F E := by
  apply le_antisymm
  · rw [actionExpansion, sup_le_iff]
    exact ⟨fun m hm => by simpa using product_mem_actionSubspace h1 hm,
      le_rfl⟩
  · exact le_sup_right

theorem finiteDimensional_actionExpansion
    (F : Submodule k H) (E : Submodule k M)
    [FiniteDimensional k F] [FiniteDimensional k E] :
    FiniteDimensional k (actionExpansion F E) := by
  rw [actionExpansion]
  infer_instance

/-- The one-dimensional subcoalgebra spanned by the unit of a Hopf algebra. -/
def unitFiniteSubcoalgebra : FiniteSubcoalgebra k H where
  carrier := Submodule.span k {1}
  isSubcoalgebra := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    let oneInSpan : Submodule.span k ({1} : Set H) :=
      ⟨1, Submodule.mem_span_singleton_self 1⟩
    refine ⟨(a • oneInSpan) ⊗ₜ[k] oneInSpan, ?_⟩
    simp only [TensorProduct.map_tmul, map_smul, Submodule.subtype_apply,
      Bialgebra.comul_one]
    exact (TensorProduct.smul_tmul' a (1 : H) (1 : H)).symm
  finiteDimensional := by infer_instance

/-- Adjoining the unit to the acting space turns pure action into the
manuscript's expansion `E + F E`. -/
theorem actionSubspace_sup_unit_eq_actionExpansion
    (F : Submodule k H) (E : Submodule k M) :
    actionSubspace (F ⊔ (unitFiniteSubcoalgebra (k := k) (H := H)).carrier) E =
      actionExpansion F E := by
  have hunit :
      actionSubspace (unitFiniteSubcoalgebra (k := k) (H := H)).carrier E = E := by
    apply le_antisymm
    · rw [actionSubspace_eq_map₂, Submodule.map₂_le]
      intro h hh m hm
      change h • m ∈ E
      change h ∈ Submodule.span k ({1} : Set H) at hh
      rw [Submodule.mem_span_singleton] at hh
      obtain ⟨a, rfl⟩ := hh
      simpa [Algebra.smul_def] using E.smul_mem a hm
    · intro m hm
      simpa using product_mem_actionSubspace
        (F := (unitFiniteSubcoalgebra (k := k) (H := H)).carrier)
        (Submodule.mem_span_singleton_self 1) hm
  rw [actionSubspace_eq_map₂, Submodule.map₂_sup_left,
    ← actionSubspace_eq_map₂, ← actionSubspace_eq_map₂, hunit,
    actionExpansion, sup_comm]

/-- Elek's ordinary finite-dimensional Følner-subspace condition for an
`H`-module. -/
def HasActionFolnerSubspaces : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k M,
        E ≠ ⊥ ∧ FiniteDimensional k E ∧
          (sfinrank k (actionExpansion F E) : ℚ) ≤
            (1 + ε) * sfinrank k E

section Coalgebra

variable [Coalgebra.IsCocomm k H]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- **The sharp ratio form of Theorem A.** For the manuscript expansion
`E + F E`, rounding to a finite subcoalgebra does not increase the ratio. -/
theorem exists_finiteSubcoalgebra_expansion_ratio_le
    (F : FiniteSubcoalgebra k H)
    (E : Submodule k M)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (actionExpansion F.carrier C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (actionExpansion F.carrier E) : ℚ) /
            (finrank k E : ℚ) := by
  let F₁ : FiniteSubcoalgebra k H := {
    carrier := F.carrier ⊔ (unitFiniteSubcoalgebra (k := k) (H := H)).carrier
    isSubcoalgebra := F.isSubcoalgebra.sup
      (unitFiniteSubcoalgebra (k := k) (H := H)).isSubcoalgebra
    finiteDimensional := by infer_instance }
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_action_ratio_le F₁ E hE
  refine ⟨C, hC, ?_⟩
  simpa only [F₁, actionSubspace_sup_unit_eq_actionExpansion] using hratio

/-- The Følner-subcoalgebra definition of amenability for a Hopf-module
coalgebra. -/
def IsAmenableHopfModuleCoalgebra : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : FiniteSubcoalgebra k M,
        C.carrier ≠ ⊥ ∧
          (sfinrank k (actionExpansion F C.carrier) : ℚ) ≤
            (1 + ε) * finrank k C.carrier

omit [Coalgebra.IsCocomm k H] [IsHopfModuleCoalgebra k H M] in
/-- Følner subcoalgebras are particular Følner subspaces. -/
theorem IsAmenableHopfModuleCoalgebra.hasActionFolnerSubspaces
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    HasActionFolnerSubspaces (k := k) (H := H) (M := M) := by
  intro F hF ε hε
  obtain ⟨C, hC, hratio⟩ := hM F hF ε hε
  exact ⟨C.carrier, hC, inferInstance, hratio⟩

/-- Ordinary Følner subspaces can be rounded to Følner subcoalgebras. -/
theorem HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
    (hM : HasActionFolnerSubspaces (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) := by
  intro F hF ε hε
  let : FiniteDimensional k F := hF
  let F1 : Submodule k H := F ⊔ Submodule.span k {1}
  let : FiniteDimensional k F1 := by
    dsimp [F1]
    infer_instance
  obtain ⟨A, hF1A⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule F1
  have hFA : F ≤ A.carrier := le_trans le_sup_left hF1A
  have h1A : (1 : H) ∈ A.carrier := by
    apply hF1A
    exact (le_sup_right : Submodule.span k {1} ≤ F1)
      (Submodule.subset_span (Set.mem_singleton 1))
  obtain ⟨E, hE, hEfd, hEratio⟩ := hM A.carrier inferInstance ε hε
  let : FiniteDimensional k E := hEfd
  rw [actionExpansion_eq_actionSubspace_of_one_mem h1A] at hEratio
  obtain ⟨C, hC, hround⟩ :=
    exists_finiteSubcoalgebra_action_ratio_le A E hE
  refine ⟨C, hC, ?_⟩
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let : Nontrivial C.carrier := Submodule.nontrivial_iff_ne_bot.mpr hC
  have hEpos : (0 : ℚ) < finrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hCpos : (0 : ℚ) < finrank k C.carrier := by
    exact_mod_cast Module.finrank_pos (R := k) (M := C.carrier)
  have hsource :
      (sfinrank k (actionSubspace A.carrier E) : ℚ) /
          finrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).mpr hEratio
  have htarget :
      (sfinrank k (actionSubspace A.carrier C.carrier) : ℚ) ≤
          (1 + ε) * finrank k C.carrier :=
    (div_le_iff₀ hCpos).mp (hround.trans hsource)
  have hmono : actionExpansion F C.carrier ≤
      actionSubspace A.carrier C.carrier := by
    rw [← actionExpansion_eq_actionSubspace_of_one_mem h1A]
    exact actionExpansion_mono_left hFA C.carrier
  have hmonoDim :
      (sfinrank k (actionExpansion F C.carrier) : ℚ) ≤
        sfinrank k (actionSubspace A.carrier C.carrier) := by
    exact_mod_cast Submodule.finrank_mono hmono
  exact hmonoDim.trans htarget

/-- **Theorem A.** A Hopf-module coalgebra is amenable exactly when its
underlying associative-algebra module is algebraically amenable. -/
theorem isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) ↔
      HasActionFolnerSubspaces (k := k) (H := H) (M := M) :=
  ⟨IsAmenableHopfModuleCoalgebra.hasActionFolnerSubspaces,
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra⟩

end Coalgebra

end

end HopfAmenability
