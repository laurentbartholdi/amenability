/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremB
import Amenability.GroupAmenability
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Permutation-module quotient infrastructure

This file proves the finite-configuration linearization lemma and uses it to
show that a quotient of a permutation module is amenable as soon as one
nonzero orbit in its image is amenable.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

section HopfTensor

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Coalgebra k M]

/-- The first-factor action on `H ⊗ M`, bundled as a coalgebra map. -/
noncomputable def firstFactorActionCoalgHom :
    H ⊗[k] (H ⊗[k] M) →ₗc[k] H ⊗[k] M :=
  (Coalgebra.TensorProduct.map
      (Bialgebra.mulCoalgHom k H) (CoalgHom.id k M)).comp
    (Coalgebra.TensorProduct.assoc k k H H M).symm.toCoalgHom

@[simp]
theorem firstFactorActionCoalgHom_tmul (a h : H) (m : M) :
    firstFactorActionCoalgHom (k := k) (H := H) (M := M)
        (a ⊗ₜ[k] (h ⊗ₜ[k] m)) = (a * h) ⊗ₜ[k] m :=
  rfl

/-- The standard left tensor-module structure is a module-coalgebra
structure; its action is multiplication on the first tensor factor. -/
instance firstFactorTensor_isHopfModuleCoalgebra :
    IsHopfModuleCoalgebra k H (H ⊗[k] M) := by
  let f := firstFactorActionCoalgHom (k := k) (H := H) (M := M)
  have hf : f.toLinearMap = hopfModuleAction := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul h x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
      | tmul a m => rfl
  constructor
  · rw [← hf]
    exact f.counit_comp
  · rw [← hf]
    exact f.map_comp_comul.symm

end HopfTensor

section AllModuleCoalgebras

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M]
variable [IsScalarTower k H M] [Coalgebra k M]
variable [IsHopfModuleCoalgebra k H M] [Nontrivial M]

omit [Module H M] [IsScalarTower k H M] [IsHopfModuleCoalgebra k H M] in
/-- Amenability of `H` gives amenability of the first-factor module
coalgebra `H ⊗ M`. -/
theorem isAmenable_firstFactorTensor
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := H ⊗[k] M) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hm
  let t : H →ₗ[k] H ⊗[k] M := (TensorProduct.mk k H M).flip m
  let c : H ⊗[k] M →ₗ[k] H :=
    (TensorProduct.leftContract φ).comp (TensorProduct.comm k H M).toLinearMap
  have hct (h : H) : c (t h) = h := by
    simp [c, t, hφ]
  have ht : Function.Injective t := by
    intro x y hxy
    simpa only [hct] using congrArg c hxy
  apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
  intro F hF ε hε
  obtain ⟨E, hE, hEfd, hratio⟩ :=
    hH.hasActionFolnerSubspaces F hF ε hε
  let E' : Submodule k (H ⊗[k] M) := E.map t
  have hE' : E' ≠ ⊥ := by
    intro hbot
    apply hE
    apply le_antisymm
    · intro x hx
      have hx' : t x ∈ E' := Submodule.mem_map_of_mem hx
      rw [hbot, Submodule.mem_bot] at hx'
      exact ht (by simpa using hx')
    · exact bot_le
  have hexpansion : (actionExpansion F E).map t =
      actionExpansion F E' := by
    rw [actionExpansion, actionExpansion, Submodule.map_sup]
    congr 1
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.map₂_le.2
      intro a ha e he
      change t (a * e) ∈
        Submodule.map₂ (Algebra.lsmul k k (H ⊗[k] M)).toLinearMap F E'
      rw [show t (a * e) = a • t e by rfl]
      exact Submodule.apply_mem_map₂ _ ha (Submodule.mem_map_of_mem he)
    · apply Submodule.map₂_le.2
      intro a ha y hy
      rcases hy with ⟨e, he, rfl⟩
      exact ⟨a * e,
        Submodule.apply_mem_map₂ (Algebra.lsmul k k H).toLinearMap ha he,
        rfl⟩
  let _ : FiniteDimensional k E' := by
    dsimp [E']
    infer_instance
  have hdimE : finrank k E' = finrank k E := by
    have h := (LinearEquiv.ofInjective (t.domRestrict E)
      (fun x y hxy => Subtype.ext (ht hxy))).finrank_eq.symm
    rw [LinearMap.range_domRestrict] at h
    exact h
  have hdimExpansion :
      finrank k ((actionExpansion F E).map t) =
        finrank k (actionExpansion F E) := by
    have h := (LinearEquiv.ofInjective (t.domRestrict (actionExpansion F E))
      (fun x y hxy => Subtype.ext (ht hxy))).finrank_eq.symm
    rw [LinearMap.range_domRestrict] at h
    exact h
  refine ⟨E', hE', inferInstance, ?_⟩
  rw [← hexpansion, sfinrank, sfinrank, hdimE, hdimExpansion]
  exact hratio

/-- The action map `H ⊗ M → M` is an equivariant surjective coalgebra
map for the first-factor action. -/
theorem isAmenable_moduleCoalgebra_of_isAmenableHopfAlgebra
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) := by
  let q : H ⊗[k] M →ₗc[k] M := hopfModuleActionCoalgHom
  apply IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom q
  · intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul h m =>
      change (a * h) • m = a • h • m
      rw [mul_smul]
  · intro m
    exact ⟨1 ⊗ₜ[k] m, by simp [q]⟩
  · exact isAmenable_firstFactorTensor hH

/-- **Theorem C.** A cocommutative Hopf algebra is amenable exactly when
all of its nonzero module coalgebras are amenable. -/
theorem isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras :
    IsAmenableHopfAlgebra (k := k) (H := H) ↔
      ∀ (N : Type v) [AddCommGroup N] [Module k N] [Module H N]
        [IsScalarTower k H N] [Coalgebra k N]
        [IsHopfModuleCoalgebra k H N] [Nontrivial N],
        IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := N) := by
  constructor
  · intro hH N _ _ _ _ _ _ _
    exact isAmenable_moduleCoalgebra_of_isAmenableHopfAlgebra hH
  · intro h
    let : Nontrivial H := ⟨⟨0, 1, fun h01 => by
      have := congrArg (Coalgebra.counit (R := k)) h01
      simp at this⟩⟩
    exact h H

end AllModuleCoalgebras

end
end HopfAmenability
