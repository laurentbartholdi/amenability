/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.FilteredInitial

/-! # Canonical realization of the augmentation associated graded -/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

local notation "Msep" =>
  AugmentationSeparatedModule (k := k) (H := H) (M := M)
local notation "grH" => AugmentationGradedHopf (k := k) (H := H)
local notation "grM" =>
  AugmentationGradedModule (k := k) (H := H) (M := M)
local notation "WM" =>
  augmentationModuleFiltration (k := k) (H := H) (M := M)
abbrev augmentationSeparatedLinearQuotient : M →ₗ[k] Msep :=
  (augmentationSeparatedQuotient (k := k) (H := H) (M := M)).toLinearMap
local notation "qsep" =>
  augmentationSeparatedLinearQuotient (k := k) (H := H) (M := M)

local instance augmentationGradedModuleAddCommGroup : AddCommGroup grM :=
  inferInstanceAs (AddCommGroup (Π₀ n,
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) n))

/-- A linear section of the canonical separated quotient. -/
def augmentationSeparatedSection : Msep →ₗ[k] M :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective qsep
    (LinearMap.range_eq_top.mpr
      (augmentationSeparatedQuotient_surjective
        (k := k) (H := H) (M := M))))

omit [Coalgebra.IsCocomm k H] in
@[simp]
theorem augmentationSeparatedQuotient_section (x : Msep) :
    qsep (augmentationSeparatedSection (k := k) (H := H) (M := M) x) = x :=
  LinearMap.congr_fun
    (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective qsep
      (LinearMap.range_eq_top.mpr
        (augmentationSeparatedQuotient_surjective
          (k := k) (H := H) (M := M))))) x

omit [Coalgebra.IsCocomm k H] in
theorem augmentationSeparatedSection_injective :
    Function.Injective
      (augmentationSeparatedSection (k := k) (H := H) (M := M)) :=
  Function.LeftInverse.injective
    (augmentationSeparatedQuotient_section (k := k) (H := H) (M := M))

/-- Lift a subspace of the separated quotient through the chosen section. -/
def liftSeparatedSubspace (E : Submodule k Msep) : Submodule k M :=
  Submodule.map
    (augmentationSeparatedSection (k := k) (H := H) (M := M)) E

omit [Coalgebra.IsCocomm k H] in
theorem finiteDimensional_liftSeparatedSubspace
    (E : Submodule k Msep) [FiniteDimensional k E] :
    FiniteDimensional k
      (liftSeparatedSubspace (k := k) (H := H) (M := M) E) := by
  change FiniteDimensional k
    (Submodule.map
      (augmentationSeparatedSection (k := k) (H := H) (M := M)) E)
  infer_instance

omit [Coalgebra.IsCocomm k H] in
theorem finrank_liftSeparatedSubspace
    (E : Submodule k Msep) [FiniteDimensional k E] :
    sfinrank k (liftSeparatedSubspace (k := k) (H := H) (M := M) E) =
      sfinrank k E := by
  rw [sfinrank, sfinrank]
  let f := (augmentationSeparatedSection (k := k) (H := H) (M := M)).domRestrict E
  have hrange : LinearMap.range f =
      liftSeparatedSubspace (k := k) (H := H) (M := M) E := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.property, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj fun x y hxy ↦
    Subtype.ext (augmentationSeparatedSection_injective
      (k := k) (H := H) (M := M) hxy)

omit [Coalgebra.IsCocomm k H] in
theorem liftSeparatedSubspace_iInf_comap_eq_bot
    (E : Submodule k Msep) :
    (⨅ n, WM n).comap
        (liftSeparatedSubspace (k := k) (H := H) (M := M) E).subtype = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨e, he, hxe⟩ := x.property
  have hxker : (x : M) ∈ LinearMap.ker qsep := by
    rw [augmentationSeparatedQuotient_ker]
    exact hx
  have hezero : e = 0 := by
    have hxzero : qsep (x : M) = 0 := hxker
    rw [← hxe, augmentationSeparatedQuotient_section] at hxzero
    exact hxzero
  subst e
  apply Subtype.ext
  simpa using hxe.symm

/-- Initial forms of a subspace of the separated quotient, viewed in the
original augmentation associated graded. -/
def separatedInitialSubspace (E : Submodule k Msep) : Submodule k grM :=
  initialSubspace (k := k) WM
    (liftSeparatedSubspace (k := k) (H := H) (M := M) E)

omit [Coalgebra.IsCocomm k H] in
theorem finiteDimensional_separatedInitialSubspace
    (E : Submodule k Msep) [FiniteDimensional k E] :
    FiniteDimensional k
      (separatedInitialSubspace (k := k) (H := H) (M := M) E) := by
  let _ : FiniteDimensional k
      (liftSeparatedSubspace (k := k) (H := H) (M := M) E) :=
    finiteDimensional_liftSeparatedSubspace E
  obtain ⟨N, hN⟩ := exists_filtration_comap_eq_bot WM
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M)) _
    (liftSeparatedSubspace_iInf_comap_eq_bot E)
  exact finiteDimensional_initialSubspace WM
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M)) _ N hN

omit [Coalgebra.IsCocomm k H] in
theorem finrank_separatedInitialSubspace
    (E : Submodule k Msep) [FiniteDimensional k E] :
    sfinrank k
        (separatedInitialSubspace (k := k) (H := H) (M := M) E) =
      sfinrank k E := by
  let _ : FiniteDimensional k
      (liftSeparatedSubspace (k := k) (H := H) (M := M) E) :=
    finiteDimensional_liftSeparatedSubspace E
  obtain ⟨N, hN⟩ := exists_filtration_comap_eq_bot WM
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M)) _
    (liftSeparatedSubspace_iInf_comap_eq_bot E)
  rw [separatedInitialSubspace]
  rw [sfinrank, finrank_initialSubspace WM
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_zero (k := k) (H := H) (M := M)) _ N hN]
  exact finrank_liftSeparatedSubspace E

omit [Coalgebra.IsCocomm k H] in
theorem separatedInitialSubspace_ne_bot
    (E : Submodule k Msep) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    separatedInitialSubspace (k := k) (H := H) (M := M) E ≠ ⊥ := by
  intro hbot
  have hdim := finrank_separatedInitialSubspace
    (k := k) (H := H) (M := M) E
  rw [hbot] at hdim
  have hErank : sfinrank k E = 0 := by simpa using hdim.symm
  apply hE
  rw [eq_bot_iff]
  intro x hx
  let _ : Subsingleton E :=
    (Module.finrank_eq_zero_iff_of_free k E).mp hErank
  exact congrArg E.subtype (show (⟨x, hx⟩ : E) = 0 from Subsingleton.elim _ _)

omit [Coalgebra.IsCocomm k H] in
/-- Initial forms commute with action expansion after passage to the
separated quotient, up to the inclusion needed for the Følner estimate. -/
theorem actionExpansion_separatedInitialSubspace_le
    (F : Submodule k grH) (E : Submodule k Msep) :
    actionExpansion F
        (separatedInitialSubspace (k := k) (H := H) (M := M) E) ≤
      separatedInitialSubspace (k := k) (H := H) (M := M)
        (actionExpansion
          (liftHomogeneousSubspace (k := k)
            (augmentationFiltration (k := k) (H := H)) F) E) := by
  refine (actionExpansion_initialSubspace_le (k := k) (H := H) (M := M)
    F (liftSeparatedSubspace (k := k) (H := H) (M := M) E)).trans ?_
  apply initialSubspace_le_of_mod_iInf
  intro x hx
  let Flift := liftHomogeneousSubspace (k := k)
    (augmentationFiltration (k := k) (H := H)) F
  let Etarget : Submodule k Msep := actionExpansion Flift E
  have hqx : qsep x ∈ Etarget := by
    apply (show Submodule.map qsep
        (actionExpansion Flift
          (liftSeparatedSubspace (k := k) (H := H) (M := M) E)) ≤ Etarget by
      rw [actionExpansion, Submodule.map_sup]
      apply sup_le
      · rintro _ ⟨z, ⟨e, he, rfl⟩, rfl⟩
        rw [augmentationSeparatedQuotient_section]
        exact Submodule.mem_sup_left he
      · rintro _ ⟨z, hz, rfl⟩
        rw [actionSubspace_eq_map₂] at hz
        induction hz using Submodule.iSup_induction' with
        | mem h y hy =>
            rcases hy with ⟨e, he, rfl⟩
            change Submodule.Quotient.mk ((h : H) • e) ∈ _
            change (h : H) • Submodule.Quotient.mk e ∈ _
            apply Submodule.mem_sup_right
            apply product_mem_actionSubspace h.property
            rcases he with ⟨z, hz, rfl⟩
            change qsep
              (augmentationSeparatedSection (k := k) (H := H) (M := M) z) ∈ E
            rw [augmentationSeparatedQuotient_section]
            exact hz
        | zero => simp
        | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb) ⟨x, hx, rfl⟩
  let y : M := augmentationSeparatedSection (k := k) (H := H) (M := M) (qsep x)
  have hy : y ∈ liftSeparatedSubspace (k := k) (H := H) (M := M) Etarget :=
    ⟨qsep x, hqx, rfl⟩
  refine ⟨y, hy, ?_⟩
  change x - y ∈ augmentationInfinity (k := k) (H := H) (M := M)
  rw [← augmentationSeparatedQuotient_ker]
  change qsep (x - y) = 0
  rw [map_sub, augmentationSeparatedQuotient_section, sub_self]

end

end HopfAmenability
