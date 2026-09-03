/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AugmentationAssociatedGraded

/-!
# Theorem J: amenability of the associated graded module coalgebra

This file exposes the final main theorem of the accompanying article using
the concrete augmentation filtration, separated quotient, and associated
graded structures constructed in the supporting files.
-/

namespace HopfAmenability

universe u v

variable {k : Type u} {H M : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- **Theorem J.** Amenability passes to the concrete augmentation-associated
graded Hopf-module coalgebra.  All quotient, lifting, and leading-symbol data
are constructed canonically in the supporting files. -/
theorem isAmenable_associatedGraded
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra
      (k := k) (H := AugmentationGradedHopf (k := k) (H := H))
      (M := AugmentationGradedModule (k := k) (H := H) (M := M)) := by
  let _ : AddCommGroup
      (AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    inferInstanceAs (AddCommGroup (Π₀ n,
      AugmentationGradedModulePiece (k := k) (H := H) (M := M) n))
  have hsep := hM.augmentationSeparated
  apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
  intro F hF ε hε
  let _ : FiniteDimensional k F := hF
  let Flift := liftHomogeneousSubspace (k := k)
    (augmentationFiltration (k := k) (H := H)) F
  let _ : FiniteDimensional k Flift :=
    finiteDimensional_liftHomogeneousSubspace _ F
  obtain ⟨E, hE, hEfd, hEratio⟩ :=
    hsep.hasActionFolnerSubspaces Flift inferInstance ε hε
  let _ : FiniteDimensional k E := hEfd
  let Egr := separatedInitialSubspace (k := k) (H := H) (M := M) E
  let _ : FiniteDimensional k Egr :=
    finiteDimensional_separatedInitialSubspace E
  have hsourcefd : FiniteDimensional k (actionExpansion Flift E) :=
    finiteDimensional_actionExpansion Flift E
  have hinitialfd : FiniteDimensional k
      (separatedInitialSubspace (k := k) (H := H) (M := M)
        (actionExpansion Flift E)) :=
    finiteDimensional_separatedInitialSubspace _
  have hdimExpansion :
      sfinrank k (actionExpansion F Egr) ≤
        sfinrank k (actionExpansion Flift E) := by
    calc
      sfinrank k (actionExpansion F Egr) ≤
          sfinrank k (separatedInitialSubspace
            (k := k) (H := H) (M := M) (actionExpansion Flift E)) :=
        Submodule.finrank_mono
          (actionExpansion_separatedInitialSubspace_le F E)
      _ = sfinrank k (actionExpansion Flift E) :=
        finrank_separatedInitialSubspace _
  refine ⟨Egr, separatedInitialSubspace_ne_bot E hE, inferInstance, ?_⟩
  calc
    (sfinrank k (actionExpansion F Egr) : ℚ) ≤
        sfinrank k (actionExpansion Flift E) := by exact_mod_cast hdimExpansion
    _ ≤ (1 + ε) * sfinrank k E := hEratio
    _ = (1 + ε) * sfinrank k Egr := by
      rw [finrank_separatedInitialSubspace E]

/-- Manuscript-letter alias for Theorem J. -/
theorem theoremJ_associatedGraded
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra
      (k := k) (H := AugmentationGradedHopf (k := k) (H := H))
      (M := AugmentationGradedModule (k := k) (H := H) (M := M)) :=
  isAmenable_associatedGraded hM

end HopfAmenability
