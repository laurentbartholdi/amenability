/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.DensityTransfer
import Amenability.CoalgebraDensityClosed
import Mathlib.LinearAlgebra.Dimension.Finrank
/-!
# Transfer estimates force inclusion in the coalgebra density filtration

This is the coalgebra wrapper around
`le_densitySubspace_of_transfer`.

Everything still takes place in a fixed finite-dimensional ambient
subspace `G ≤ H`. The only coalgebraic input is that `C` is admissible,
i.e. its ambient image is a subcoalgebra.
-/

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

variable (G : Submodule k H)
variable [FiniteDimensional k G]

open Module

/--
If `C` is a subcoalgebra inside `G`, `U ≤ E ∩ C`, and the transferred
dimension inequality holds against the intersection of `C` with the
density maximizer for `E`, then `C` is contained in that maximizer.
-/
theorem le_subcoalgebraDensitySubspace_of_transfer
    {E U C : Submodule k G}
    (t : ℚ)
    (hC : IsSubcoalgebra (k := k) (ambientImage G C))
    (hUE : U ≤ E)
    (hUC : U ≤ C)
    (htransfer :
      t * ((finrank k C : ℚ) -
        (finrank k
          (C ⊓ subcoalgebraDensitySubspace G E t :
            Submodule k G) : ℚ)) ≤
      (finrank k U : ℚ) -
        (finrank k
          (U ⊓ (C ⊓ subcoalgebraDensitySubspace G E t) :
            Submodule k G) : ℚ)) :
                C ≤ subcoalgebraDensitySubspace G E t := by
  let 𝓛 :=
    subcoalgebraAdmissibleFamily G
      (subcoalgebraInfClosed (k := k) (H := H) G)
  change
    t * ((finrank k C : ℚ) -
      (finrank k
        (C ⊓ densitySubspace 𝓛 E t :
          Submodule k G) : ℚ)) ≤
    (finrank k U : ℚ) -
      (finrank k
        (U ⊓ (C ⊓ densitySubspace 𝓛 E t) :
          Submodule k G) : ℚ) at htransfer
  change C ≤ densitySubspace 𝓛 E t
  exact le_densitySubspace_of_transfer
    𝓛 t hC hUE hUC htransfer

end HopfAmenability
