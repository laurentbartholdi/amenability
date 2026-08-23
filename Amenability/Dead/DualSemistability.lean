/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.DensityFiltration
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual form of the semistability inequality

Let `V` be finite-dimensional, `U ≤ V`, and put `K = Uᗮ`, the dual
annihilator.  For `B ≤ V`, put `I = Bᗮ`.

The identity
```
dim I - dim (I ∩ K) = dim U - dim (U ∩ B)
```
is the numerical bridge used in the transfer lemma.
-/

namespace HopfAmenability

open Module

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/--
The codimension lost by intersecting `Bᗮ` with `Uᗮ` equals the
dimension lost by intersecting `U` with `B`.
-/
theorem dualAnnihilator_difference
    (U B : Submodule k V) :
    (finrank k B.dualAnnihilator : ℚ) -
        (finrank k
          (B.dualAnnihilator ⊓ U.dualAnnihilator :
            Submodule k (Module.Dual k V)) : ℚ) =
      (finrank k U : ℚ) -
        (sfinrank k (U ⊓ B) : ℚ) := by
  have hBnat :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq B
  have hBUnat :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq
      (B ⊔ U : Submodule k V)
  have hmodnat :=
    Submodule.finrank_sup_add_finrank_inf_eq B U
  have hB :
      (finrank k B : ℚ) +
          (finrank k B.dualAnnihilator : ℚ) =
        (finrank k V : ℚ) := by
    exact_mod_cast hBnat
  have hBU :
      (sfinrank k (B ⊔ U) : ℚ) +
          (finrank k
            (B ⊔ U : Submodule k V).dualAnnihilator : ℚ) =
        (finrank k V : ℚ) := by
    exact_mod_cast hBUnat
  have hmod' :
      (sfinrank k (B ⊔ U) : ℚ) +
          (sfinrank k (B ⊓ U) : ℚ) =
        (finrank k B : ℚ) + (finrank k U : ℚ) := by
    exact_mod_cast hmodnat
  have hmod :
      (sfinrank k (B ⊔ U) : ℚ) +
          (sfinrank k (U ⊓ B) : ℚ) =
        (finrank k B : ℚ) + (finrank k U : ℚ) := by
    rw [inf_comm U B]
    exact hmod'
  have hann :
      B.dualAnnihilator ⊓ U.dualAnnihilator =
        (B ⊔ U : Submodule k V).dualAnnihilator := by
    rw [Submodule.dualAnnihilator_sup_eq]
  rw [hann]
  linarith

/--
Semistability in `V` transfers verbatim to the annihilator formulation.

The premise is the form obtained from the density filtration:
`dim U - dim(U ∩ B) ≥ t (dim V - dim B)`.
-/
theorem semistable_to_dualAnnihilator
    (U B : Submodule k V) (t : ℚ)
    (hsem :
      t * ((finrank k V : ℚ) - (finrank k B : ℚ)) ≤
        (finrank k U : ℚ) -
          (sfinrank k (U ⊓ B) : ℚ)) :
    t * (finrank k B.dualAnnihilator : ℚ) ≤
      (finrank k B.dualAnnihilator : ℚ) -
        (finrank k
          (B.dualAnnihilator ⊓ U.dualAnnihilator :
            Submodule k (Module.Dual k V)) : ℚ) := by
  have hBnat :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq B
  have hB :
      (finrank k B : ℚ) +
          (finrank k B.dualAnnihilator : ℚ) =
        (finrank k V : ℚ) := by
    exact_mod_cast hBnat
  have hdiff := dualAnnihilator_difference U B
  have hcodim :
      (finrank k V : ℚ) - (finrank k B : ℚ) =
        (finrank k B.dualAnnihilator : ℚ) := by
    linarith [hB]
  rw [hcodim] at hsem
  rw [hdiff]
  exact hsem

end HopfAmenability
