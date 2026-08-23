/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TensorSquareIntersection

/-!
# The unconditional coalgebra density filtration

Over a field, intersections of subcoalgebras are automatically subcoalgebras.
This file removes the temporary `SubcoalgebraInfClosed` argument from the
definitions in `CoalgebraDensity.lean`.
-/

open Module

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

variable (G : Submodule k H)
variable [FiniteDimensional k G]

/--
The density filtration on subcoalgebras contained in a finite-dimensional
ambient subspace `G`.
-/
noncomputable def subcoalgebraDensitySubspace
    (E : Submodule k G) (t : ℚ) :
    Submodule k G :=
  coalgebraDensitySubspace G
    (subcoalgebraInfClosed (k := k) (H := H) G) E t

/--
The image in the ambient coalgebra of the chosen density subspace is a
subcoalgebra.
-/
theorem subcoalgebraDensitySubspace_isSubcoalgebra
    (E : Submodule k G) (t : ℚ) :
    IsSubcoalgebra (k := k)
      (ambientImage G (subcoalgebraDensitySubspace G E t)) := by
  exact coalgebraDensitySubspace_isSubcoalgebra G
    (subcoalgebraInfClosed (k := k) (H := H) G) E t

/--
The subcoalgebra density filtration is decreasing.
-/
theorem subcoalgebraDensitySubspace_antitone
    (E : Submodule k G) :
    Antitone fun t : ℚ => subcoalgebraDensitySubspace G E t := by
  exact coalgebraDensitySubspace_antitone G
    (subcoalgebraInfClosed (k := k) (H := H) G) E

/--
For `t > 1`, the chosen density subspace is zero.
-/
theorem subcoalgebraDensitySubspace_eq_bot_of_one_lt
    (E : Submodule k G) {t : ℚ} (ht : 1 < t) :
    subcoalgebraDensitySubspace G E t = ⊥ := by
  exact coalgebraDensitySubspace_eq_bot_of_one_lt G
    (subcoalgebraInfClosed (k := k) (H := H) G) E ht

/--
Semistability of the subcoalgebra density filtration.
-/
theorem subcoalgebraDensitySubspace_semistable
    (E : Submodule k G) (t : ℚ)
    {B : Submodule k G}
    (hB : IsSubcoalgebra (k := k) (ambientImage G B)) :
    t * ((finrank k (subcoalgebraDensitySubspace G E t) : ℚ) -
      (finrank k B : ℚ)) ≤
      (intersectionRank E (subcoalgebraDensitySubspace G E t) : ℚ) -
        (intersectionRank E B : ℚ) := by
  exact coalgebraDensitySubspace_semistable G
    (subcoalgebraInfClosed (k := k) (H := H) G) E t hB

end HopfAmenability
