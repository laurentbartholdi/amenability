/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.DensityFiltration
import Amenability.SubcoalgebraBasic

/-!
# The density filtration for subcoalgebras inside a finite ambient subspace

The density files work with a finite-dimensional ambient vector space `V`.
For an infinite-dimensional coalgebra `H`, we therefore fix a finite-dimensional
subspace `G ≤ H` and work with subspaces of the subtype `G`.

A subspace `C : Submodule k G` is declared admissible when its image in `H`
is a subcoalgebra.

The only coalgebraic lattice fact not proved in `SubcoalgebraBasic.lean` is
closure under intersections.  This file takes precisely that fact as an
explicit hypothesis `hInf`.  A later file will discharge it.
-/

open Module

namespace UnifiedRounding

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H]

/--
The image in `H` of a subspace of the subtype `G`.
-/
def ambientImage
    (G : Submodule k H) (C : Submodule k G) :
    Submodule k H :=
  C.map G.subtype

@[simp]
theorem ambientImage_bot
    (G : Submodule k H) :
    ambientImage G (⊥ : Submodule k G) = ⊥ := by
  simp [ambientImage]

@[simp]
theorem ambientImage_sup
    (G : Submodule k H) (C D : Submodule k G) :
    ambientImage G (C ⊔ D : Submodule k G) =
      ambientImage G C ⊔ ambientImage G D := by
  simp [ambientImage, Submodule.map_sup]

@[simp]
theorem ambientImage_inf
    (G : Submodule k H) (C D : Submodule k G) :
    ambientImage G (C ⊓ D : Submodule k G) =
      ambientImage G C ⊓ ambientImage G D := by
  have hGinj : Function.Injective G.subtype := by
    intro x y hxy
    exact Subtype.ext hxy
  exact Submodule.map_inf_of_injective G.subtype hGinj C D

/--
The exact intersection-closure hypothesis required to instantiate the abstract
density filtration with subcoalgebras inside `G`.
-/
def SubcoalgebraInfClosed [Coalgebra k H] (G : Submodule k H) : Prop :=
  ∀ C D : Submodule k G,
    IsSubcoalgebra (k := k) (ambientImage G C) →
    IsSubcoalgebra (k := k) (ambientImage G D) →
    IsSubcoalgebra (k := k) (ambientImage G (C ⊓ D : Submodule k G))

/--
Subcoalgebras inside `G` form an `AdmissibleFamily`, assuming closure under
intersections.
-/
def subcoalgebraAdmissibleFamily [Coalgebra k H]
    (G : Submodule k H)
    (hInf : SubcoalgebraInfClosed (k := k) G) :
    AdmissibleFamily k G where
  admissible C := IsSubcoalgebra (k := k) (ambientImage G C)
  bot_admissible := by
    simpa using (isSubcoalgebra_bot (k := k) (H := H))
  sup_admissible := by
    intro C D hC hD
    rw [ambientImage_sup]
    exact hC.sup hD
  inf_admissible := by
    intro C D hC hD
    exact hInf C D hC hD

variable (G : Submodule k H)
variable [FiniteDimensional k G] [Coalgebra k H]
variable (hInf : SubcoalgebraInfClosed (k := k) G)

/--
The density filtration on subcoalgebras contained in the finite ambient
subspace `G`.
-/
noncomputable def coalgebraDensitySubspace
    (E : Submodule k G) (t : ℚ) :
    Submodule k G :=
  densitySubspace (subcoalgebraAdmissibleFamily G hInf) E t

/--
The image in `H` of the chosen density subspace is a subcoalgebra.
-/
theorem coalgebraDensitySubspace_isSubcoalgebra
    (E : Submodule k G) (t : ℚ) :
    IsSubcoalgebra (k := k)
      (ambientImage G (coalgebraDensitySubspace G hInf E t)) := by
  exact densitySubspace_admissible
    (subcoalgebraAdmissibleFamily G hInf) E t

/--
The coalgebra density filtration is decreasing.
-/
theorem coalgebraDensitySubspace_antitone
    (E : Submodule k G) :
    Antitone fun t : ℚ => coalgebraDensitySubspace G hInf E t := by
  exact densitySubspace_antitone
    (subcoalgebraAdmissibleFamily G hInf) E

/--
For `t > 1`, the coalgebra density subspace is zero.
-/
theorem coalgebraDensitySubspace_eq_bot_of_one_lt
    (E : Submodule k G) {t : ℚ} (ht : 1 < t) :
    coalgebraDensitySubspace G hInf E t = ⊥ := by
  exact densitySubspace_eq_bot_of_one_lt
    (subcoalgebraAdmissibleFamily G hInf) E ht

/--
Semistability of the coalgebra density filtration.
-/
theorem coalgebraDensitySubspace_semistable
    (E : Submodule k G) (t : ℚ)
    {B : Submodule k G}
    (hB : IsSubcoalgebra (k := k) (ambientImage G B)) :
    t * ((finrank k (coalgebraDensitySubspace G hInf E t) : ℚ) -
      (finrank k B : ℚ)) ≤
      (intersectionRank E (coalgebraDensitySubspace G hInf E t) : ℚ) -
        (intersectionRank E B : ℚ) := by
  exact densitySubspace_semistable
    (subcoalgebraAdmissibleFamily G hInf) E t hB

end UnifiedRounding
