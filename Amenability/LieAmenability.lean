/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.LieCoalgebraRounding

/-!
# Subcoalgebra Følner sets for amenable Lie modules
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k]
variable [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]

/-- The finite-dimensional Følner condition for a Lie module. -/
def IsAmenableLieModule : Prop :=
  ∀ (F : Submodule k L), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k M,
        E ≠ ⊥ ∧ FiniteDimensional k E ∧
          (sfinrank k (lieExpansion F E) : ℚ) ≤
            (1 + ε) * sfinrank k E

variable [Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M]

/-- In a Lie-module coalgebra, the Følner subspaces witnessing amenability
may be chosen to be finite subcoalgebras. -/
theorem IsAmenableLieModule.exists_finiteSubcoalgebra_folner
    (hM : IsAmenableLieModule (k := k) (L := L) (M := M))
    (F : Submodule k L) [FiniteDimensional k F]
    (ε : ℚ) (hε : 0 < ε) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) ≤
          (1 + ε) * finrank k C.carrier := by
  obtain ⟨E, hE, hEfd, hFolner⟩ := hM F inferInstance ε hε
  let : FiniteDimensional k E := hEfd
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_lie_ratio_le F E hE
  refine ⟨C, hC, ?_⟩
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let : Nontrivial C.carrier := Submodule.nontrivial_iff_ne_bot.mpr hC
  have hEpos : (0 : ℚ) < finrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hCpos : (0 : ℚ) < finrank k C.carrier := by
    exact_mod_cast Module.finrank_pos (R := k) (M := C.carrier)
  have hsource :
      (sfinrank k (lieExpansion F E) : ℚ) / finrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).mpr hFolner
  exact (div_le_iff₀ hCpos).mp (hratio.trans hsource)

end

end HopfAmenability
