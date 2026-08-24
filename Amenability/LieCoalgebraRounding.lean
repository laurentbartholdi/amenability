/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.LieDensityTransfer
import Amenability.DensityRounding
import Amenability.FundamentalTheoremCoalgebra

/-!
# Rounding finite-dimensional Lie-module subspaces to subcoalgebras
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
variable [Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M]

/-- Finite-ambient Lie rounding for a subspace internal to a finite
subcoalgebra. -/
theorem exists_finiteSubcoalgebra_lie_ratio_le_internal
    (F : Submodule k L) [FiniteDimensional k F]
    (G : FiniteSubcoalgebra k M) (E : Submodule k G.carrier)
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F (ambientImage G.carrier E)) : ℚ) /
            (finrank k E : ℚ) := by
  let FG : Submodule k M := lieExpansion F G.carrier
  let FE : Submodule k FG :=
    (lieExpansion F (ambientImage G.carrier E)).comap FG.subtype
  let sourceFamily : AdmissibleFamily k G.carrier :=
    subcoalgebraAdmissibleFamily G.carrier
      (subcoalgebraInfClosed (k := k) (H := M) G.carrier)
  let targetFamily : AdmissibleFamily k FG :=
    subcoalgebraAdmissibleFamily FG
      (subcoalgebraInfClosed (k := k) (H := M) FG)
  have hFG : lieExpansion F (ambientImage G.carrier E) ≤ FG := by
    apply lieExpansion_mono_right F
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hFEImage : ambientImage FG FE =
      lieExpansion F (ambientImage G.carrier E) :=
    ambientImage_comap_eq_of_le FG _ hFG
  have hA : ∃ A : Submodule k G.carrier,
      sourceFamily.admissible A ∧ E ≤ A := by
    refine ⟨⊤, ?_, le_top⟩
    change IsSubcoalgebra (k := k) (ambientImage G.carrier ⊤)
    have htop : ambientImage G.carrier (⊤ : Submodule k G.carrier) =
        G.carrier := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [htop]
    exact G.isSubcoalgebra
  let b : ℚ → ℚ := fun t =>
    sfinrank k (lieExpansion F
      (ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t)))
  have hb_nonneg : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ b t := by
    intro t ht0 ht1
    change (0 : ℚ) ≤ (sfinrank k (lieExpansion F
      (ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t))) : ℚ)
    exact_mod_cast (Nat.zero_le (sfinrank k (lieExpansion F
      (ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t)))))
  have hb_le : ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      b t ≤ finrank k (densitySubspace targetFamily FE t) := by
    intro t ht0 ht1
    have hle := lieExpansion_subcoalgebraDensitySubspace_le F G.carrier E t
    let FCt : Submodule k M := lieExpansion F
      (ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t))
    have hFCtFG : FCt ≤ FG := by
      apply lieExpansion_mono_right F
      rintro x ⟨y, -, rfl⟩
      exact y.2
    let FCtInt : Submodule k FG := FCt.comap FG.subtype
    have hFCtImage : ambientImage FG FCtInt = FCt :=
      ambientImage_comap_eq_of_le FG FCt hFCtFG
    have hleInt : FCtInt ≤ subcoalgebraDensitySubspace FG FE t := by
      intro x hx
      have hx' : (x : M) ∈ FCt := hx
      rcases hle hx' with ⟨y, hy, hyx⟩
      exact Subtype.ext hyx ▸ hy
    have hfin := Submodule.finrank_mono hleInt
    change (finrank k FCt : ℚ) ≤
      finrank k (subcoalgebraDensitySubspace FG FE t)
    rw [← hFCtImage, finrank_ambientImage FG]
    exact_mod_cast hfin
  obtain ⟨t, htmem, htpos, hratio⟩ :=
    exists_ratio_le_of_density_filtrations
      sourceFamily targetFamily E FE hE hA b hb_nonneg hb_le
  change 0 < finrank k
    (subcoalgebraDensitySubspace G.carrier E t) at htpos
  change
    (sfinrank k (lieExpansion F
        (ambientImage G.carrier
          (subcoalgebraDensitySubspace G.carrier E t))) : ℚ) /
        (finrank k (subcoalgebraDensitySubspace G.carrier E t) : ℚ) ≤
      (finrank k FE : ℚ) / (finrank k E : ℚ) at hratio
  let Ct : Submodule k G.carrier :=
    subcoalgebraDensitySubspace G.carrier E t
  let C : FiniteSubcoalgebra k M :=
    finiteSubcoalgebraOfAmbientImage G.carrier Ct
      (subcoalgebraDensitySubspace_isSubcoalgebra G.carrier E t)
  refine ⟨C, ?_, ?_⟩
  · intro hC
    have hdimC : finrank k C.carrier = finrank k Ct :=
      finrank_ambientImage G.carrier Ct
    have : finrank k Ct = 0 := by
      rw [← hdimC, hC]
      simp
    exact (Nat.ne_of_gt htpos) this
  · change
      (sfinrank k (lieExpansion F (ambientImage G.carrier Ct)) : ℚ) /
          (finrank k (ambientImage G.carrier Ct) : ℚ) ≤
        (sfinrank k (lieExpansion F (ambientImage G.carrier E)) : ℚ) /
          (finrank k E : ℚ)
    rw [finrank_ambientImage G.carrier Ct]
    unfold sfinrank
    rw [← hFEImage, finrank_ambientImage FG]
    exact hratio

/-- Ambient wrapper once the original subspace lies in a finite
subcoalgebra. -/
theorem exists_finiteSubcoalgebra_lie_ratio_le_of_le
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥)
    (G : FiniteSubcoalgebra k M) (hEG : E ≤ G.carrier) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F E) : ℚ) /
            (finrank k E : ℚ) := by
  let Eint : Submodule k G.carrier := E.comap G.carrier.subtype
  have hEintImage : ambientImage G.carrier Eint = E :=
    ambientImage_comap_eq_of_le G.carrier E hEG
  have hEint : Eint ≠ ⊥ := by
    intro hbot
    apply hE
    rw [← hEintImage, hbot, ambientImage_bot]
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_lie_ratio_le_internal F G Eint hEint
  refine ⟨C, hC, ?_⟩
  have hdimE : finrank k E = finrank k Eint := by
    calc
      finrank k E = finrank k (ambientImage G.carrier Eint) := by
        rw [hEintImage]
      _ = finrank k Eint := finrank_ambientImage G.carrier Eint
  rw [hEintImage, ← hdimE] at hratio
  exact hratio

/-- Every nonzero finite-dimensional subspace of a Lie-module coalgebra can
be rounded to a nonzero finite subcoalgebra with no larger expansion ratio. -/
theorem exists_finiteSubcoalgebra_lie_ratio_le
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F E) : ℚ) /
            (finrank k E : ℚ) := by
  obtain ⟨G, hEG⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule E
  exact exists_finiteSubcoalgebra_lie_ratio_le_of_le F E hE G hEG

/-- The data selected by Lie-module coalgebra rounding. -/
structure LieRoundingResult
    (F : Submodule k L) (E : Submodule k M) where
  C : FiniteSubcoalgebra k M
  ne_bot : C.carrier ≠ ⊥
  ratio_le :
    (sfinrank k (lieExpansion F C.carrier) : ℚ) /
        (finrank k C.carrier : ℚ) ≤
      (sfinrank k (lieExpansion F E) : ℚ) /
        (finrank k E : ℚ)

/-- A chosen finite subcoalgebra supplied by the Lie rounding theorem. -/
noncomputable def lieRounding
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    LieRoundingResult F E :=
  let h := exists_finiteSubcoalgebra_lie_ratio_le F E hE
  let C := Classical.choose h
  ⟨C, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

@[simp]
theorem lieRounding_ne_bot
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    (lieRounding F E hE).C.carrier ≠ ⊥ :=
  (lieRounding F E hE).ne_bot

theorem lieRounding_ratio_le
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    (sfinrank k
        (lieExpansion F (lieRounding F E hE).C.carrier) : ℚ) /
          (finrank k (lieRounding F E hE).C.carrier : ℚ) ≤
      (sfinrank k (lieExpansion F E) : ℚ) /
        (finrank k E : ℚ) :=
  (lieRounding F E hE).ratio_le

end

end HopfAmenability
