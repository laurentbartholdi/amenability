/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.DensityRounding
import Amenability.DensityProductTransferPrimal
import Amenability.SubcoalgebraAmbient

/-!
# Finite coalgebraic rounding

This file combines finite density averaging with the pointwise compatibility
of the coalgebra density filtration with left multiplication.
-/

open Coalgebra Module

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/--
Finite coalgebraic rounding for a subspace internal to a fixed finite
subcoalgebra.
-/
theorem exists_finiteSubcoalgebra_ratio_le_internal
    (F : FiniteSubcoalgebra k H)
    (G : FiniteSubcoalgebra k H)
    (E : Submodule k G.carrier)
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k H,
      C.carrier ≠ ⊥ ∧
        (finrank k (F.carrier * C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (finrank k (F.carrier * ambientImage G.carrier E) : ℚ) /
            (finrank k E : ℚ) := by
  let FG : Submodule k H := F.carrier * G.carrier
  let : FiniteDimensional k FG := finiteDimensional_mul F.carrier G.carrier
  let FE : Submodule k FG :=
    (F.carrier * ambientImage G.carrier E).comap FG.subtype
  let sourceFamily : AdmissibleFamily k G.carrier :=
    subcoalgebraAdmissibleFamily G.carrier
      (subcoalgebraInfClosed (k := k) (H := H) G.carrier)
  let targetFamily : AdmissibleFamily k FG :=
    subcoalgebraAdmissibleFamily FG
      (subcoalgebraInfClosed (k := k) (H := H) FG)
  have hFG : F.carrier * ambientImage G.carrier E ≤ FG := by
    apply subcoalgebra_mul_mono le_rfl
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hFEImage : ambientImage FG FE =
      F.carrier * ambientImage G.carrier E :=
    ambientImage_comap_eq_of_le FG _ hFG
  have hA : ∃ A : Submodule k G.carrier,
      sourceFamily.admissible A ∧ E ≤ A := by
    refine ⟨⊤, ?_, le_top⟩
    change IsSubcoalgebra (k := k) (ambientImage G.carrier ⊤)
    have htop : ambientImage G.carrier (⊤ : Submodule k G.carrier) =
        G.carrier := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [htop]
    exact G.isSubcoalgebra
  let b : ℚ → ℚ := fun t =>
    finrank k
      (F.carrier * ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t))
  have hb_nonneg : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ b t := by
    intro t ht0 ht1
    change (0 : ℚ) ≤ finrank k
      (F.carrier * ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t))
    exact_mod_cast (Nat.zero_le (finrank k
      (F.carrier * ambientImage G.carrier
        (subcoalgebraDensitySubspace G.carrier E t))))
  have hb_le : ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      b t ≤ finrank k (densitySubspace targetFamily FE t) := by
    intro t ht0 ht1
    have hle := mul_subcoalgebraDensitySubspace_le_primal F G.carrier E t
    let FCt : Submodule k H := F.carrier * ambientImage G.carrier
      (subcoalgebraDensitySubspace G.carrier E t)
    have hFCtFG : FCt ≤ FG := by
      apply subcoalgebra_mul_mono le_rfl
      rintro x ⟨y, hy, rfl⟩
      exact y.2
    let FCtInt : Submodule k FG := FCt.comap FG.subtype
    have hFCtImage : ambientImage FG FCtInt = FCt :=
      ambientImage_comap_eq_of_le FG FCt hFCtFG
    have hleInt : FCtInt ≤ subcoalgebraDensitySubspace FG FE t := by
      intro x hx
      have hx' : (x : H) ∈ FCt := hx
      have himage := hle hx'
      rcases himage with ⟨y, hy, hyx⟩
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
    (finrank k
        (F.carrier * ambientImage G.carrier
          (subcoalgebraDensitySubspace G.carrier E t)) : ℚ) /
        (finrank k (subcoalgebraDensitySubspace G.carrier E t) : ℚ) ≤
      (finrank k FE : ℚ) / (finrank k E : ℚ) at hratio
  let Ct : Submodule k G.carrier :=
    subcoalgebraDensitySubspace G.carrier E t
  let C : FiniteSubcoalgebra k H :=
    finiteSubcoalgebraOfAmbientImage G.carrier Ct
      (subcoalgebraDensitySubspace_isSubcoalgebra G.carrier E t)
  refine ⟨C, ?_, ?_⟩
  · intro hC
    have hdimC : finrank k C.carrier = finrank k Ct := by
      exact finrank_ambientImage G.carrier Ct
    have : finrank k Ct = 0 := by
      rw [← hdimC, hC]
      simp
    exact (Nat.ne_of_gt htpos) this
  · change
      (finrank k (F.carrier * ambientImage G.carrier Ct) : ℚ) /
          (finrank k (ambientImage G.carrier Ct) : ℚ) ≤
        (finrank k (F.carrier * ambientImage G.carrier E) : ℚ) /
          (finrank k E : ℚ)
    rw [finrank_ambientImage G.carrier Ct]
    rw [← hFEImage, finrank_ambientImage FG]
    exact hratio

/--
Finite coalgebraic rounding for an ambient finite-dimensional subspace once it
is placed in a finite subcoalgebra.
-/
theorem exists_finiteSubcoalgebra_ratio_le_of_le
    (F : FiniteSubcoalgebra k H)
    (E : Submodule k H)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥)
    (G : FiniteSubcoalgebra k H)
    (hEG : E ≤ G.carrier) :
    ∃ C : FiniteSubcoalgebra k H,
      C.carrier ≠ ⊥ ∧
        (finrank k (F.carrier * C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (finrank k (F.carrier * E) : ℚ) /
            (finrank k E : ℚ) := by
  let Eint : Submodule k G.carrier := E.comap G.carrier.subtype
  have hEintImage : ambientImage G.carrier Eint = E :=
    ambientImage_comap_eq_of_le G.carrier E hEG
  have hEint : Eint ≠ ⊥ := by
    intro hbot
    apply hE
    rw [← hEintImage, hbot, ambientImage_bot]
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_ratio_le_internal F G Eint hEint
  refine ⟨C, hC, ?_⟩
  have hdimE : finrank k E = finrank k Eint := by
    calc
      finrank k E = finrank k (ambientImage G.carrier Eint) := by
        rw [hEintImage]
      _ = finrank k Eint := finrank_ambientImage G.carrier Eint
  rw [hEintImage, ← hdimE] at hratio
  exact hratio

end

end UnifiedRounding
