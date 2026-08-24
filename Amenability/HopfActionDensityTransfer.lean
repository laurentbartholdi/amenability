/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfActionTransfer
import Amenability.CoalgebraDensityTransfer

/-!
# Functoriality of the density filtration under a Hopf action
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M]
variable [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- A Hopf action carries a density subcoalgebra into the corresponding
density subcoalgebra in the expanded ambient space. -/
theorem actionSubspace_subcoalgebraDensitySubspace_le
    (F : FiniteSubcoalgebra k H)
    (G : Submodule k M) [FiniteDimensional k G]
    (E : Submodule k G) (t : ℚ) :
    actionSubspace F.carrier
        (ambientImage G (subcoalgebraDensitySubspace G E t)) ≤
      ambientImage (actionSubspace F.carrier G)
        (subcoalgebraDensitySubspace (actionSubspace F.carrier G)
          ((actionSubspace F.carrier (ambientImage G E)).comap
            (actionSubspace F.carrier G).subtype) t) := by
  let Ct : Submodule k G := subcoalgebraDensitySubspace G E t
  let Camb : Submodule k M := ambientImage G Ct
  have hCamb : IsSubcoalgebra (k := k) Camb :=
    subcoalgebraDensitySubspace_isSubcoalgebra G E t
  let Cfin : FiniteSubcoalgebra k M :=
    finiteSubcoalgebraOfAmbientImage G Ct hCamb
  let FG : Submodule k M := actionSubspace F.carrier G
  let : FiniteDimensional k FG :=
    finiteDimensional_actionSubspace (k := k) (H := H) (M := M) F.carrier G
  let FE : Submodule k FG :=
    (actionSubspace F.carrier (ambientImage G E)).comap FG.subtype
  let Dt : Submodule k FG := subcoalgebraDensitySubspace FG FE t
  let FCt : Submodule k FG :=
    (actionSubspace F.carrier Camb).comap FG.subtype
  have hCambG : Camb ≤ G := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hFCtFG : actionSubspace F.carrier Camb ≤ FG :=
    actionSubspace_mono_right F.carrier hCambG
  have hFCtImage : ambientImage FG FCt = actionSubspace F.carrier Camb :=
    ambientImage_comap_eq_of_le FG (actionSubspace F.carrier Camb) hFCtFG
  have hFCt : IsSubcoalgebra (k := k) (ambientImage FG FCt) := by
    rw [hFCtImage]
    exact IsSubcoalgebra.actionSubspace (k := k) (H := H) (M := M)
      F.isSubcoalgebra hCamb
  let Uamb : Submodule k M := ambientImage G (E ⊓ Ct)
  have hUambCamb : Uamb ≤ Camb := Submodule.map_mono inf_le_right
  let U : Submodule k Cfin.carrier := Uamb.comap Cfin.carrier.subtype
  have hUimage : ambientImage Cfin.carrier U = Uamb :=
    ambientImage_comap_eq_of_le Cfin.carrier Uamb hUambCamb
  have hsem : ∀ B : Submodule k Cfin.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k Cfin.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B) := by
    intro B hB
    let Bamb : Submodule k M := ambientImage Cfin.carrier B
    have hBamb : IsSubcoalgebra (k := k) Bamb :=
      (isSubcoalgebra_ambientImage_iff Cfin.carrier Cfin.isSubcoalgebra B).mpr hB
    have hBambG : Bamb ≤ G := by
      rintro x ⟨b, -, rfl⟩
      exact hCambG b.2
    let BG : Submodule k G := Bamb.comap G.subtype
    have hBGimage : ambientImage G BG = Bamb :=
      ambientImage_comap_eq_of_le G Bamb hBambG
    have hBG : IsSubcoalgebra (k := k) (ambientImage G BG) := by
      rw [hBGimage]
      exact hBamb
    have hBGCt : BG ≤ Ct := by
      intro x hx
      change (x : M) ∈ Bamb at hx
      rcases hx with ⟨b, hb, hbx⟩
      have : (x : M) ∈ Camb := by
        rw [← hbx]
        exact b.2
      rcases this with ⟨c, hc, hcx⟩
      exact Subtype.ext hcx.symm ▸ hc
    have hs := subcoalgebraDensitySubspace_semistable G E t hBG
    change t * ((finrank k Ct : ℚ) - finrank k BG) ≤
      (sfinrank k (E ⊓ Ct) : ℚ) - sfinrank k (E ⊓ BG) at hs
    have hUBimage : ambientImage Cfin.carrier (U ⊓ B) =
        ambientImage G (E ⊓ BG) := by
      rw [ambientImage_inf, hUimage, ambientImage_inf, hBGimage]
      change ambientImage G (E ⊓ Ct) ⊓ Bamb = ambientImage G E ⊓ Bamb
      rw [ambientImage_inf, inf_assoc]
      apply congrArg (ambientImage G E ⊓ ·)
      exact inf_eq_right.mpr (by
        rintro x ⟨b, -, rfl⟩
        exact b.2)
    have hdimC : finrank k Cfin.carrier = finrank k Ct := by
      change finrank k (ambientImage G Ct) = finrank k Ct
      exact finrank_ambientImage G Ct
    have hdimB : finrank k B = finrank k BG := by
      calc
        finrank k B = finrank k Bamb :=
          (finrank_ambientImage Cfin.carrier B).symm
        _ = finrank k BG := by
          rw [← hBGimage]
          exact finrank_ambientImage G BG
    have hdimU : finrank k U = sfinrank k (E ⊓ Ct) := by
      calc
        finrank k U = finrank k Uamb := by
          rw [← hUimage]
          exact (finrank_ambientImage Cfin.carrier U).symm
        _ = sfinrank k (E ⊓ Ct) := finrank_ambientImage G (E ⊓ Ct)
    have hdimUB : sfinrank k (U ⊓ B) = sfinrank k (E ⊓ BG) := by
      calc
        _ = finrank k (ambientImage Cfin.carrier (U ⊓ B)) :=
          (finrank_ambientImage Cfin.carrier (U ⊓ B)).symm
        _ = finrank k (ambientImage G (E ⊓ BG)) := by rw [hUBimage]
        _ = _ := finrank_ambientImage G (E ⊓ BG)
    unfold sfinrank at hdimU hdimUB ⊢
    rw [hdimC, hdimB, hdimU, hdimUB]
    exact hs
  let Wamb : Submodule k M := actionSubspace F.carrier Uamb
  let W : Submodule k FG := Wamb.comap FG.subtype
  have hWFG : Wamb ≤ FG :=
    actionSubspace_mono_right F.carrier (hUambCamb.trans hCambG)
  have hWimage : ambientImage FG W = Wamb :=
    ambientImage_comap_eq_of_le FG Wamb hWFG
  have hWFCt : W ≤ FCt := by
    intro x hx
    change (x : M) ∈ actionSubspace F.carrier Camb
    have hx' : (x : M) ∈ ambientImage FG W := ⟨x, hx, rfl⟩
    rw [hWimage] at hx'
    exact actionSubspace_mono_right F.carrier hUambCamb hx'
  have hWFE : W ≤ FE := by
    intro x hx
    change (x : M) ∈ actionSubspace F.carrier (ambientImage G E)
    have hx' : (x : M) ∈ ambientImage FG W := ⟨x, hx, rfl⟩
    rw [hWimage] at hx'
    exact actionSubspace_mono_right F.carrier (Submodule.map_mono inf_le_left) hx'
  rw [← hFCtImage]
  apply Submodule.map_mono
  apply le_subcoalgebraDensitySubspace_of_transfer FG t hFCt hWFE hWFCt
  let Damb : Submodule k M := ambientImage FG (FCt ⊓ Dt)
  have hDambFC : Damb ≤ actionSubspace F.carrier Cfin.carrier := by
    change ambientImage FG (FCt ⊓ Dt) ≤ actionSubspace F.carrier Camb
    rw [ambientImage_inf, hFCtImage]
    exact inf_le_left
  have hDamb : IsSubcoalgebra (k := k) Damb := by
    change IsSubcoalgebra (k := k) (ambientImage FG (FCt ⊓ Dt))
    rw [ambientImage_inf]
    exact hFCt.inf_of_tensorSquareIntersection tensorSquareIntersectionProperty
      (subcoalgebraDensitySubspace_isSubcoalgebra FG FE t)
  have htransfer := finiteSubcoalgebra_action_transfer_ambient F Cfin U Damb hDambFC hDamb t hsem
  rw [hUimage] at htransfer
  have hWintersection : Wamb ⊓ Damb =
      ambientImage FG (W ⊓ (FCt ⊓ Dt)) := by
    rw [← hWimage]
    change ambientImage FG W ⊓ ambientImage FG (FCt ⊓ Dt) = _
    rw [← ambientImage_inf]
  have hdimFC : sfinrank k (actionSubspace F.carrier Cfin.carrier) = finrank k FCt := by
    change finrank k (actionSubspace F.carrier Camb) = finrank k FCt
    rw [← hFCtImage]
    exact finrank_ambientImage FG FCt
  have hdimD : finrank k Damb = sfinrank k (FCt ⊓ Dt) :=
    finrank_ambientImage FG (FCt ⊓ Dt)
  have hdimW : finrank k Wamb = finrank k W := by
    rw [← hWimage]
    exact finrank_ambientImage FG W
  have hdimWintersection : sfinrank k (Wamb ⊓ Damb) =
      sfinrank k (W ⊓ (FCt ⊓ Dt)) := by
    rw [hWintersection]
    exact finrank_ambientImage FG (W ⊓ (FCt ⊓ Dt))
  unfold sfinrank at htransfer hdimFC hdimD hdimW hdimWintersection
  rw [hdimFC, hdimD, hdimW, hdimWintersection] at htransfer
  exact htransfer

end

end HopfAmenability
