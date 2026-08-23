/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FiniteSubcoalgebraTransferAmbient
import Amenability.CoalgebraDensityTransfer

/-!
# Product functoriality of the coalgebra density filtration
-/

open Coalgebra Module

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/--
Multiplication by `F` carries the density subcoalgebra of `E` into the
density subcoalgebra of `FE`, using `G` and `F * G` as the two finite
ambient spaces.
-/
theorem mul_subcoalgebraDensitySubspace_le
    (F : FiniteSubcoalgebra k H)
    (S : SplitDualFiltration k F.Dual)
    (G : Submodule k H) [FiniteDimensional k G]
    (E : Submodule k G) (t : ℚ) :
    F.carrier *
        ambientImage G (subcoalgebraDensitySubspace G E t) ≤
      ambientImage (F.carrier * G)
        (subcoalgebraDensitySubspace (F.carrier * G)
          ((F.carrier * ambientImage G E).comap
            (F.carrier * G).subtype) t) := by
  let Ct : Submodule k G := subcoalgebraDensitySubspace G E t
  let Camb : Submodule k H := ambientImage G Ct
  have hCamb : IsSubcoalgebra (k := k) Camb := by
    exact subcoalgebraDensitySubspace_isSubcoalgebra G E t
  let Cfin : FiniteSubcoalgebra k H :=
    finiteSubcoalgebraOfAmbientImage G Ct hCamb
  let FG : Submodule k H := F.carrier * G
  let : FiniteDimensional k FG := finiteDimensional_mul F.carrier G
  let FE : Submodule k FG :=
    (F.carrier * ambientImage G E).comap FG.subtype
  let Dt : Submodule k FG := subcoalgebraDensitySubspace FG FE t
  let FCt : Submodule k FG :=
    (F.carrier * Camb).comap FG.subtype
  have hCambG : Camb ≤ G := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hFCtFG : F.carrier * Camb ≤ FG :=
    subcoalgebra_mul_mono le_rfl hCambG
  have hFCtImage : ambientImage FG FCt = F.carrier * Camb := by
    exact ambientImage_comap_eq_of_le FG (F.carrier * Camb) hFCtFG
  have hFCt : IsSubcoalgebra (k := k) (ambientImage FG FCt) := by
    rw [hFCtImage]
    exact F.isSubcoalgebra.mul hCamb
  let Uamb : Submodule k H := ambientImage G (E ⊓ Ct)
  have hUambCamb : Uamb ≤ Camb := by
    exact Submodule.map_mono inf_le_right
  let U : Submodule k Cfin.carrier := Uamb.comap Cfin.carrier.subtype
  have hUimage : ambientImage Cfin.carrier U = Uamb := by
    exact ambientImage_comap_eq_of_le Cfin.carrier Uamb hUambCamb
  have hsem :
      ∀ B : Submodule k Cfin.carrier,
        IsSubcoalgebra (k := k) B →
          t *
              ((finrank k Cfin.carrier : ℚ) - (finrank k B : ℚ)) ≤
            (finrank k U : ℚ) -
              (finrank k (U ⊓ B : Submodule k Cfin.carrier) : ℚ) := by
    intro B hB
    let Bamb : Submodule k H := ambientImage Cfin.carrier B
    have hBamb : IsSubcoalgebra (k := k) Bamb :=
      (isSubcoalgebra_ambientImage_iff Cfin.carrier Cfin.isSubcoalgebra B).2 hB
    have hBambG : Bamb ≤ G := by
      rintro x ⟨b, hb, rfl⟩
      exact hCambG b.2
    let BG : Submodule k G := Bamb.comap G.subtype
    have hBGimage : ambientImage G BG = Bamb :=
      ambientImage_comap_eq_of_le G Bamb hBambG
    have hBG : IsSubcoalgebra (k := k) (ambientImage G BG) := by
      rw [hBGimage]
      exact hBamb
    have hBGCt : BG ≤ Ct := by
      intro x hx
      change (x : H) ∈ Bamb at hx
      rcases hx with ⟨b, hb, hbx⟩
      have : (x : H) ∈ Camb := by
        rw [← hbx]
        exact b.2
      rcases this with ⟨c, hc, hcx⟩
      exact Subtype.ext hcx.symm ▸ hc
    have hs := subcoalgebraDensitySubspace_semistable G E t hBG
    change
      t * ((finrank k Ct : ℚ) - (finrank k BG : ℚ)) ≤
        (finrank k (E ⊓ Ct : Submodule k G) : ℚ) -
          (finrank k (E ⊓ BG : Submodule k G) : ℚ) at hs
    have hUBimage :
        ambientImage Cfin.carrier (U ⊓ B) =
          ambientImage G (E ⊓ BG) := by
      rw [ambientImage_inf, hUimage, ambientImage_inf, hBGimage]
      change ambientImage G (E ⊓ Ct) ⊓ Bamb = ambientImage G E ⊓ Bamb
      rw [ambientImage_inf, inf_assoc]
      apply congrArg (ambientImage G E ⊓ ·)
      exact inf_eq_right.mpr (by
        rintro x ⟨b, hb, rfl⟩
        exact b.2)
    have hdimC : finrank k Cfin.carrier = finrank k Ct := by
      change finrank k (ambientImage G Ct) = finrank k Ct
      exact finrank_ambientImage G Ct
    have hdimB : finrank k B = finrank k BG := by
      calc
        finrank k B = finrank k Bamb := (finrank_ambientImage Cfin.carrier B).symm
        _ = finrank k BG := by rw [← hBGimage]; exact finrank_ambientImage G BG
    have hdimU : finrank k U = finrank k (E ⊓ Ct : Submodule k G) := by
      calc
        finrank k U = finrank k Uamb := by
          rw [← hUimage]
          exact (finrank_ambientImage Cfin.carrier U).symm
        _ = finrank k (E ⊓ Ct : Submodule k G) := finrank_ambientImage G (E ⊓ Ct)
    have hdimUB :
        finrank k (U ⊓ B : Submodule k Cfin.carrier) =
          finrank k (E ⊓ BG : Submodule k G) := by
      calc
        _ = finrank k (ambientImage Cfin.carrier (U ⊓ B)) :=
          (finrank_ambientImage Cfin.carrier (U ⊓ B)).symm
        _ = finrank k (ambientImage G (E ⊓ BG)) := by rw [hUBimage]
        _ = _ := finrank_ambientImage G (E ⊓ BG)
    rw [hdimC, hdimB, hdimU, hdimUB]
    exact hs
  let W : Submodule k FG :=
    (ambientImage (FiniteSubcoalgebra.mul F Cfin).carrier
      (FiniteSubcoalgebra.leftProductSubspace F Cfin U)).comap FG.subtype
  have hWimage :
      ambientImage FG W =
        ambientImage (FiniteSubcoalgebra.mul F Cfin).carrier
          (FiniteSubcoalgebra.leftProductSubspace F Cfin U) := by
    apply ambientImage_comap_eq_of_le
    rw [SplitDualFiltration.ambientImage_leftProductSubspace F Cfin U]
    rw [hUimage]
    exact subcoalgebra_mul_mono le_rfl hUambCamb |>.trans hFCtFG
  have hWFCt : W ≤ FCt := by
    intro x hx
    change (x : H) ∈ F.carrier * Camb
    have hx' : (x : H) ∈ ambientImage FG W := ⟨x, hx, rfl⟩
    rw [hWimage,
      SplitDualFiltration.ambientImage_leftProductSubspace F Cfin U,
      hUimage] at hx'
    exact subcoalgebra_mul_mono le_rfl hUambCamb hx'
  have hWFE : W ≤ FE := by
    intro x hx
    change (x : H) ∈ F.carrier * ambientImage G E
    have hx' : (x : H) ∈ ambientImage FG W := ⟨x, hx, rfl⟩
    rw [hWimage,
      SplitDualFiltration.ambientImage_leftProductSubspace F Cfin U,
      hUimage] at hx'
    exact subcoalgebra_mul_mono le_rfl (Submodule.map_mono inf_le_left) hx'
  rw [← hFCtImage]
  apply Submodule.map_mono
  apply le_subcoalgebraDensitySubspace_of_transfer FG t hFCt hWFE hWFCt
  let Damb : Submodule k H := ambientImage FG (FCt ⊓ Dt)
  have hDambFC : Damb ≤ (FiniteSubcoalgebra.mul F Cfin).carrier := by
    change ambientImage FG (FCt ⊓ Dt) ≤
      (FiniteSubcoalgebra.mul F Cfin).carrier
    rw [ambientImage_inf, hFCtImage]
    exact inf_le_left
  have hDamb : IsSubcoalgebra (k := k) Damb := by
    change IsSubcoalgebra (k := k) (ambientImage FG (FCt ⊓ Dt))
    rw [ambientImage_inf]
    exact hFCt.inf_of_tensorSquareIntersection
      tensorSquareIntersectionProperty
      (subcoalgebraDensitySubspace_isSubcoalgebra FG FE t)
  have htransfer := S.finiteSubcoalgebra_transfer_ambient F Cfin U Damb
    hDambFC t hDamb hsem
  have hmulcarrier :
      (FiniteSubcoalgebra.mul F Cfin).carrier = ambientImage FG FCt := by
    change F.carrier * Camb = ambientImage FG FCt
    exact hFCtImage.symm
  have hWintersection :
      ambientImage (FiniteSubcoalgebra.mul F Cfin).carrier
            (FiniteSubcoalgebra.leftProductSubspace F Cfin U) ⊓ Damb =
        ambientImage FG (W ⊓ (FCt ⊓ Dt)) := by
    rw [← hWimage]
    change ambientImage FG W ⊓ ambientImage FG (FCt ⊓ Dt) = _
    rw [← ambientImage_inf]
  have hdimFC :
      finrank k (FiniteSubcoalgebra.mul F Cfin).carrier = finrank k FCt := by
    rw [hmulcarrier]
    exact finrank_ambientImage FG FCt
  have hdimD : finrank k Damb = finrank k (FCt ⊓ Dt : Submodule k FG) := by
    change finrank k (ambientImage FG (FCt ⊓ Dt)) = _
    exact finrank_ambientImage FG (FCt ⊓ Dt)
  have hdimW :
      finrank k
          (ambientImage (FiniteSubcoalgebra.mul F Cfin).carrier
            (FiniteSubcoalgebra.leftProductSubspace F Cfin U)) =
        finrank k W := by
    rw [← hWimage]
    exact finrank_ambientImage FG W
  have hdimWintersection :
      finrank k
          (ambientImage (FiniteSubcoalgebra.mul F Cfin).carrier
              (FiniteSubcoalgebra.leftProductSubspace F Cfin U) ⊓ Damb :
            Submodule k H) =
        finrank k (W ⊓ (FCt ⊓ Dt) : Submodule k FG) := by
    rw [hWintersection]
    exact finrank_ambientImage FG (W ⊓ (FCt ⊓ Dt))
  rw [hdimFC, hdimD, hdimW, hdimWintersection] at htransfer
  exact htransfer

end

end UnifiedRounding
