/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.RightCoideal
import Amenability.TensorRightComodule

/-!
# Tensor amplification of coalgebra semistability
-/

open Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {C : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Coalgebra.IsCocomm k C] [FiniteDimensional k C]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Coalgebra semistability is preserved after tensor amplification. -/
theorem tensor_semistable
    (U : Submodule k C) (t : ℚ)
    (hsem : ∀ B : Submodule k C,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B))
    (Z : Submodule k (W ⊗[k] C))
    (hZ : IsRightSubcomodule (C := C) Z) :
    t * ((finrank k W : ℚ) * finrank k C - sfinrank k Z) ≤
      (finrank k W : ℚ) * sfinrank k U -
        sfinrank k (Z ⊓ tensorSubspace (k := k) W U) := by
  induction hn : finrank k W using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hn0 : n = 0
    · have hW0 : finrank k W = 0 := hn.trans hn0
      have hTensor0 : finrank k (W ⊗[k] C) = 0 := by
        rw [Module.finrank_tensorProduct, hW0, zero_mul]
      have hZ0 : sfinrank k Z = 0 := by
        change finrank k Z = 0
        exact Nat.eq_zero_of_le_zero
          (show finrank k Z ≤ 0 by
            simpa [hTensor0] using
              (Submodule.finrank_mono
                (show Z ≤ (⊤ : Submodule k (W ⊗[k] C)) from le_top)))
      have hN0 :
          sfinrank k (Z ⊓ tensorSubspace (k := k) W U) = 0 := by
        exact Nat.eq_zero_of_le_zero
          (show sfinrank k (Z ⊓ tensorSubspace (k := k) W U) ≤ 0 by
            simpa [hTensor0] using
              (Submodule.finrank_mono
                (show Z ⊓ tensorSubspace (k := k) W U ≤
                  (⊤ : Submodule k (W ⊗[k] C)) from le_top)))
      simp [hn0, hZ0, hN0]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hWpos : 0 < finrank k W := hn ▸ hnpos
      obtain ⟨ell, a, ha⟩ :=
        exists_leftFunctional_apply_eq_one (W := W) hWpos
      let L : Submodule k W := LinearMap.ker ell
      let phi : W ⊗[k] C →ₗ[k] C :=
        TensorProduct.leftContract ell
      let i : L ⊗[k] C →ₗ[k] W ⊗[k] C :=
        L.subtype.rTensor C
      let B : Submodule k C := Z.map phi
      let Z0 : Submodule k (L ⊗[k] C) := Z.comap i
      have hLrank : finrank k W = finrank k L + 1 :=
        finrank_ker_add_one_of_apply_eq_one ell a ha
      have hLlt : finrank k L < n := by omega
      have hphiMap :
          IsRightComoduleMap (C := C) phi :=
        leftContract_isRightComoduleMap ell
      have hiMap : IsRightComoduleMap (C := C) i :=
        rTensor_isRightComoduleMap L.subtype
      have hBcomodule : IsRightSubcomodule (C := C) B :=
        IsRightSubcomodule.map Z phi hZ hphiMap
      have hBcoal : IsSubcoalgebra (k := k) B :=
        isSubcoalgebra_of_isRightSubcomodule hBcomodule
      have hZ0comodule : IsRightSubcomodule (C := C) Z0 :=
        IsRightSubcomodule.comap Z i hZ hiMap
      have hphiKer : LinearMap.ker phi = LinearMap.range i := by
        exact ker_leftContract_eq_range_rTensor ell a ha
      let : Module.Free k C := Module.Free.of_divisionRing k C
      have hiinj : Function.Injective i :=
        Module.Flat.rTensor_preserves_injective_linearMap
          L.subtype L.subtype_injective
      have hpreimageTensor : ∀ x : L ⊗[k] C,
          i x ∈ tensorSubspace (k := k) W U ↔
            x ∈ tensorSubspace (k := k) L U := by
        intro x
        constructor
        · intro hx
          have hxzero : U.mkQ.lTensor W (i x) = 0 := by
            rcases hx with ⟨z, hz⟩
            rw [← hz]
            rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
            have hcomp : U.mkQ.comp U.subtype = 0 := by ext; simp
            rw [hcomp]
            simp
          have hcomm :
              U.mkQ.lTensor W ∘ₗ i =
                (L.subtype.rTensor (C ⧸ U)) ∘ₗ U.mkQ.lTensor L := by
            ext l c
            rfl
          have hsmallzero : U.mkQ.lTensor L x = 0 := by
            have hinj : Function.Injective
                (L.subtype.rTensor (C ⧸ U)) :=
              Module.Flat.rTensor_preserves_injective_linearMap
                L.subtype L.subtype_injective
            apply hinj
            simpa only [map_zero, ← LinearMap.comp_apply, ← hcomm] using hxzero
          rw [tensorSubspace, ← lTensor_mkQ L U]
          exact hsmallzero
        · rintro ⟨z, rfl⟩
          refine ⟨L.subtype.rTensor U z, ?_⟩
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add z z' hz hz' =>
              simpa only [map_add] using congrArg₂ (· + ·) hz hz'
          | tmul l u => rfl
      have hZdim :
          sfinrank k Z = sfinrank k Z0 + sfinrank k B := by
        exact sfinrank_eq_comap_add_map_of_ker_eq_range
          i hiinj phi hphiKer Z
      let N : Submodule k (W ⊗[k] C) :=
        Z ⊓ tensorSubspace (k := k) W U
      let N0 : Submodule k (L ⊗[k] C) :=
        Z0 ⊓ tensorSubspace (k := k) L U
      have hNcomap : N.comap i = N0 := by
        ext x
        exact and_congr Iff.rfl (hpreimageTensor x)
      have hNmap : N.map phi ≤ U ⊓ B := by
        rintro y ⟨x, hx, rfl⟩
        refine ⟨?_, ?_⟩
        · rcases hx.2 with ⟨z, hz⟩
          rw [← hz]
          clear hz
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add z z' hz hz' =>
              rw [map_add, map_add]
              exact U.add_mem hz hz'
          | tmul w u =>
              change ell w • (u : C) ∈ U
              exact U.smul_mem _ u.2
        · exact ⟨x, hx.1, rfl⟩
      have hNrank :
          sfinrank k N =
            sfinrank k N0 + sfinrank k (N.map phi) := by
        rw [← hNcomap]
        exact sfinrank_eq_comap_add_map_of_ker_eq_range
          i hiinj phi hphiKer N
      have hNdim :
          sfinrank k N ≤ sfinrank k N0 + sfinrank k (U ⊓ B) := by
        rw [hNrank]
        exact Nat.add_le_add_left (Submodule.finrank_mono hNmap) _
      have hIH := ih (finrank k L) hLlt Z0 hZ0comodule rfl
      have hBsem := hsem B hBcoal
      have hZdimQ : (sfinrank k Z : ℚ) =
          sfinrank k Z0 + sfinrank k B := by exact_mod_cast hZdim
      have hNdimQ : (sfinrank k N : ℚ) ≤
          sfinrank k N0 + sfinrank k (U ⊓ B) := by
        exact_mod_cast hNdim
      have hLrankQ : (finrank k W : ℚ) =
          finrank k L + 1 := by exact_mod_cast hLrank
      rw [← hn]
      change t * ((finrank k W : ℚ) * finrank k C - sfinrank k Z) ≤
        (finrank k W : ℚ) * sfinrank k U - sfinrank k N
      change t * ((finrank k L : ℚ) * finrank k C - sfinrank k Z0) ≤
        (finrank k L : ℚ) * sfinrank k U - sfinrank k N0 at hIH
      rw [hLrankQ, hZdimQ]
      linarith

end

end HopfAmenability
