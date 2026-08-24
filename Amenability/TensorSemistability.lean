/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.RightCoideal
import Amenability.TwoSidedCoideal
import Amenability.TensorRightComodule

/-!
# Tensor amplification of coalgebra semistability
-/

open Module TensorProduct

namespace Coalgebra

noncomputable section

universe u v w

variable {k : Type u} {C : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup W] [Module k W]

/-- The left coaction on a tensor copy of the regular coalgebra. -/
noncomputable def tensorLeftCoaction :
    W ⊗[k] C →ₗ[k] C ⊗[k] (W ⊗[k] C) :=
  (_root_.TensorProduct.comm k (W ⊗[k] C) C).toLinearMap ∘ₗ
    (_root_.TensorProduct.assoc k W C C).symm.toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm k C C).toLinearMap.lTensor W) ∘ₗ
        (Coalgebra.comul (R := k) (A := C)).lTensor W

/-- A subspace of `W ⊗ C` stable under the left regular coaction of `C`. -/
def IsTensorLeftSubcomodule (Z : Submodule k (W ⊗[k] C)) : Prop :=
  ∀ z, z ∈ Z → tensorLeftCoaction (k := k) (C := C) (W := W) z ∈
    LinearMap.range (Z.subtype.lTensor C)

@[simp]
theorem tensorLeftCoaction_tmul (w : W) (c : C) :
    tensorLeftCoaction (k := k) (C := C) (W := W) (w ⊗ₜ[k] c) =
      (_root_.TensorProduct.comm k (W ⊗[k] C) C)
        ((_root_.TensorProduct.assoc k W C C).symm
          (w ⊗ₜ[k]
            (_root_.TensorProduct.comm k C C)
              (Coalgebra.comul (R := k) (A := C) c))) := rfl

/-- Contracting the auxiliary tensor factor intertwines the left coaction
with comultiplication. -/
theorem comul_leftContract_eq
    (ell : W →ₗ[k] k) (z : W ⊗[k] C) :
    Coalgebra.comul (R := k) (A := C)
        (TensorProduct.leftContract ell z) =
      (TensorProduct.leftContract ell).lTensor C
        (tensorLeftCoaction (k := k) (C := C) (W := W) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hz'
  | tmul w c =>
      simp only [TensorProduct.leftContract_tmul, map_smul]
      rw [tensorLeftCoaction_tmul]
      generalize hq : Coalgebra.comul (R := k) (A := C) c = q
      clear hq c
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
          simpa only [map_add, smul_add, tmul_add] using
            congrArg₂ (fun x y => x + y) hq hq'
      | tmul c d =>
          simp [TensorProduct.leftContract_tmul]

/-- Inclusion of an auxiliary subspace intertwines the left coactions. -/
theorem tensorLeftCoaction_rTensor
    {L : Type*} [AddCommGroup L] [Module k L]
    (i : L →ₗ[k] W) (z : L ⊗[k] C) :
    tensorLeftCoaction (k := k) (C := C) (W := W) (i.rTensor C z) =
      (i.rTensor C).lTensor C
        (tensorLeftCoaction (k := k) (C := C) (W := L) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hz'
  | tmul l c =>
      simp only [LinearMap.rTensor_tmul]
      rw [tensorLeftCoaction_tmul, tensorLeftCoaction_tmul]
      generalize hq : Coalgebra.comul (R := k) (A := C) c = q
      clear hq c
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
          simpa only [map_add, tmul_add] using congrArg₂ (fun x y => x + y) hq hq'
      | tmul c d => rfl

end

end Coalgebra

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {C : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [FiniteDimensional k C]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Coalgebra semistability is preserved after tensor amplification. -/
theorem tensor_semistable
    (U : Submodule k C) (t : ℚ)
    (hsem : ∀ B : Submodule k C,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B))
    (Z : Submodule k (W ⊗[k] C))
    (hZ : IsRightSubcomodule (C := C) Z)
    (hZleft : Coalgebra.IsTensorLeftSubcomodule (k := k) (C := C) Z) :
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
      have hBleft : Coalgebra.IsLeftCoideal B := by
        intro b hb
        rcases hb with ⟨z, hz, rfl⟩
        rcases hZleft z hz with ⟨q, hq⟩
        let phiB : Z →ₗ[k] B :=
          LinearMap.codRestrict B (phi.comp Z.subtype) (fun z => ⟨z, z.2, rfl⟩)
        refine ⟨phiB.lTensor C q, ?_⟩
        have hnatural : ∀ q : C ⊗[k] Z,
            (B.subtype.lTensor C) (phiB.lTensor C q) =
              (phi.lTensor C) (Z.subtype.lTensor C q) := by
          intro q
          induction q using TensorProduct.induction_on with
          | zero => simp
          | add q q' hq hq' => simpa only [map_add] using congrArg₂ (fun x y => x + y) hq hq'
          | tmul c z => rfl
        rw [hnatural, hq]
        exact (Coalgebra.comul_leftContract_eq ell z).symm
      have hBcoal : IsSubcoalgebra (k := k) B :=
        Coalgebra.isSubcoalgebra_of_twoSidedCoideal hBcomodule hBleft
      have hZ0comodule : IsRightSubcomodule (C := C) Z0 :=
        IsRightSubcomodule.comap Z i hZ hiMap
      have hZ0left : Coalgebra.IsTensorLeftSubcomodule
          (k := k) (C := C) Z0 := by
        intro x hx
        let j : L ⊗[k] C →ₗ[k] (W ⊗[k] C) ⧸ Z := Z.mkQ.comp i
        have hkerj : LinearMap.ker j = Z0 := by
          ext y
          rw [LinearMap.mem_ker]
          change Z.mkQ (i y) = 0 ↔ i y ∈ Z
          exact Submodule.Quotient.mk_eq_zero Z
        rw [← hkerj]
        have hexact := Module.Flat.lTensor_exact (R := k) C
          (N := LinearMap.ker j) (N' := L ⊗[k] C)
          (f := (LinearMap.ker j).subtype) (g := j)
          (LinearMap.exact_subtype_ker_map j)
        rw [← hexact.linearMap_ker_eq, LinearMap.mem_ker]
        have hix : i x ∈ Z := hx
        rcases hZleft (i x) hix with ⟨q, hq⟩
        have hquot : (Z.mkQ.lTensor C)
            (Coalgebra.tensorLeftCoaction (k := k) (C := C) (W := W) (i x)) = 0 := by
          rw [← hq]
          rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
          have hcomp : Z.mkQ.comp Z.subtype = 0 := by
            ext z
            exact (Submodule.Quotient.mk_eq_zero Z).2 z.2
          rw [hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
        have hjzero : (j.lTensor C)
            (Coalgebra.tensorLeftCoaction (k := k) (C := C) (W := L) x) = 0 := by
          change (Z.mkQ.lTensor C)
              (Coalgebra.tensorLeftCoaction (k := k) (C := C) (W := W)
                (L.subtype.rTensor C x)) = 0 at hquot
          rw [Coalgebra.tensorLeftCoaction_rTensor L.subtype x] at hquot
          change ((Z.mkQ.comp i).lTensor C)
              (Coalgebra.tensorLeftCoaction (k := k) (C := C) (W := L) x) = 0
          rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
          exact hquot
        exact hjzero
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
      have hIH := ih (finrank k L) hLlt Z0 hZ0comodule hZ0left rfl
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
