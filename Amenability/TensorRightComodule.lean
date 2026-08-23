/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.ComoduleMap
import Amenability.SubmoduleFinrank
import Amenability.TensorContraction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor copies of the regular right comodule
-/

open Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w x y

variable {k : Type u} {C : Type v} {W : Type w} {X : Type x}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- The standard right-comodule coaction on a tensor product. -/
noncomputable def tensorRightComoduleCoaction :
    W ⊗[k] C →ₗ[k] (W ⊗[k] C) ⊗[k] C :=
  (TensorProduct.assoc k W C C).symm.toLinearMap ∘ₗ
    (Coalgebra.comul (R := k) (A := C)).lTensor W

@[simp]
theorem tensorRightComoduleCoaction_tmul (w : W) (c : C) :
    tensorRightComoduleCoaction (k := k) (C := C) (W := W) (w ⊗ₜ[k] c) =
      (TensorProduct.assoc k W C C).symm
        (w ⊗ₜ[k] Coalgebra.comul (R := k) (A := C) c) := by
  rfl

/-- A tensor product with the regular right comodule is naturally a right
comodule. -/
noncomputable instance tensorRightComodule : RightComodule k C (W ⊗[k] C) where
  coaction := tensorRightComoduleCoaction
  coassoc := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [tensorRightComoduleCoaction]
    | add z z' hz hz' =>
        simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul w c =>
        let prepend : C ⊗[k] (C ⊗[k] C) →ₗ[k]
            (W ⊗[k] C) ⊗[k] (C ⊗[k] C) :=
          (TensorProduct.assoc k W C (C ⊗[k] C)).symm.toLinearMap ∘ₗ
            TensorProduct.mk k W (C ⊗[k] (C ⊗[k] C)) w
        have hleftGeneric : ∀ q : C ⊗[k] C,
            TensorProduct.assoc k (W ⊗[k] C) C C
                ((tensorRightComoduleCoaction (k := k) (C := C) (W := W)).rTensor C
                  ((TensorProduct.assoc k W C C).symm (w ⊗ₜ[k] q))) =
              prepend (TensorProduct.assoc k C C C
                ((Coalgebra.comul (R := k) (A := C)).rTensor C
                  q)) := by
          intro q
          induction q using TensorProduct.induction_on with
          | zero => simp [tensorRightComoduleCoaction, prepend]
          | add q q' hq1 hq2 =>
              simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hq1 hq2
          | tmul c₁ c₂ =>
              simp only [TensorProduct.assoc_symm_tmul,
                LinearMap.rTensor_tmul, tensorRightComoduleCoaction_tmul,
                prepend, LinearMap.comp_apply]
              generalize hr : Coalgebra.comul (R := k) (A := C) c₁ = r
              clear hr c₁
              induction r using TensorProduct.induction_on with
              | zero => simp
              | add r r' hr1 hr2 =>
                  simpa only [map_add, add_tmul, tmul_add] using
                    congrArg₂ (· + ·) hr1 hr2
              | tmul d₁ d₂ => rfl
        have hrightGeneric : ∀ q : C ⊗[k] C,
            (Coalgebra.comul (R := k) (A := C)).lTensor (W ⊗[k] C)
                ((TensorProduct.assoc k W C C).symm (w ⊗ₜ[k] q)) =
              prepend ((Coalgebra.comul (R := k) (A := C)).lTensor C
                q) := by
          intro q
          induction q using TensorProduct.induction_on with
          | zero => simp [prepend]
          | add q q' hq1 hq2 =>
              simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hq1 hq2
          | tmul c₁ c₂ =>
              simp only [TensorProduct.assoc_symm_tmul,
                LinearMap.lTensor_tmul, prepend, LinearMap.comp_apply]
              generalize hr : Coalgebra.comul (R := k) (A := C) c₂ = r
              clear hr c₂
              induction r using TensorProduct.induction_on with
              | zero => simp
              | add r r' hr1 hr2 =>
                  simpa only [map_add, tmul_add] using
                    congrArg₂ (· + ·) hr1 hr2
              | tmul d₁ d₂ => rfl
        have hleft := hleftGeneric (Coalgebra.comul (R := k) (A := C) c)
        have hright := hrightGeneric (Coalgebra.comul (R := k) (A := C) c)
        simp only [LinearMap.comp_apply]
        calc
          _ = prepend (TensorProduct.assoc k C C C
              ((Coalgebra.comul (R := k) (A := C)).rTensor C
                (Coalgebra.comul (R := k) (A := C) c))) := hleft
          _ = prepend ((Coalgebra.comul (R := k) (A := C)).lTensor C
              (Coalgebra.comul (R := k) (A := C) c)) := by
                rw [Coalgebra.coassoc_apply]
          _ = _ := hright.symm
  counit := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [tensorRightComoduleCoaction]
    | add z z' hz hz' =>
        simpa only [map_add, LinearMap.id_apply] using
          congrArg₂ (· + ·) hz hz'
    | tmul w c =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply,
          tensorRightComoduleCoaction_tmul]
        have hgeneric : ∀ q : C ⊗[k] C,
            TensorProduct.rid k (W ⊗[k] C)
                ((Coalgebra.counit (R := k) (A := C)).lTensor (W ⊗[k] C)
                  ((TensorProduct.assoc k W C C).symm (w ⊗ₜ[k] q))) =
              w ⊗ₜ[k] TensorProduct.rid k C
                ((Coalgebra.counit (R := k) (A := C)).lTensor C q) := by
          intro q
          induction q using TensorProduct.induction_on with
          | zero => simp
          | add q q' hq hq' =>
              simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hq hq'
          | tmul c₁ c₂ =>
              simp only [TensorProduct.assoc_symm_tmul,
                LinearMap.lTensor_tmul,
                TensorProduct.rid_tmul, tmul_smul, smul_tmul']
        calc
          _ = w ⊗ₜ[k] TensorProduct.rid k C
              ((Coalgebra.counit (R := k) (A := C)).lTensor C
                (Coalgebra.comul (R := k) (A := C) c)) :=
            hgeneric (Coalgebra.comul (R := k) (A := C) c)
          _ = w ⊗ₜ[k] c := by
            rw [Coalgebra.lTensor_counit_comul]
            simp

@[simp]
theorem tensorRightComodule_coaction_tmul (w : W) (c : C) :
    RightComodule.coaction (k := k) (C := C) (M := W ⊗[k] C)
        (w ⊗ₜ[k] c) =
      (TensorProduct.assoc k W C C).symm
        (w ⊗ₜ[k] Coalgebra.comul (R := k) (A := C) c) := by
  exact tensorRightComoduleCoaction_tmul w c

/-- Tensoring a linear map with the identity of C gives a comodule map. -/
theorem rTensor_isRightComoduleMap
    {W₁ : Type x} {W₂ : Type y}
    [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂]
    (f : W₁ →ₗ[k] W₂) :
    IsRightComoduleMap (C := C) (f.rTensor C) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul w c =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul,
        tensorRightComodule_coaction_tmul]
      generalize hq : Coalgebra.comul (R := k) (A := C) c = q
      clear hq c
      induction q using TensorProduct.induction_on with
      | zero => rfl
      | add q q' hq1 hq2 =>
          simpa only [map_add, tmul_add] using congrArg₂ (· + ·) hq1 hq2
      | tmul c₁ c₂ => rfl

/-- Contraction of the tensor-copy coordinate is a comodule map to the
regular comodule. -/
theorem leftContract_isRightComoduleMap
    (ell : W →ₗ[k] k) :
    IsRightComoduleMap (C := C)
      (TensorProduct.leftContract ell : W ⊗[k] C →ₗ[k] C) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul w c =>
      change Coalgebra.comul (R := k) (A := C) (ell w • c) =
        (TensorProduct.leftContract ell).rTensor C
          ((TensorProduct.assoc k W C C).symm
            (w ⊗ₜ[k] Coalgebra.comul (R := k) (A := C) c))
      rw [map_smul]
      generalize hq : Coalgebra.comul (R := k) (A := C) c = q
      clear hq c
      induction q using TensorProduct.induction_on with
      | zero => rfl
      | add q q' hq1 hq2 =>
          simpa only [map_add, smul_add, tmul_add] using
            congrArg₂ (· + ·) hq1 hq2
      | tmul c₁ c₂ => simp [smul_tmul']

/-- The copy of a subspace U of C inside the tensor product. -/
noncomputable def tensorSubspace (W : Type w)
    [AddCommGroup W] [Module k W] (U : Submodule k C) :
    Submodule k (W ⊗[k] C) :=
  LinearMap.range (U.subtype.lTensor W)

omit [Coalgebra k C] in
theorem tensorSubspace_mono {U U' : Submodule k C} (hUU' : U ≤ U') :
    tensorSubspace (k := k) W U ≤ tensorSubspace (k := k) W U' := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(Submodule.inclusion hUU').lTensor W z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

omit [Coalgebra k C] in
@[simp]
theorem tensorSubspace_bot :
    tensorSubspace (k := k) W (⊥ : Submodule k C) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, rfl⟩
  change (⊥ : Submodule k C).subtype.lTensor W z = 0
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add, zero_add] using congrArg₂ (· + ·) hz hz'
  | tmul w c =>
      rcases c with ⟨c, hc⟩
      simp only [Submodule.mem_bot] at hc
      subst c
      simp

omit [Coalgebra k C] in
@[simp]
theorem tensorSubspace_top :
    tensorSubspace (k := k) W (⊤ : Submodule k C) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  exact LinearMap.lTensor_surjective W
    (fun c => ⟨⟨c, trivial⟩, rfl⟩) z

omit [Coalgebra k C] in
theorem sfinrank_tensorSubspace
    [FiniteDimensional k W] (U : Submodule k C)
    [FiniteDimensional k U] :
    sfinrank k (tensorSubspace (k := k) W U) =
      finrank k W * sfinrank k U := by
  let : Module.Free k W := Module.Free.of_divisionRing k W
  have hinj : Function.Injective (U.subtype.lTensor W) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      U.subtype U.subtype_injective
  change finrank k (LinearMap.range (U.subtype.lTensor W)) =
    finrank k W * finrank k U
  rw [LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct]

/-- A nonzero finite-dimensional vector space admits a normalized linear
functional and vector. -/
theorem exists_leftFunctional_apply_eq_one
    [FiniteDimensional k W] (hW : 0 < finrank k W) :
    ∃ (ell : W →ₗ[k] k) (a : W), ell a = 1 := by
  let e := Module.finBasis k W
  let i : Fin (finrank k W) := ⟨0, hW⟩
  refine ⟨e.coord i, e i, ?_⟩
  simp [e, i]

/-- The kernel of a normalized functional has codimension one. -/
theorem finrank_ker_add_one_of_apply_eq_one
    [FiniteDimensional k W] (ell : W →ₗ[k] k) (a : W)
    (ha : ell a = 1) :
    finrank k W = finrank k (LinearMap.ker ell) + 1 := by
  have hell : ell ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h a
    simp [ha] at this
  exact (Module.Dual.finrank_ker_add_one_of_ne_zero hell).symm

/-- Projection onto the kernel of a normalized functional along its
normalized vector. -/
noncomputable def tensorKernelProjection
    (ell : W →ₗ[k] k) (a : W) (ha : ell a = 1) :
    W →ₗ[k] LinearMap.ker ell where
  toFun w := ⟨w - ell w • a, by simp [ha]⟩
  map_add' w w' := by
    apply Subtype.ext
    simp only [map_add, add_smul, Submodule.coe_add]
    abel
  map_smul' r w := by
    apply Subtype.ext
    simp [smul_sub, smul_smul]

/-- Every tensor splits into its kernel-coordinate part and its normalized
rank-one coordinate. -/
theorem tensorKernelProjection_decomposition
    (ell : W →ₗ[k] k) (a : W) (ha : ell a = 1)
    (z : W ⊗[k] X) :
    ((LinearMap.ker ell).subtype.rTensor X)
        ((tensorKernelProjection ell a ha).rTensor X z) +
      a ⊗ₜ[k] TensorProduct.leftContract ell z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simp only [map_add, tmul_add]
      calc
        _ = (((LinearMap.ker ell).subtype.rTensor X)
                ((tensorKernelProjection ell a ha).rTensor X z) +
              a ⊗ₜ[k] TensorProduct.leftContract ell z) +
            (((LinearMap.ker ell).subtype.rTensor X)
                ((tensorKernelProjection ell a ha).rTensor X z') +
              a ⊗ₜ[k] TensorProduct.leftContract ell z') := by abel
        _ = z + z' := congrArg₂ (· + ·) hz hz'
  | tmul w x =>
      simp [tensorKernelProjection, TensorProduct.leftContract_tmul,
        sub_tmul, smul_tmul']

/-- The kernel of a normalized contraction is the tensor copy of the
kernel of the functional. -/
theorem ker_leftContract_eq_range_rTensor
    (ell : W →ₗ[k] k) (a : W) (ha : ell a = 1) :
    LinearMap.ker
        (TensorProduct.leftContract ell : W ⊗[k] X →ₗ[k] X) =
      LinearMap.range ((LinearMap.ker ell).subtype.rTensor X) := by
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    refine ⟨(tensorKernelProjection ell a ha).rTensor X z, ?_⟩
    have hdecomp := tensorKernelProjection_decomposition ell a ha z
    rw [hz, tmul_zero, add_zero] at hdecomp
    exact hdecomp
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp [hz, hz']
    | tmul w x => simp

/-- A normalized contraction is surjective. -/
theorem leftContract_surjective
    (ell : W →ₗ[k] k) (a : W) (ha : ell a = 1) :
    Function.Surjective
      (TensorProduct.leftContract ell : W ⊗[k] X →ₗ[k] X) := by
  intro x
  exact ⟨a ⊗ₜ[k] x, by simp [ha]⟩

/-- Rank-nullity for a subspace, with its kernel identified as the image of
an injective parametrization. -/
theorem sfinrank_eq_comap_add_map_of_ker_eq_range
    {Y : Type y} [AddCommGroup Y] [Module k Y]
    [FiniteDimensional k W]
    (i : X →ₗ[k] W) (hi : Function.Injective i)
    (phi : W →ₗ[k] Y)
    (hker : LinearMap.ker phi = LinearMap.range i)
    (P : Submodule k W) :
    sfinrank k P =
      sfinrank k (P.comap i) + sfinrank k (P.map phi) := by
  let fP : P →ₗ[k] P.map phi :=
    (phi.domRestrict P).codRestrict (P.map phi) fun p => ⟨p, p.2, rfl⟩
  have hfPsurj : Function.Surjective fP := by
    rintro ⟨y, x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let kerEquiv : LinearMap.ker fP ≃ₗ[k] P.comap i := {
    toFun := fun x => by
      have hxker : (x : W) ∈ LinearMap.ker phi := by
        rw [LinearMap.mem_ker]
        exact congrArg Subtype.val x.2
      rw [hker] at hxker
      let y : X := Classical.choose hxker
      exact ⟨y, by
        change i y ∈ P
        rw [Classical.choose_spec hxker]
        exact x.1.2⟩
    invFun := fun x => ⟨⟨i x, x.2⟩, by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change phi (i x) = 0
      rw [← LinearMap.mem_ker, hker]
      exact ⟨x, rfl⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec
        (show (x : W) ∈ LinearMap.range i by
          rw [← hker]
          rw [LinearMap.mem_ker]
          exact congrArg Subtype.val x.2))
    right_inv := by
      intro x
      apply Subtype.ext
      exact hi (Classical.choose_spec
        (show i x ∈ LinearMap.range i from ⟨x, rfl⟩))
    map_add' := by
      intro x x'
      apply Subtype.ext
      apply hi
      simp only [Submodule.coe_add, map_add]
      exact (Classical.choose_spec
        (show ((x + x' : LinearMap.ker fP) : W) ∈ LinearMap.range i by
          rw [← hker, LinearMap.mem_ker]
          exact congrArg Subtype.val (x + x').2)).trans
        (congrArg₂ (· + ·)
          (Classical.choose_spec
            (show (x : W) ∈ LinearMap.range i by
              rw [← hker, LinearMap.mem_ker]
              exact congrArg Subtype.val x.2)).symm
          (Classical.choose_spec
            (show (x' : W) ∈ LinearMap.range i by
              rw [← hker, LinearMap.mem_ker]
              exact congrArg Subtype.val x'.2)).symm)
    map_smul' := by
      intro r x
      apply Subtype.ext
      apply hi
      simp only [Submodule.coe_smul, map_smul]
      exact (Classical.choose_spec
        (show ((r • x : LinearMap.ker fP) : W) ∈ LinearMap.range i by
          rw [← hker, LinearMap.mem_ker]
          exact congrArg Subtype.val (r • x).2)).trans
        (congrArg (r • ·)
          (Classical.choose_spec
            (show (x : W) ∈ LinearMap.range i by
              rw [← hker, LinearMap.mem_ker]
              exact congrArg Subtype.val x.2)).symm)
  }
  have hrank := LinearMap.finrank_range_add_finrank_ker fP
  rw [LinearMap.range_eq_top.2 hfPsurj, finrank_top,
    kerEquiv.finrank_eq] at hrank
  change finrank k P = finrank k (P.comap i) + finrank k (P.map phi)
  omega

end

end HopfAmenability
