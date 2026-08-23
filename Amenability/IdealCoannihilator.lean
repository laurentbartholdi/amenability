/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.ConvolutionAnnihilator
import Amenability.TensorSquareIntersection
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Flat.Basic

/-!
# Ideals of a finite convolution dual and subcoalgebras

For a finite-dimensional cocommutative coalgebra `C`, the coannihilator
of an ideal subspace of `C*` is a subcoalgebra of `C`.

This is the converse half of the familiar finite-dimensional
anti-correspondence between subcoalgebras of `C` and ideals of `C*`.
-/

open Coalgebra Module TensorProduct WithConv

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {C : Type v}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Coalgebra.IsCocomm k C]
variable [FiniteDimensional k C]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/--
Membership in the convolution-dual coannihilator can be tested directly
against the original convolution-dual subspace.
-/
theorem mem_convDualCoannihilator
    (M : Submodule k (WithConv (Module.Dual k C)))
    (c : C) :
    c ∈ convDualCoannihilator M ↔
      ∀ φ : WithConv (Module.Dual k C), φ ∈ M → φ c = 0 := by
  rw [convDualCoannihilator, Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    exact h
      ((WithConv.linearEquiv k (Module.Dual k C)) φ)
      ⟨φ, hφ, rfl⟩
  · intro h ψ hψ
    rcases hψ with ⟨φ, hφ, rfl⟩
    exact h φ hφ

/--
Evaluation of elements of `C` on a subspace `M ≤ C*`.
Its kernel is the coannihilator of `M`.
-/
def convSubspaceEval
    (M : Submodule k (WithConv (Module.Dual k C))) :
    C →ₗ[k] Module.Dual k M where
  toFun c :=
    { toFun := fun φ => (φ.1 : WithConv (Module.Dual k C)) c
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro r φ
        rfl }
  map_add' := by
    intro c d
    ext φ
    exact map_add φ.1.ofConv c d
  map_smul' := by
    intro r c
    ext φ
    exact map_smul φ.1.ofConv r c

@[simp]
theorem convSubspaceEval_apply
    (M : Submodule k (WithConv (Module.Dual k C)))
    (c : C) (φ : M) :
    convSubspaceEval M c φ = φ.1 c :=
  rfl

theorem ker_convSubspaceEval
    (M : Submodule k (WithConv (Module.Dual k C))) :
    LinearMap.ker (convSubspaceEval M) =
      convDualCoannihilator M := by
  ext c
  constructor
  · intro hc
    rw [LinearMap.mem_ker] at hc
    rw [mem_convDualCoannihilator]
    intro φ hφ
    have h :=
      DFunLike.congr_fun hc ⟨φ, hφ⟩
    simpa using h
  · intro hc
    rw [mem_convDualCoannihilator] at hc
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro φ
    exact hc φ.1 φ.2

/--
Tensoring the evaluation kernel on the right identifies
`B ⊗ C` with the corresponding kernel in the tensor product.
-/
theorem range_coannihilator_rTensor_eq_ker
    (M : Submodule k (WithConv (Module.Dual k C))) :
    LinearMap.range
        ((convDualCoannihilator M).subtype.rTensor C) =
      LinearMap.ker ((convSubspaceEval M).rTensor C) := by
  have h :=
    Module.Flat.rTensor_exact C
      (LinearMap.exact_subtype_ker_map (convSubspaceEval M))
  have heq :=
    (LinearMap.exact_iff.mp h).symm
  rw [ker_convSubspaceEval M] at heq
  exact heq

/--
Pairing the tensor obtained by applying `convSubspaceEval` in the first
leg with `φ ∈ M` and `ψ ∈ C*` gives the convolution product
`(φ * ψ)(c)`.
-/
theorem eval_rTensor_comul_pair
    (M : Submodule k (WithConv (Module.Dual k C)))
    (c : C) (φ : M) (ψ : Module.Dual k C) :
    ψ
        (dualTensorHom k M C
          (((convSubspaceEval M).rTensor C)
            (Coalgebra.comul (R := k) (A := C) c)) φ) =
      (φ.1 * WithConv.toConv ψ) c := by
  rw [LinearMap.convMul_apply]
  change
    ψ
        (dualTensorHom k M C
          (((convSubspaceEval M).rTensor C)
            (Coalgebra.comul (R := k) (A := C) c)) φ) =
      LinearMap.mul' k k
        (TensorProduct.map φ.1.ofConv ψ
          (Coalgebra.comul (R := k) (A := C) c))
  induction (Coalgebra.comul (R := k) (A := C) c) using
      TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y => simp [dualTensorHom_apply]

/--
If `M` is an ideal subspace of the convolution dual and `c` annihilates
`M`, then the comultiplication of `c` lies in `B ⊗ C`, where
`B = M^⊥`.
-/
theorem comul_mem_coannihilator_rTensor
    (M : Submodule k (WithConv (Module.Dual k C)))
    (hM : IsIdealSubspace M)
    {c : C}
    (hc : c ∈ convDualCoannihilator M) :
    Coalgebra.comul (R := k) (A := C) c ∈
      LinearMap.range
        ((convDualCoannihilator M).subtype.rTensor C) := by
  rw [range_coannihilator_rTensor_eq_ker M]
  rw [LinearMap.mem_ker]
  letI : FiniteDimensional k (WithConv (Module.Dual k C)) :=
    FiniteDimensional.of_injective
      (WithConv.linearEquiv k (Module.Dual k C)).toLinearMap
      (WithConv.linearEquiv k (Module.Dual k C)).injective
  letI : FiniteDimensional k M :=
    FiniteDimensional.of_injective M.subtype Subtype.val_injective
  letI : Module.Free k M := Module.Free.of_divisionRing k M
  apply
    (dualTensorHom_bijective
      (R := k) (M := M) (N := C)).1
  rw [map_zero]
  apply LinearMap.ext
  intro φ
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro ψ
  rw [Module.Dual.eval_apply]
  rw [eval_rTensor_comul_pair M c φ ψ]
  have hprod :
      φ.1 * WithConv.toConv ψ ∈ M := by
    simpa [mul_comm] using
      hM (WithConv.toConv ψ) φ.2
  simpa using (mem_convDualCoannihilator M c).1 hc _ hprod

/--
The other one-sided tensor condition follows from cocommutativity.
-/
theorem comul_mem_coannihilator_lTensor
    (M : Submodule k (WithConv (Module.Dual k C)))
    (hM : IsIdealSubspace M)
    {c : C}
    (hc : c ∈ convDualCoannihilator M) :
    Coalgebra.comul (R := k) (A := C) c ∈
      LinearMap.range
        ((convDualCoannihilator M).subtype.lTensor C) := by
  have hr :=
    comul_mem_coannihilator_rTensor M hM hc
  rcases hr with ⟨z, hz⟩
  have hcomm :
      ((convDualCoannihilator M).subtype.lTensor C)
          (TensorProduct.comm k (convDualCoannihilator M) C z) =
        TensorProduct.comm k C C
          (((convDualCoannihilator M).subtype.rTensor C) z) := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero =>
        simp
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy
    | tmul x y =>
        rfl
  refine ⟨TensorProduct.comm k (convDualCoannihilator M) C z, ?_⟩
  calc
    ((convDualCoannihilator M).subtype.lTensor C)
        (TensorProduct.comm k (convDualCoannihilator M) C z)
        =
      TensorProduct.comm k C C
        (((convDualCoannihilator M).subtype.rTensor C) z) := hcomm
    _ = TensorProduct.comm k C C
        (Coalgebra.comul (R := k) (A := C) c) := by
          rw [hz]
    _ = Coalgebra.comul (R := k) (A := C) c := by
          exact Coalgebra.comm_comul k c

/--
The coannihilator of an ideal in the finite convolution dual is a
subcoalgebra.
-/
theorem convDualCoannihilator_isSubcoalgebra
    (M : Submodule k (WithConv (Module.Dual k C)))
    (hM : IsIdealSubspace M) :
    IsSubcoalgebra (k := k) (convDualCoannihilator M) := by
  intro c hc
  rw [range_mapIncl_self_eq_inf
    (convDualCoannihilator M)]
  exact
    ⟨comul_mem_coannihilator_rTensor M hM hc,
      comul_mem_coannihilator_lTensor M hM hc⟩


end

end UnifiedRounding
