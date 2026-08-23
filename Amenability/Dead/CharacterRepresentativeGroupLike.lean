/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.SplitDualRepresentatives
import Amenability.Dead.DualTensorAlgebra
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Characters of a finite convolution dual are represented by group-like elements
-/

open Coalgebra Module TensorProduct WithConv

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {F : Type v}
variable [Field k]
variable [AddCommGroup F] [Module k F] [Coalgebra k F]
variable [Coalgebra.IsCocomm k F]
variable [FiniteDimensional k F]

namespace SplitDualFiltration

variable (S :
  SplitDualFiltration k
    (WithConv (Module.Dual k F)))

omit [Coalgebra.IsCocomm k F] in
/--
Evaluation of a pure tensor of functionals on `Δg` is convolution
evaluation at `g`.
-/
theorem dualDistrib_tmul_comul
    (φ ψ : WithConv (Module.Dual k F))
    (g : F) :
    convDualDistribLinearEquiv
        (k := k) (C := F) (D := F)
        (φ ⊗ₜ[k] ψ)
      (Coalgebra.comul (R := k) (A := F) g) =
      (φ * ψ) g := by
  rw [LinearMap.convMul_apply]
  rfl

/--
The element representing an algebra character of `F*` is group-like.
-/
theorem characterRepresentative_isGroupLike
    (i : Fin S.n) :
    IsGroupLikeElem k (S.characterRepresentative i) := by
  let g := S.characterRepresentative i
  constructor
  · calc
      Coalgebra.counit (R := k) (A := F) g
          = (1 : WithConv (Module.Dual k F)) g := by
              rfl
      _ = S.character i 1 := by
              symm
              exact S.character_eq_eval i 1
      _ = 1 := by
              exact map_one (S.character i)
  · apply Module.eval_apply_injective k
    apply LinearMap.ext
    intro η
    let ηc : WithConv (Module.Dual k (F ⊗[k] F)) :=
      WithConv.toConv η
    obtain ⟨z, hz⟩ :=
      (convDualDistribLinearEquiv
        (k := k) (C := F) (D := F)).surjective ηc
    change ηc (Coalgebra.comul (R := k) (A := F) g) =
      ηc (g ⊗ₜ[k] g)
    rw [← hz]
    clear hz η ηc
    induction z using TensorProduct.induction_on with
    | zero =>
        simp
    | add x y hx hy =>
        rw [map_add]
        change
          convDualDistribLinearEquiv
                (k := k) (C := F) (D := F) x
              (Coalgebra.comul (R := k) (A := F) g) +
            convDualDistribLinearEquiv
                (k := k) (C := F) (D := F) y
              (Coalgebra.comul (R := k) (A := F) g) =
          convDualDistribLinearEquiv
                (k := k) (C := F) (D := F) x (g ⊗ₜ[k] g) +
            convDualDistribLinearEquiv
                (k := k) (C := F) (D := F) y (g ⊗ₜ[k] g)
        exact congrArg₂ (fun a b : k => a + b) hx hy
    | tmul φ ψ =>
        rw [dualDistrib_tmul_comul φ ψ g]
        rw [convDualDistribLinearEquiv_tmul_apply]
        rw [← S.character_eq_eval i (φ * ψ)]
        rw [map_mul]
        rw [S.character_eq_eval i φ, S.character_eq_eval i ψ]

end SplitDualFiltration

end

end HopfAmenability
