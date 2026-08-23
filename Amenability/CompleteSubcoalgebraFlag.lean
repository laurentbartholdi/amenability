/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FiniteSubcoalgebra
import Amenability.SubcoalgebraCoalgHom

/-!
# Complete flags of finite subcoalgebras
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {C : Type v} {H : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]

/-- A coalgebra homomorphism maps a subcoalgebra to a subcoalgebra. -/
theorem IsSubcoalgebra.map_coalgHom
    (f : C →ₗc[k] H)
    (P : Submodule k C)
    (hP : IsSubcoalgebra (k := k) P) :
    IsSubcoalgebra (k := k) (P.map f.toLinearMap) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases hP hy with ⟨q, hq⟩
  let g : P →ₗ[k] P.map f.toLinearMap :=
    LinearMap.codRestrict _ (f.toLinearMap.comp P.subtype)
      (fun x ↦ ⟨x, x.2, rfl⟩)
  refine ⟨TensorProduct.map g g q, ?_⟩
  have hmap :
      TensorProduct.mapIncl (P.map f.toLinearMap) (P.map f.toLinearMap)
          (TensorProduct.map g g q) =
        TensorProduct.map f.toLinearMap f.toLinearMap
          (TensorProduct.mapIncl P P q) := by
    clear hq hy y hP
    induction q using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add q q' hq hq' => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hq hq'
    | tmul x x' => rfl
  calc
    TensorProduct.mapIncl (P.map f.toLinearMap) (P.map f.toLinearMap)
        (TensorProduct.map g g q) =
      TensorProduct.map f.toLinearMap f.toLinearMap
        (TensorProduct.mapIncl P P q) := hmap
    _ = TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) (A := C) y) := by rw [hq]
    _ = Coalgebra.comul (R := k) (A := H) (f y) :=
      CoalgHomClass.map_comp_comul_apply f y

namespace FiniteSubcoalgebra

/-- The image of a finite subcoalgebra under an injective coalgebra map. -/
noncomputable def map
    (A : FiniteSubcoalgebra k C)
    (f : C →ₗc[k] H)
    (_hf : Function.Injective f) :
    FiniteSubcoalgebra k H where
  carrier := A.carrier.map f.toLinearMap
  isSubcoalgebra := A.isSubcoalgebra.map_coalgHom f
  finiteDimensional := by
    let inclusion : A.carrier →ₗ[k] A.carrier.map f.toLinearMap :=
      LinearMap.codRestrict _ (f.toLinearMap.comp A.carrier.subtype)
        (fun x ↦ ⟨x, x.2, rfl⟩)
    exact FiniteDimensional.of_surjective inclusion (by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)

@[simp]
theorem map_carrier
    (A : FiniteSubcoalgebra k C)
    (f : C →ₗc[k] H)
    (hf : Function.Injective f) :
    (A.map f hf).carrier = A.carrier.map f.toLinearMap := rfl

end FiniteSubcoalgebra

namespace PrimalTransfer

/-- A complete flag of finite subcoalgebras, expressed recursively. -/
inductive HasCompleteSubcoalgebraFlag : FiniteSubcoalgebra k H → Prop
  | bot {A : FiniteSubcoalgebra k H} (hA : A.carrier = ⊥) :
      HasCompleteSubcoalgebraFlag A
  | step {A' A : FiniteSubcoalgebra k H}
      (hflag : HasCompleteSubcoalgebraFlag A')
      (hAA : A'.carrier ≤ A.carrier)
      (hdim : finrank k A.carrier = finrank k A'.carrier + 1) :
      HasCompleteSubcoalgebraFlag A

/-- An injective coalgebra map carries a complete subcoalgebra flag to its image. -/
theorem HasCompleteSubcoalgebraFlag.map
    {A : FiniteSubcoalgebra k C}
    (hA : HasCompleteSubcoalgebraFlag A)
    (f : C →ₗc[k] H)
    (hf : Function.Injective f) :
    HasCompleteSubcoalgebraFlag (A.map f hf) := by
  induction hA with
  | @bot A hbot =>
      apply HasCompleteSubcoalgebraFlag.bot
      rw [FiniteSubcoalgebra.map_carrier, hbot, Submodule.map_bot]
  | @step A' A hflag hAA hdim ih =>
      apply HasCompleteSubcoalgebraFlag.step ih
        (Submodule.map_mono hAA)
      have hfinrank (B : Submodule k C) :
          sfinrank k (B.map f.toLinearMap) = sfinrank k B := by
        let g : B →ₗ[k] B.map f.toLinearMap :=
          LinearMap.codRestrict _ (f.toLinearMap.comp B.subtype)
            (fun x ↦ ⟨x, x.2, rfl⟩)
        have hg : Function.Injective g := by
          intro x y hxy
          apply Subtype.ext
          apply hf
          exact congrArg Subtype.val hxy
        have hsurj : Function.Surjective g := by
          rintro ⟨y, x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        exact (LinearEquiv.ofBijective g ⟨hg, hsurj⟩).finrank_eq.symm
      change sfinrank k (A.carrier.map f.toLinearMap) =
        sfinrank k (A'.carrier.map f.toLinearMap) + 1
      rw [hfinrank A.carrier, hfinrank A'.carrier]
      exact hdim

end PrimalTransfer

end

end HopfAmenability
