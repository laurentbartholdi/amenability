/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Coalgebras carrying a compatible Hopf-module structure
-/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M]
variable [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M]

/-- The linearized action of a Hopf algebra on one of its modules. -/
def hopfModuleAction : H ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (Algebra.lsmul k k M).toLinearMap

omit [Coalgebra k M] in
@[simp]
theorem hopfModuleAction_tmul (h : H) (m : M) :
    hopfModuleAction (k := k) (H := H) (M := M) (h ⊗ₜ[k] m) = h • m :=
  rfl

omit [Coalgebra k M] in
/-- A group-like element acts injectively on every module. -/
theorem groupLike_action_injective {g : H} (hg : IsGroupLikeElem k g) :
    Function.Injective
      ((Algebra.lsmul k k M g : Module.End k M) : M →ₗ[k] M) := by
  intro x y hxy
  have hxy' : g • x = g • y := hxy
  calc
    x = (1 : H) • x := by simp
    _ = (HopfAlgebra.antipode k g * g) • x := by rw [hg.antipode_mul_cancel]
    _ = HopfAlgebra.antipode k g • (g • x) := by rw [mul_smul]
    _ = HopfAlgebra.antipode k g • (g • y) := by rw [hxy']
    _ = (HopfAlgebra.antipode k g * g) • y := by rw [mul_smul]
    _ = (1 : H) • y := by rw [hg.antipode_mul_cancel]
    _ = y := by simp

/-- Compatibility of an `H`-module structure with the coalgebra structure.
Cocommutativity is deliberately not part of this definition. -/
class IsHopfModuleCoalgebra
    (k : Type u) (H : Type v) (M : Type w)
    [Field k] [Ring H] [HopfAlgebra k H]
    [AddCommGroup M] [Module k M]
    [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] : Prop where
  counit_action :
    Coalgebra.counit (R := k) (A := M) ∘ₗ hopfModuleAction =
      Coalgebra.counit (R := k) (A := H ⊗[k] M)
  comul_action :
    Coalgebra.comul (R := k) (A := M) ∘ₗ hopfModuleAction =
      TensorProduct.map hopfModuleAction hopfModuleAction ∘ₗ
        Coalgebra.comul (R := k) (A := H ⊗[k] M)

section Compatible

variable [IsHopfModuleCoalgebra k H M]

/-- The module action bundled as a coalgebra morphism. -/
def hopfModuleActionCoalgHom : H ⊗[k] M →ₗc[k] M :=
  CoalgHom.mk hopfModuleAction
    (IsHopfModuleCoalgebra.counit_action (k := k) (H := H) (M := M))
    (IsHopfModuleCoalgebra.comul_action (k := k) (H := H) (M := M)).symm

@[simp]
theorem hopfModuleActionCoalgHom_tmul (h : H) (m : M) :
    hopfModuleActionCoalgHom (k := k) (H := H) (M := M) (h ⊗ₜ[k] m) = h • m :=
  rfl

@[simp]
theorem counit_smul (h : H) (m : M) :
    Coalgebra.counit (R := k) (A := M) (h • m) =
      Coalgebra.counit (R := k) (A := H) h *
        Coalgebra.counit (R := k) (A := M) m := by
  have hcompat := congrArg
    (fun f : H ⊗[k] M →ₗ[k] k => f (h ⊗ₜ[k] m))
    (IsHopfModuleCoalgebra.counit_action (k := k) (H := H) (M := M))
  simpa [mul_comm] using hcompat

@[simp]
theorem comul_smul (h : H) (m : M) :
    Coalgebra.comul (R := k) (A := M) (h • m) =
      TensorProduct.map hopfModuleAction hopfModuleAction
        (Coalgebra.comul (R := k) (A := H ⊗[k] M) (h ⊗ₜ[k] m)) := by
  have hcompat := congrArg
    (fun f : H ⊗[k] M →ₗ[k] M ⊗[k] M => f (h ⊗ₜ[k] m))
    (IsHopfModuleCoalgebra.comul_action (k := k) (H := H) (M := M))
  simpa using hcompat

end Compatible

/-- The regular left action of a Hopf algebra is a Hopf-module coalgebra. -/
instance regularIsHopfModuleCoalgebra : IsHopfModuleCoalgebra k H H where
  counit_action := by
    change Coalgebra.counit ∘ₗ LinearMap.mul' k H = Coalgebra.counit
    exact CoalgHomClass.counit_comp (Bialgebra.mulCoalgHom k H)
  comul_action := by
    change Coalgebra.comul ∘ₗ LinearMap.mul' k H =
      TensorProduct.map (LinearMap.mul' k H) (LinearMap.mul' k H) ∘ₗ
        Coalgebra.comul
    exact (CoalgHomClass.map_comp_comul (Bialgebra.mulCoalgHom k H)).symm

end

end HopfAmenability
