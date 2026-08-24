/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoalgebraBaseChange
import Amenability.HopfActionSubspace
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of Hopf-module coalgebras
-/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {K : Type v} {H : Type w} {M : Type x}
variable [Field k] [Field K] [Algebra k K]
variable [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M]
variable [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

abbrev BaseChangeHopf := K ⊗[k] H
abbrev BaseChangeModule := K ⊗[k] M

local instance baseChange_scalarTower : IsScalarTower k K (K ⊗[k] M) :=
  isScalarTower_left

local instance baseChange_smulComm_scalars : SMulCommClass K k (K ⊗[k] M) :=
  ⟨fun a r z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp [hz, hz']
    | tmul b m => simp [smul_tmul', smul_eq_mul]⟩

/-- The original `H`-representation after extension of scalars. -/
noncomputable def baseChangeHRepresentation :
    H →+* Module.End K (K ⊗[k] M) :=
  ((Module.End.baseChangeHom k K M).comp
    (Algebra.lsmul k k M : H →ₐ[k] Module.End k M)).toRingHom

/-- The canonical representation of `K ⊗ H` on `K ⊗ M`. -/
noncomputable def baseChangeActionRepresentation :
    K ⊗[k] H →ₐ[K] Module.End K (K ⊗[k] M) :=
  Algebra.TensorProduct.lift
    (Algebra.lsmul K K (K ⊗[k] M))
    ((Module.End.baseChangeHom k K M).comp
      (Algebra.lsmul k k M : H →ₐ[k] Module.End k M))
    (fun a h => by
      apply LinearMap.ext
      intro z
      exact LinearMap.map_smul_of_tower
        (((Module.End.baseChangeHom k K M).comp
          (Algebra.lsmul k k M : H →ₐ[k] Module.End k M)) h) a z |>.symm)

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
theorem baseChangeActionRepresentation_tmul (a : K) (h : H) :
    baseChangeActionRepresentation (k := k) (K := K) (H := H) (M := M)
        (a ⊗ₜ[k] h) =
      (Algebra.lsmul K K (K ⊗[k] M)) a *
        ((Module.End.baseChangeHom k K M).comp
          (Algebra.lsmul k k M : H →ₐ[k] Module.End k M)) h :=
  Algebra.TensorProduct.lift_tmul _ _ _ a h

/-- The canonical action of `K ⊗ H` on `K ⊗ M`. -/
@[instance_reducible]
noncomputable def baseChangeModule_inst :
    Module (K ⊗[k] H) (K ⊗[k] M) :=
  Module.compHom (K ⊗[k] M)
    (baseChangeActionRepresentation (k := k) (K := K) (H := H) (M := M)).toRingHom

scoped[HopfModuleBaseChange] attribute [instance] HopfAmenability.baseChangeModule_inst

section ScopedInstances

attribute [local instance] baseChangeModule_inst

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
theorem baseChange_smul_tmul (a : K) (h : H) (b : K) (m : M) :
    (a ⊗ₜ[k] h : K ⊗[k] H) • (b ⊗ₜ[k] m : K ⊗[k] M) =
      (a * b) ⊗ₜ[k] (h • m) := by
  change baseChangeActionRepresentation (k := k) (K := K) (H := H) (M := M)
      (a ⊗ₜ[k] h) (b ⊗ₜ[k] m) = _
  rw [baseChangeActionRepresentation_tmul]
  change a • ((Algebra.lsmul k k M h).baseChange K (b ⊗ₜ[k] m)) = _
  rw [LinearMap.baseChange_tmul]
  simp [smul_tmul', smul_eq_mul]

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
theorem baseChange_actionTower :
    IsScalarTower K (K ⊗[k] H) (K ⊗[k] M) :=
  IsScalarTower.of_algebraMap_smul (fun a z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        change ((a ⊗ₜ[k] (1 : H)) : K ⊗[k] H) • (z + z') = a • (z + z')
        change ((a ⊗ₜ[k] (1 : H)) : K ⊗[k] H) • z = a • z at hz
        change ((a ⊗ₜ[k] (1 : H)) : K ⊗[k] H) • z' = a • z' at hz'
        rw [smul_add, smul_add, hz, hz']
    | tmul b m =>
        change ((a ⊗ₜ[k] (1 : H)) : K ⊗[k] H) • (b ⊗ₜ[k] m) = _
        simp [smul_tmul', smul_eq_mul])

scoped[HopfModuleBaseChange] attribute [instance] HopfAmenability.baseChange_actionTower

attribute [local instance] baseChange_actionTower

/-- Base change preserves the Hopf-module-coalgebra structure. -/
theorem baseChangeIsHopfModuleCoalgebra :
    IsHopfModuleCoalgebra K (K ⊗[k] H) (K ⊗[k] M) where
  counit_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hz'
    | tmul x y =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x x' hx hx' =>
            simpa only [add_tmul, map_add] using congrArg₂ (fun p q => p + q) hx hx'
        | tmul a h =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y y' hy hy' =>
              simpa only [tmul_add, map_add] using congrArg₂ (fun p q => p + q) hy hy'
          | tmul b m =>
              simp only [LinearMap.coe_comp, Function.comp_apply,
                hopfModuleAction_tmul, baseChange_smul_tmul, counit_tmul,
                counit_smul, CommSemiring.counit_apply, smul_eq_mul,
                Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
              rw [mul_smul]
              rw [mul_comm a b]
  comul_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hz'
    | tmul x y =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x x' hx hx' =>
            simpa only [add_smul, map_add, add_tmul] using
              congrArg₂ (fun p q => p + q) hx hx'
        | tmul a h =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y y' hy hy' =>
              simpa only [smul_add, map_add, tmul_add] using
                congrArg₂ (fun p q => p + q) hy hy'
          | tmul b m =>
              simp only [LinearMap.comp_apply, hopfModuleAction_tmul,
                baseChange_smul_tmul]
              rw [TensorProduct.comul_tmul, TensorProduct.comul_tmul,
                comul_smul]
              simp only [TensorProduct.comul_tmul]
              generalize hh : Coalgebra.comul (R := k) (A := H) h = qh
              generalize hm : Coalgebra.comul (R := k) (A := M) m = qm
              clear hh hm h m
              induction qh using TensorProduct.induction_on with
              | zero => simp
              | add qh qh' hqh hqh' =>
                  simpa only [add_tmul, tmul_add, map_add] using
                    congrArg₂ (fun p q => p + q) hqh hqh'
              | tmul h₁ h₂ =>
                induction qm using TensorProduct.induction_on with
                | zero => simp
                | add qm qm' hqm hqm' =>
                    simpa only [tmul_add, map_add] using
                      congrArg₂ (fun p q => p + q) hqm hqm'
                | tmul m₁ m₂ =>
                    simp [baseChange_smul_tmul, CommSemiring.comul_apply]

scoped[HopfModuleBaseChange] attribute [instance]
  HopfAmenability.baseChangeIsHopfModuleCoalgebra

attribute [local instance] baseChangeIsHopfModuleCoalgebra

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
/-- Acting on scalar-extended subspaces commutes with scalar extension. -/
theorem actionSubspace_baseChange
    (P : Submodule k H) (Q : Submodule k M) :
    actionSubspace
        (baseChangeSubspace (k := k) K P)
        (baseChangeSubspace (k := k) K Q) =
      baseChangeSubspace (k := k) K (actionSubspace P Q) := by
  rw [actionSubspace_eq_map₂]
  apply le_antisymm
  · rw [Submodule.map₂_le]
    intro x hx y hy
    rcases hx with ⟨xp, rfl⟩
    rcases hy with ⟨yq, rfl⟩
    induction xp using TensorProduct.induction_on with
    | zero => simp
    | add xp xp' hxp hxp' =>
        convert (baseChangeSubspace K (actionSubspace P Q)).add_mem hxp hxp' using 1
        all_goals simp only [map_add, LinearMap.add_apply]
    | tmul a p =>
      induction yq using TensorProduct.induction_on with
      | zero => simp
      | add yq yq' hyq hyq' =>
          convert (baseChangeSubspace K (actionSubspace P Q)).add_mem hyq hyq' using 1
          all_goals simp only [map_add]
      | tmul b q =>
          refine ⟨(a * b) ⊗ₜ[k]
            (⟨(p : H) • (q : M), product_mem_actionSubspace p.2 q.2⟩ :
              actionSubspace P Q), ?_⟩
          simp [baseChange_smul_tmul]
  · rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' =>
        rw [map_add]
        exact (Submodule.map₂ (Algebra.lsmul K K (K ⊗[k] M)).toLinearMap
          (baseChangeSubspace K P) (baseChangeSubspace K Q)).add_mem hw hw'
    | tmul a q =>
      rcases q.2 with ⟨v, hv⟩
      rw [LinearMap.baseChange_tmul]
      change a ⊗ₜ[k] (q : M) ∈ _
      rw [← hv]
      clear q hv
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
          rw [map_add, tmul_add]
          exact (Submodule.map₂ (Algebra.lsmul K K (K ⊗[k] M)).toLinearMap
            (baseChangeSubspace K P) (baseChangeSubspace K Q)).add_mem hv hv'
      | tmul p q =>
          rw [restrictedHopfModuleAction_tmul]
          have hpK : ((1 : K) ⊗ₜ[k] (p : H)) ∈
              baseChangeSubspace (k := k) K P := ⟨(1 : K) ⊗ₜ[k] p, rfl⟩
          have hqK : (a ⊗ₜ[k] (q : M)) ∈
              baseChangeSubspace (k := k) K Q := ⟨a ⊗ₜ[k] q, rfl⟩
          have hmem := Submodule.apply_mem_map₂
            (Algebra.lsmul K K (K ⊗[k] M)).toLinearMap hpK hqK
          change ((1 : K) ⊗ₜ[k] (p : H) : K ⊗[k] H) •
              (a ⊗ₜ[k] (q : M)) ∈ _ at hmem
          simpa [baseChange_smul_tmul] using hmem

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
theorem sfinrank_actionSubspace_baseChange
    (P : Submodule k H) (Q : Submodule k M)
    [FiniteDimensional k P] [FiniteDimensional k Q] :
    sfinrank K
        (actionSubspace
          (baseChangeSubspace (k := k) K P)
          (baseChangeSubspace (k := k) K Q)) =
      sfinrank k (actionSubspace P Q) := by
  rw [actionSubspace_baseChange]
  exact sfinrank_baseChangeSubspace (actionSubspace P Q)

end ScopedInstances

end

end HopfAmenability
