/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfModuleCoalgebraRounding
import Amenability.TensorProductMap
import Amenability.UniversalEnvelopingCoalgebra
import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Rounding and amenability for Lie-module coalgebras

This opt-in specialization extends a Lie action to the universal enveloping
Hopf algebra and applies the generic Hopf-module-coalgebra rounding theorem.
-/

open TensorProduct
open Coalgebra
open Module

namespace Coalgebra

universe u v w

/-- A coalgebra carrying a Lie-module structure whose action operators are
coderivations. Counit compatibility follows from this axiom. -/
class IsLieModuleCoalgebra
    (k : Type u) (L : Type v) (M : Type w)
    [Field k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup M] [Module k M]
    [LieRingModule L M] [LieModule k L M]
    [Coalgebra k M] : Prop where
  comul_lie : ∀ x : L,
    Coalgebra.comul (R := k) (A := M) ∘ₗ LieModule.toEnd k L M x =
      ((LieModule.toEnd k L M x).rTensor M +
        (LieModule.toEnd k L M x).lTensor M) ∘ₗ
          Coalgebra.comul (R := k) (A := M)

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
variable [Coalgebra k M] [IsLieModuleCoalgebra k L M]

theorem comul_lie_apply (x : L) (m : M) :
    Coalgebra.comul (R := k) (A := M) ⁅x, m⁆ =
      (LieModule.toEnd k L M x).rTensor M
          (Coalgebra.comul (R := k) (A := M) m) +
        (LieModule.toEnd k L M x).lTensor M
          (Coalgebra.comul (R := k) (A := M) m) := by
  have h := congrArg (fun f : M →ₗ[k] TensorProduct k M M => f m)
    (IsLieModuleCoalgebra.comul_lie (k := k) (L := L) (M := M) x)
  simpa using h

theorem counit_lie_apply (x : L) (m : M) :
    Coalgebra.counit (R := k) (A := M) ⁅x, m⁆ = 0 := by
  let ε := Coalgebra.counit (R := k) (A := M)
  let εε : TensorProduct k M M →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap.comp
      ((ε.lTensor k).comp (ε.rTensor M))
  have hleft (f : M →ₗ[k] k) (y : M) :
      (TensorProduct.lid k k) (_root_.TensorProduct.map ε f
        (Coalgebra.comul (R := k) (A := M) y)) = f y := by
    have hy := congrArg (fun z => (TensorProduct.lid k k) z)
      (LinearMap.congr_fun (CoassocSimps.map_counit_comp_comul_left f) y)
    simpa [εε, ε] using hy
  have hright (f : M →ₗ[k] k) (y : M) :
      (TensorProduct.lid k k) (_root_.TensorProduct.map f ε
        (Coalgebra.comul (R := k) (A := M) y)) = f y := by
    have hy := congrArg (fun z => (TensorProduct.lid k k) z)
      (LinearMap.congr_fun (CoassocSimps.map_counit_comp_comul_right f) y)
    simpa [εε, ε] using hy
  have h := congrArg εε (comul_lie_apply x m)
  have h' :
      (TensorProduct.lid k k)
          (_root_.TensorProduct.map ε ε
            (Coalgebra.comul (R := k) (A := M) ⁅x, m⁆)) =
        (TensorProduct.lid k k)
            (_root_.TensorProduct.map
              (ε.comp (LieModule.toEnd k L M x)) ε
              (Coalgebra.comul (R := k) (A := M) m)) +
          (TensorProduct.lid k k)
            (_root_.TensorProduct.map ε
              (ε.comp (LieModule.toEnd k L M x))
              (Coalgebra.comul (R := k) (A := M) m)) := by
    simpa [εε, ε] using h
  rw [hleft, hright, hleft] at h'
  change (ε.comp (LieModule.toEnd k L M x)) m = 0
  have hz : (0 : k) = (ε.comp (LieModule.toEnd k L M x)) m := by
    calc
      0 = (ε.comp (LieModule.toEnd k L M x)) m -
          (ε.comp (LieModule.toEnd k L M x)) m := by simp
      _ = ((ε.comp (LieModule.toEnd k L M x)) m +
            (ε.comp (LieModule.toEnd k L M x)) m) -
          (ε.comp (LieModule.toEnd k L M x)) m :=
        congrArg (fun z => z - (ε.comp (LieModule.toEnd k L M x)) m) h'
      _ = (ε.comp (LieModule.toEnd k L M x)) m := by abel
  exact hz.symm

end Coalgebra

namespace HopfAmenability
universe u v w
variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
variable {M : Type w} [AddCommGroup M] [Module k M]
  [LieRingModule L M] [LieModule k L M]

def lieActionBilinear : L →ₗ[k] M →ₗ[k] M :=
  (LieModule.toEnd k L M : L →ₗ[k] Module.End k M)

def lieActionMap (F : Submodule k L) (E : Submodule k M) :
    F ⊗[k] E →ₗ[k] M :=
  TensorProduct.lift
    ((lieActionBilinear (k := k) (L := L) (M := M)).domRestrict₁₂ F E)

def lieActionSubspace (F : Submodule k L) (E : Submodule k M) :
    Submodule k M :=
  LinearMap.range (lieActionMap F E)

theorem lieActionSubspace_eq_map₂ (F : Submodule k L) (E : Submodule k M) :
    lieActionSubspace F E =
      Submodule.map₂ (lieActionBilinear (k := k) (L := L) (M := M)) F E := by
  rw [lieActionSubspace, TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul x m => rfl

def lieExpansion (F : Submodule k L) (E : Submodule k M) :
    Submodule k M :=
  E ⊔ lieActionSubspace F E

local notation "U" => UniversalEnvelopingAlgebra k L
attribute [local instance 100] LieRing.ofAssociativeRing
section Action

noncomputable def ueaRepresentation : U →ₐ[k] Module.End k M :=
  UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k L M)

@[instance_reducible] noncomputable def ueaModule : Module U M :=
  Module.compHom M (ueaRepresentation (k := k) (L := L) (M := M)).toRingHom

noncomputable local instance : Module U M := ueaModule

noncomputable local instance : IsScalarTower k U M :=
  IsScalarTower.of_algebraMap_smul (fun r m => by
    change ueaRepresentation (M := M) (algebraMap k U r) m = r • m
    rw [(ueaRepresentation (k := k) (L := L) (M := M)).commutes]
    rfl)

@[simp] theorem iota_smul (x : L) (m : M) :
    UniversalEnvelopingAlgebra.ι k x • m = ⁅x, m⁆ := by
  change ueaRepresentation (M := M) (UniversalEnvelopingAlgebra.ι k x) m = _
  rw [ueaRepresentation, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

variable [Coalgebra k M]

def GoodComul (u : U) : Prop := ∀ m : M,
  Coalgebra.comul (R := k) (A := M) (u • m) =
    TensorProduct.map HopfAmenability.hopfModuleAction
      HopfAmenability.hopfModuleAction
      (Coalgebra.comul (R := k) (A := U ⊗[k] M) (u ⊗ₜ[k] m))

theorem goodComul_mul {u v : U} (hu : GoodComul (M := M) u)
    (hv : GoodComul (M := M) v) : GoodComul (M := M) (u * v) := by
  intro m
  rw [mul_smul, hu]
  rw [TensorProduct.comul_tmul, hv]
  rw [TensorProduct.comul_tmul]
  conv_rhs =>
    rw [TensorProduct.comul_tmul, Bialgebra.comul_mul]
  generalize Coalgebra.comul (R := k) (A := U) u = tu at *
  generalize Coalgebra.comul (R := k) (A := U) v = tv at *
  generalize Coalgebra.comul (R := k) (A := M) m = tm at *
  induction tu using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp [hp, hq, add_tmul, add_mul]
  | tmul u₁ u₂ =>
      induction tv using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq => simp [hp, hq, add_tmul, tmul_add, mul_add]
      | tmul v₁ v₂ =>
          induction tm using TensorProduct.induction_on with
          | zero => simp
          | add p q hp hq => simp [hp, hq, tmul_add]
          | tmul m₁ m₂ => simp [mul_smul]

theorem goodComul_iota (x : L)
    (hx : ∀ m : M, Coalgebra.comul (R := k) (A := M) ⁅x, m⁆ =
      (LieModule.toEnd k L M x).rTensor M (Coalgebra.comul (R := k) m) +
      (LieModule.toEnd k L M x).lTensor M (Coalgebra.comul (R := k) m)) :
    GoodComul (M := M) (UniversalEnvelopingAlgebra.ι k x) := by
  intro m
  rw [iota_smul, hx]
  change _ = TensorProduct.map HopfAmenability.hopfModuleAction
    HopfAmenability.hopfModuleAction
    (Coalgebra.comul (R := k) (A := U ⊗[k] M)
      (UniversalEnvelopingAlgebra.ι k x ⊗ₜ[k] m))
  rw [TensorProduct.comul_tmul]
  change _ = TensorProduct.map HopfAmenability.hopfModuleAction
    HopfAmenability.hopfModuleAction
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm k k k k U U M M
      (delta (UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k]
        Coalgebra.comul (R := k) m))
  rw [delta_iota]
  induction Coalgebra.comul (R := k) (A := M) m using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add]
      rw [show
        (LieModule.toEnd k L M x).rTensor M p +
            (LieModule.toEnd k L M x).rTensor M q +
          ((LieModule.toEnd k L M x).lTensor M p +
            (LieModule.toEnd k L M x).lTensor M q) =
          ((LieModule.toEnd k L M x).rTensor M p +
            (LieModule.toEnd k L M x).lTensor M p) +
          ((LieModule.toEnd k L M x).rTensor M q +
            (LieModule.toEnd k L M x).lTensor M q) by abel]
      rw [hp, hq]
      simp [add_tmul, tmul_add]
  | tmul m₁ m₂ =>
      simp only [TensorProduct.add_tmul, map_add,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.map_tmul, HopfAmenability.hopfModuleAction_tmul,
        one_smul, iota_smul]
      rfl

theorem goodComul_all
    (hx : ∀ (x : L) (m : M), Coalgebra.comul (R := k) (A := M) ⁅x, m⁆ =
      (LieModule.toEnd k L M x).rTensor M (Coalgebra.comul (R := k) m) +
      (LieModule.toEnd k L M x).lTensor M (Coalgebra.comul (R := k) m))
    (u : U) : GoodComul (M := M) u := by
  let good : Subalgebra k U :=
    { carrier := {a | GoodComul (M := M) a}
      mul_mem' := fun ha hb => goodComul_mul ha hb
      add_mem' := fun ha hb m => by
        simp only [add_smul, map_add, ha m, hb m]
        simp [add_tmul]
      algebraMap_mem' := fun r m => by
        rw [IsScalarTower.algebraMap_smul]
        simp only [map_smul, TensorProduct.comul_tmul, Bialgebra.comul_algebraMap]
        induction Coalgebra.comul (R := k) (A := M) m using
            TensorProduct.induction_on with
        | zero => simp
        | add p q hp hq => simp [hp, hq, tmul_add]
        | tmul m₁ m₂ =>
            simpa using TensorProduct.smul_tmul' r m₁ m₂ }
  have hi : Set.range (UniversalEnvelopingAlgebra.ι k) ⊆ (good : Set U) := by
    rintro _ ⟨x, rfl⟩
    exact goodComul_iota x (hx x)
  let of : LieHom k L good :=
    { toLinearMap := (UniversalEnvelopingAlgebra.ι k).toLinearMap.codRestrict
        good.toSubmodule (fun x => hi ⟨x, rfl⟩)
      map_lie' := fun {x y} => by
        apply Subtype.ext
        change (UniversalEnvelopingAlgebra.ι k) ⁅x, y⁆ = _
        exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι k) x y }
  have hval : good.val.comp (UniversalEnvelopingAlgebra.lift k of) =
      AlgHom.id k U := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp [of]
    rfl
  have hu : u ∈ good := by
    have heq : good.val (UniversalEnvelopingAlgebra.lift k of u) = u :=
      DFunLike.congr_fun hval u
    rw [← heq]
    exact (UniversalEnvelopingAlgebra.lift k of u).property
  exact hu

def GoodCounit (u : U) : Prop := ∀ m : M,
  Coalgebra.counit (R := k) (A := M) (u • m) =
    Coalgebra.counit (R := k) (A := U) u *
      Coalgebra.counit (R := k) (A := M) m

theorem goodCounit_all
    (hx : ∀ (x : L) (m : M),
      Coalgebra.counit (R := k) (A := M) ⁅x, m⁆ = 0)
    (u : U) : GoodCounit (M := M) u := by
  let good : Subalgebra k U :=
    { carrier := {a | GoodCounit (M := M) a}
      mul_mem' := fun ha hb m => by
        rw [mul_smul, ha, hb, Bialgebra.counit_mul]
        ring
      add_mem' := fun ha hb m => by
        simp only [add_smul, map_add, ha m, hb m]
        ring
      algebraMap_mem' := fun r m => by
        rw [IsScalarTower.algebraMap_smul]
        simp }
  have hi : Set.range (UniversalEnvelopingAlgebra.ι k) ⊆ (good : Set U) := by
    rintro _ ⟨x, rfl⟩
    intro m
    rw [iota_smul, hx]
    have he : counit (R := k) (UniversalEnvelopingAlgebra.ι k x) = 0 := by
      change eps (UniversalEnvelopingAlgebra.ι k x) = 0
      exact eps_iota x
    rw [he]
    simp
  let of : LieHom k L good :=
    { toLinearMap := (UniversalEnvelopingAlgebra.ι k).toLinearMap.codRestrict
        good.toSubmodule (fun x => hi ⟨x, rfl⟩)
      map_lie' := fun {x y} => by
        apply Subtype.ext
        change (UniversalEnvelopingAlgebra.ι k) ⁅x, y⁆ = _
        exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι k) x y }
  have hval : good.val.comp (UniversalEnvelopingAlgebra.lift k of) =
      AlgHom.id k U := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp [of]
    rfl
  have hu : u ∈ good := by
    have heq : good.val (UniversalEnvelopingAlgebra.lift k of u) = u :=
      DFunLike.congr_fun hval u
    rw [← heq]
    exact (UniversalEnvelopingAlgebra.lift k of u).property
  exact hu

variable [Coalgebra.IsLieModuleCoalgebra k L M]

noncomputable local instance : HopfAmenability.IsHopfModuleCoalgebra k U M where
  counit_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hp hq
    | tmul u m =>
        simpa [mul_comm] using
          (goodCounit_all (fun x m => Coalgebra.counit_lie_apply x m) u m)
  comul_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hp hq
    | tmul u m =>
        simpa using
          (goodComul_all (fun x m => Coalgebra.comul_lie_apply x m) u m)

/-- The finite subcoalgebra of `U(L)` spanned by `1` and a finite-dimensional
subspace of primitive generators. -/
noncomputable def lieActingSubcoalgebra
    (F : Submodule k L) [FiniteDimensional k F] : FiniteSubcoalgebra k U where
  carrier := k ∙ (1 : U) ⊔ Submodule.map
    (UniversalEnvelopingAlgebra.ι k).toLinearMap F
  isSubcoalgebra := by
    let P : Submodule k U := k ∙ (1 : U) ⊔ Submodule.map
      (UniversalEnvelopingAlgebra.ι k).toLinearMap F
    let stable : Submodule k U :=
      (LinearMap.range (TensorProduct.mapIncl P P)).comap Coalgebra.comul
    change P ≤ stable
    apply sup_le
    · apply Submodule.span_le.2
      intro x hx
      rcases hx with rfl
      change Coalgebra.comul (R := k) (1 : U) ∈
        LinearMap.range (TensorProduct.mapIncl P P)
      let oneP : P := ⟨1, Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self 1)⟩
      exact ⟨oneP ⊗ₜ[k] oneP, by
        rw [Bialgebra.comul_one]
        change (1 : U) ⊗ₜ[k] (1 : U) = (1 : U ⊗[k] U)
        rw [Algebra.TensorProduct.one_def]⟩
    · rintro _ ⟨x, hx, rfl⟩
      change Coalgebra.comul (R := k) (UniversalEnvelopingAlgebra.ι k x) ∈
        LinearMap.range (TensorProduct.mapIncl P P)
      let oneP : P := ⟨1, Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self 1)⟩
      let xP : P := ⟨UniversalEnvelopingAlgebra.ι k x,
        Submodule.mem_sup_right ⟨x, hx, rfl⟩⟩
      refine ⟨xP ⊗ₜ[k] oneP + oneP ⊗ₜ[k] xP, ?_⟩
      change _ = delta (UniversalEnvelopingAlgebra.ι k x)
      rw [delta_iota]
      rfl
  finiteDimensional := by
    exact Submodule.finiteDimensional_sup _ _

omit [Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M] in
theorem actionSubspace_lieActingSubcoalgebra
    (F : Submodule k L) [FiniteDimensional k F] (E : Submodule k M) :
    actionSubspace (lieActingSubcoalgebra F).carrier E =
      lieExpansion F E := by
  rw [actionSubspace_eq_map₂, lieExpansion,
    lieActionSubspace_eq_map₂]
  change Submodule.map₂ (Algebra.lsmul k k M).toLinearMap
      (k ∙ (1 : U) ⊔ Submodule.map
        (UniversalEnvelopingAlgebra.ι k).toLinearMap F) E = _
  rw [Submodule.map₂_sup_left]
  congr 1
  · apply le_antisymm
    · apply Submodule.map₂_le.2
      intro a ha m hm
      rw [Submodule.mem_span_singleton] at ha
      rcases ha with ⟨r, rfl⟩
      simpa [smul_smul] using E.smul_mem r hm
    · intro m hm
      simpa using Submodule.mem_map₂
        (Algebra.lsmul k k M).toLinearMap _ _
        (Submodule.mem_span_singleton_self (1 : U)) hm
  · apply le_antisymm
    · apply Submodule.map₂_le.2
      intro a ha m hm
      rcases ha with ⟨x, hx, rfl⟩
      have hmem := Submodule.mem_map₂
        (lieActionBilinear (k := k) (L := L) (M := M)) F E hx hm
      have heq : ((Algebra.lsmul k k M).toLinearMap
          ((UniversalEnvelopingAlgebra.ι k).toLinearMap x)) m =
          (lieActionBilinear (k := k) (L := L) (M := M) x) m := by
        exact iota_smul x m
      rw [heq]
      exact hmem
    · apply Submodule.map₂_le.2
      intro x hx m hm
      have hmem := Submodule.mem_map₂
        (Algebra.lsmul k k M).toLinearMap
        (Submodule.map (UniversalEnvelopingAlgebra.ι k).toLinearMap F) E
        ⟨x, hx, rfl⟩ hm
      have heq : (lieActionBilinear (k := k) (L := L) (M := M) x) m =
          ((Algebra.lsmul k k M).toLinearMap
            ((UniversalEnvelopingAlgebra.ι k).toLinearMap x)) m := by
        exact (iota_smul x m).symm
      rw [heq]
      exact hmem

/-- Every nonzero finite-dimensional subspace of a Lie-module coalgebra can
be rounded to a nonzero finite subcoalgebra with no larger Lie-expansion
ratio. -/
theorem exists_finiteSubcoalgebra_lie_ratio_le
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F E) : ℚ) /
            (finrank k E : ℚ) := by
  simpa only [actionSubspace_lieActingSubcoalgebra] using
    (exists_finiteSubcoalgebra_action_ratio_le
      (lieActingSubcoalgebra F) E hE)

/-- The finite-dimensional Følner-subspace condition for a Lie module. -/
def HasLieFolnerSubspaces : Prop :=
  ∀ (F : Submodule k L), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k M,
        E ≠ ⊥ ∧ FiniteDimensional k E ∧
          (sfinrank k (lieExpansion F E) : ℚ) ≤
          (1 + ε) * sfinrank k E

/-- Amenability of a Lie-module coalgebra, defined by the existence of
almost-invariant nonzero finite subcoalgebras. -/
def IsAmenableLieModule : Prop :=
  ∀ (F : Submodule k L), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : FiniteSubcoalgebra k M,
        C.carrier ≠ ⊥ ∧
          (sfinrank k (lieExpansion F C.carrier) : ℚ) ≤
            (1 + ε) * finrank k C.carrier

/-- Følner subspaces in a Lie-module coalgebra round to almost-invariant
finite subcoalgebras. -/
theorem HasLieFolnerSubspaces.isAmenableLieModule
    (hM : HasLieFolnerSubspaces (k := k) (L := L) (M := M)) :
    IsAmenableLieModule (k := k) (L := L) (M := M) := by
  intro F hF ε hε
  let : FiniteDimensional k F := hF
  obtain ⟨E, hE, hEfd, hFolner⟩ := hM F inferInstance ε hε
  let : FiniteDimensional k E := hEfd
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_lie_ratio_le F E hE
  refine ⟨C, hC, ?_⟩
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let : Nontrivial C.carrier := Submodule.nontrivial_iff_ne_bot.mpr hC
  have hEpos : (0 : ℚ) < finrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hCpos : (0 : ℚ) < finrank k C.carrier := by
    exact_mod_cast Module.finrank_pos (R := k) (M := C.carrier)
  have hsource :
      (sfinrank k (lieExpansion F E) : ℚ) / finrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).mpr hFolner
  exact (div_le_iff₀ hCpos).mp (hratio.trans hsource)

omit [Coalgebra.IsLieModuleCoalgebra k L M] in
/-- Almost-invariant finite subcoalgebras are, in particular, Følner
subspaces. -/
theorem IsAmenableLieModule.hasFolnerSubspaces
    (hM : IsAmenableLieModule (k := k) (L := L) (M := M)) :
    HasLieFolnerSubspaces (k := k) (L := L) (M := M) := by
  intro F hF ε hε
  obtain ⟨C, hC, hFolner⟩ := hM F hF ε hε
  exact ⟨C.carrier, hC, inferInstance, hFolner⟩

/-- The subcoalgebra and subspace Følner conditions for a Lie-module
coalgebra are equivalent. -/
theorem isAmenableLieModule_iff_hasFolnerSubspaces :
    IsAmenableLieModule (k := k) (L := L) (M := M) ↔
      HasLieFolnerSubspaces (k := k) (L := L) (M := M) :=
  ⟨IsAmenableLieModule.hasFolnerSubspaces,
    HasLieFolnerSubspaces.isAmenableLieModule⟩

omit [Coalgebra.IsLieModuleCoalgebra k L M] in
/-- Projection form of amenability: an amenable Lie-module coalgebra has an
almost-invariant finite subcoalgebra for every finite-dimensional test
subspace. -/
theorem IsAmenableLieModule.exists_finiteSubcoalgebra_folner
    (hM : IsAmenableLieModule (k := k) (L := L) (M := M))
    (F : Submodule k L) [FiniteDimensional k F]
    (ε : ℚ) (hε : 0 < ε) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) ≤
          (1 + ε) * finrank k C.carrier := by
  exact hM F inferInstance ε hε
end Action
end HopfAmenability
