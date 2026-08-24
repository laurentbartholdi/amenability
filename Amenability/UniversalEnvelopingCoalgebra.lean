/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The standard Hopf algebra structure on a universal enveloping algebra

This file supplies the cocommutative bialgebra and Hopf algebra instances for
the universal enveloping algebra of a Lie algebra. The declarations are kept
in namespace Coalgebra and isolated from the amenability development so that
they can be proposed for future inclusion in Mathlib.
-/

open TensorProduct
open Coalgebra
namespace Coalgebra
universe u v
variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
local notation "U" => UniversalEnvelopingAlgebra k L
attribute [local instance 100] LieRing.ofAssociativeRing
example (a b c d : U) : (a ⊗ₜ[k] b) * (c ⊗ₜ[k] d) = (a * c) ⊗ₜ[k] (b * d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
noncomputable def prim : L →ₗ⁅k⁆ U ⊗[k] U where
  toLinearMap :=
    (Algebra.TensorProduct.includeLeft.toLinearMap.comp
      (UniversalEnvelopingAlgebra.ι k).toLinearMap) +
    (Algebra.TensorProduct.includeRight.toLinearMap.comp
      (UniversalEnvelopingAlgebra.ι k).toLinearMap)
  map_lie' := fun {x y} => by
    change
      (UniversalEnvelopingAlgebra.ι k ⁅x, y⁆) ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k ⁅x, y⁆) =
        ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
            1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x)) *
          ((UniversalEnvelopingAlgebra.ι k y) ⊗ₜ[k] 1 +
            1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k y)) -
        ((UniversalEnvelopingAlgebra.ι k y) ⊗ₜ[k] 1 +
            1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k y)) *
          ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
            1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x))
    rw [LieHom.map_lie]
    simp only [LieRing.of_associative_ring_bracket, mul_add, add_mul,
      sub_eq_add_neg]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
    simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg]
    abel

noncomputable def delta : U →ₐ[k] U ⊗[k] U :=
  UniversalEnvelopingAlgebra.lift k prim

noncomputable def epsLie : LieHom k L k := 0

noncomputable def eps : U →ₐ[k] k :=
  UniversalEnvelopingAlgebra.lift k epsLie

@[simp] theorem delta_iota (x : L) : delta (UniversalEnvelopingAlgebra.ι k x) =
    (UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
      1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x) := by
  rw [delta, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

@[simp] theorem eps_iota (x : L) : eps (UniversalEnvelopingAlgebra.ι k x) = 0 := by
  simp [eps, epsLie]

noncomputable instance : Bialgebra k U := Bialgebra.ofAlgHom delta eps (by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply, delta_iota]
    change (Algebra.TensorProduct.assoc k k k U U U)
        ((Algebra.TensorProduct.map delta (AlgHom.id k U))
          ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
            1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x))) =
      (Algebra.TensorProduct.map (AlgHom.id k U) delta)
        ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x))
    simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
    rw [delta_iota]
    simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul,
      TensorProduct.tmul_add, Algebra.TensorProduct.assoc_tmul]
    abel) (by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply, delta_iota]
    change (Algebra.TensorProduct.map (eps (k := k) (L := L)) (AlgHom.id k U))
        ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x)) =
      (Algebra.TensorProduct.lid k U).symm (UniversalEnvelopingAlgebra.ι k x)
    simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
    rw [eps_iota]
    simp) (by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply, delta_iota]
    change (Algebra.TensorProduct.map (AlgHom.id k U) (eps (k := k) (L := L)))
        ((UniversalEnvelopingAlgebra.ι k x) ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] (UniversalEnvelopingAlgebra.ι k x)) =
      (Algebra.TensorProduct.rid k k U).symm (UniversalEnvelopingAlgebra.ι k x)
    simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
    rw [eps_iota]
    simp)

noncomputable instance : Coalgebra.IsCocomm k U := ⟨by
  apply LinearMap.ext
  intro u
  change (TensorProduct.comm k U U) (delta u) = delta u
  have h : (Algebra.TensorProduct.comm k U U).toAlgHom.comp delta = delta := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply,
      delta_iota]
    simp
    abel
  exact DFunLike.congr_fun h u⟩

noncomputable def antipodeLie : LieHom k L Uᵐᵒᵖ where
  toLinearMap := -(MulOpposite.opLinearEquiv k).toLinearMap.comp
    (UniversalEnvelopingAlgebra.ι k).toLinearMap
  map_lie' := fun {x y} => by
    change MulOpposite.op (-(UniversalEnvelopingAlgebra.ι k ⁅x, y⁆)) =
      ⁅MulOpposite.op (-(UniversalEnvelopingAlgebra.ι k x)),
        MulOpposite.op (-(UniversalEnvelopingAlgebra.ι k y))⁆
    rw [LieHom.map_lie]
    simp [LieRing.of_associative_ring_bracket]

noncomputable def antipodeAnti : U →ₐ[k] Uᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift k antipodeLie

noncomputable def antipode : U →ₗ[k] U where
  toFun u := MulOpposite.unop (antipodeAnti u)
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem antipode_iota (x : L) :
    antipode (UniversalEnvelopingAlgebra.ι k x) =
      -(UniversalEnvelopingAlgebra.ι k x) := by
  change MulOpposite.unop
      (antipodeAnti (UniversalEnvelopingAlgebra.ι k x)) = _
  rw [antipodeAnti, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

@[simp] theorem antipode_one : antipode (1 : U) = 1 := by
  simp [antipode, antipodeAnti]

@[simp] theorem antipode_algebraMap (r : k) :
    antipode (algebraMap k U r) = algebraMap k U r := by
  rw [show algebraMap k U r = r • (1 : U) by simp [Algebra.smul_def]]
  rw [map_smul, antipode_one]

theorem antipode_mul (x y : U) : antipode (x * y) = antipode y * antipode x := by
  simp [antipode, antipodeAnti]

noncomputable def leftConv : U →ₗ[k] U :=
  LinearMap.mul' k U ∘ₗ _root_.TensorProduct.map antipode LinearMap.id ∘ₗ
    Coalgebra.comul

@[simp] theorem leftConv_iota (x : L) :
    leftConv (UniversalEnvelopingAlgebra.ι k x) = 0 := by
  change LinearMap.mul' k U
    (_root_.TensorProduct.map antipode LinearMap.id
      (delta (UniversalEnvelopingAlgebra.ι k x))) = 0
  rw [delta_iota]
  simp only [UniversalEnvelopingAlgebra.ι_apply, map_add, map_tmul,
    LinearMap.id_coe, id_eq, antipode_one, LinearMap.mul'_apply, mul_one,
    one_mul]
  change antipode (UniversalEnvelopingAlgebra.ι k x) +
    UniversalEnvelopingAlgebra.ι k x = 0
  rw [antipode_iota]
  simp

theorem leftConv_mul_of (u v : U)
    (hu : leftConv u = Coalgebra.counit (R := k) u • (1 : U))
    (hv : leftConv v = Coalgebra.counit (R := k) v • (1 : U)) :
    leftConv (u * v) = Coalgebra.counit (R := k) (u * v) • (1 : U) := by
  let ru := ℛ k u
  let rv := ℛ k v
  rw [leftConv, LinearMap.comp_apply, LinearMap.comp_apply, Bialgebra.comul_mul,
    ← ru.eq, ← rv.eq]
  simp only [map_sum, _root_.TensorProduct.map_tmul, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply,
    antipode_mul, LinearMap.id_apply]
  have hu' : ∑ i ∈ ru.index, antipode (ru.left i) * ru.right i =
      counit (R := k) u • (1 : U) := by
    rw [leftConv, LinearMap.comp_apply, LinearMap.comp_apply, ← ru.eq] at hu
    simpa using hu
  have hv' : ∑ i ∈ rv.index, antipode (rv.left i) * rv.right i =
      counit (R := k) v • (1 : U) := by
    rw [leftConv, LinearMap.comp_apply, LinearMap.comp_apply, ← rv.eq] at hv
    simpa using hv
  simp only [mul_assoc]
  simp_rw [← mul_assoc (antipode (ru.left _))]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [hu']
  simp_rw [smul_mul_assoc, one_mul, mul_smul_comm]
  rw [← Finset.smul_sum, hv']
  simp [Bialgebra.counit_mul, smul_smul]

noncomputable def rightConv : U →ₗ[k] U :=
  LinearMap.mul' k U ∘ₗ _root_.TensorProduct.map LinearMap.id antipode ∘ₗ
    Coalgebra.comul

@[simp] theorem rightConv_iota (x : L) :
    rightConv (UniversalEnvelopingAlgebra.ι k x) = 0 := by
  change LinearMap.mul' k U
    (_root_.TensorProduct.map LinearMap.id antipode
      (delta (UniversalEnvelopingAlgebra.ι k x))) = 0
  rw [delta_iota]
  simp only [UniversalEnvelopingAlgebra.ι_apply, map_add, map_tmul,
    LinearMap.id_coe, id_eq, antipode_one, LinearMap.mul'_apply, mul_one,
    one_mul]
  change UniversalEnvelopingAlgebra.ι k x +
    antipode (UniversalEnvelopingAlgebra.ι k x) = 0
  rw [antipode_iota]
  simp

theorem rightConv_mul_of (u v : U)
    (hu : rightConv u = counit (R := k) u • (1 : U))
    (hv : rightConv v = counit (R := k) v • (1 : U)) :
    rightConv (u * v) = counit (R := k) (u * v) • (1 : U) := by
  let ru := ℛ k u
  let rv := ℛ k v
  rw [rightConv, LinearMap.comp_apply, LinearMap.comp_apply,
    Bialgebra.comul_mul, ← ru.eq, ← rv.eq]
  simp only [map_sum, _root_.TensorProduct.map_tmul, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply,
    antipode_mul, LinearMap.id_apply]
  have hu' : ∑ i ∈ ru.index, ru.left i * antipode (ru.right i) =
      counit (R := k) u • (1 : U) := by
    rw [rightConv, LinearMap.comp_apply, LinearMap.comp_apply, ← ru.eq] at hu
    simpa using hu
  have hv' : ∑ i ∈ rv.index, rv.left i * antipode (rv.right i) =
      counit (R := k) v • (1 : U) := by
    rw [rightConv, LinearMap.comp_apply, LinearMap.comp_apply, ← rv.eq] at hv
    simpa using hv
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  simp_rw [← mul_assoc (rv.left _)]
  simp_rw [← mul_assoc (ru.left _)]
  simp_rw [← Finset.sum_mul]
  simp_rw [mul_assoc (ru.left _)]
  simp_rw [← Finset.mul_sum]
  rw [hv']
  simp_rw [mul_smul_comm, mul_one, smul_mul_assoc]
  rw [← Finset.smul_sum, hu']
  simp [Bialgebra.counit_mul, smul_smul, mul_comm]

theorem leftConv_eq (u : U) :
    leftConv u = counit (R := k) u • (1 : U) := by
  obtain ⟨a, rfl⟩ :=
    RingCon.mk'_surjective (UniversalEnvelopingAlgebra.ringCon k L) u
  change leftConv (UniversalEnvelopingAlgebra.mkAlgHom k L a) =
    counit (R := k) (UniversalEnvelopingAlgebra.mkAlgHom k L a) • (1 : U)
  induction a using TensorAlgebra.induction with
  | algebraMap r =>
      rw [(UniversalEnvelopingAlgebra.mkAlgHom k L).commutes r]
      simp [leftConv, Algebra.smul_def]
  | ι x =>
      rw [← UniversalEnvelopingAlgebra.ι_apply]
      rw [leftConv_iota]
      have he : counit (R := k) (UniversalEnvelopingAlgebra.ι k x) = 0 := by
        change eps (UniversalEnvelopingAlgebra.ι k x) = 0
        exact eps_iota x
      rw [he]
      simp
  | mul a b ha hb =>
      rw [map_mul]
      exact leftConv_mul_of _ _ ha hb
  | add a b ha hb => simp [map_add, ha, hb, add_smul]

theorem rightConv_eq (u : U) :
    rightConv u = counit (R := k) u • (1 : U) := by
  obtain ⟨a, rfl⟩ :=
    RingCon.mk'_surjective (UniversalEnvelopingAlgebra.ringCon k L) u
  change rightConv (UniversalEnvelopingAlgebra.mkAlgHom k L a) =
    counit (R := k) (UniversalEnvelopingAlgebra.mkAlgHom k L a) • (1 : U)
  induction a using TensorAlgebra.induction with
  | algebraMap r => simp [rightConv, Algebra.smul_def]
  | ι x =>
      rw [← UniversalEnvelopingAlgebra.ι_apply]
      rw [rightConv_iota]
      have he : counit (R := k) (UniversalEnvelopingAlgebra.ι k x) = 0 := by
        change eps (UniversalEnvelopingAlgebra.ι k x) = 0
        exact eps_iota x
      rw [he]
      simp
  | mul a b ha hb =>
      rw [map_mul]
      exact rightConv_mul_of _ _ ha hb
  | add a b ha hb => simp [map_add, ha, hb, add_smul]

noncomputable instance : HopfAlgebra k U := HopfAlgebra.ofConvInverse antipode (by
    apply WithConv.ofConv_injective
    apply LinearMap.ext
    intro u
    simpa [LinearMap.convMul_apply, LinearMap.convOne_apply, leftConv,
      Algebra.smul_def] using
      leftConv_eq (k := k) (L := L) u) (by
    apply WithConv.ofConv_injective
    apply LinearMap.ext
    intro u
    simpa [LinearMap.convMul_apply, LinearMap.convOne_apply, rightConv,
      Algebra.smul_def] using
      rightConv_eq (k := k) (L := L) u)


end Coalgebra
