/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Tactic.NoncommRing

/-!
# Derivations of exterior algebras

A linear endomorphism of the generating module extends canonically to an
ordinary derivation of its exterior algebra.  We construct the extension by
mapping into the trivial square-zero extension: the first coordinate is the
generator and the second coordinate is its prescribed derivative.
-/

namespace ExteriorAlgebra

noncomputable section

universe u v

variable {k : Type u} [CommRing k]
variable {M : Type v} [AddCommGroup M] [Module k M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The tangent lift of a linear map on the generators to the trivial
square-zero extension of the exterior algebra. -/
def tangentGenerator (f : M →ₗ[k] M) :
    M →ₗ[k] TrivSqZeroExt (ExteriorAlgebra k M) (ExteriorAlgebra k M) where
  toFun m := show TrivSqZeroExt _ _ from (ι k m, ι k (f m))
  map_add' x y := by
    change (ι k (x + y), ι k (f (x + y))) =
      (ι k x + ι k y, ι k (f x) + ι k (f y))
    simp
  map_smul' r x := by
    change (ι k (r • x), ι k (f (r • x))) =
      (r • ι k x, r • ι k (f x))
    simp

theorem tangentGenerator_sq (f : M →ₗ[k] M) (m : M) :
    tangentGenerator f m * tangentGenerator f m = 0 := by
  ext
  · exact ι_sq_zero m
  · change ι k m * ι k (f m) + ι k (f m) * ι k m = 0
    exact ι_add_mul_swap m (f m)

/-- The algebra map to dual numbers associated to a linear endomorphism of
the exterior generators. -/
def tangentLift (f : M →ₗ[k] M) :
    ExteriorAlgebra k M →ₐ[k]
      TrivSqZeroExt (ExteriorAlgebra k M) (ExteriorAlgebra k M) :=
  ExteriorAlgebra.lift k ⟨tangentGenerator f, tangentGenerator_sq f⟩

@[simp]
theorem tangentLift_ι (f : M →ₗ[k] M) (m : M) :
    tangentLift f (ι k m) =
      (show TrivSqZeroExt _ _ from (ι k m, ι k (f m))) := by
  rw [tangentLift, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- The first component of the tangent lift is the identity. -/
theorem tangentLift_fst (f : M →ₗ[k] M) (x : ExteriorAlgebra k M) :
    (tangentLift f x).fst = x := by
  let fst : TrivSqZeroExt (ExteriorAlgebra k M) (ExteriorAlgebra k M) →ₐ[k]
      ExteriorAlgebra k M := TrivSqZeroExt.fstHom k _ _
  have h : fst.comp (tangentLift f) = AlgHom.id k _ := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    change (tangentLift f (ι k m)).fst = ι k m
    rw [tangentLift_ι]
    rfl
  exact DFunLike.congr_fun h x

/-- The ordinary product derivation induced by a linear endomorphism of the
exterior generators, regarded as a linear map. -/
def derivationLinear (f : M →ₗ[k] M) :
    ExteriorAlgebra k M →ₗ[k] ExteriorAlgebra k M where
  toFun x := (tangentLift f x).snd
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
theorem derivationLinear_ι (f : M →ₗ[k] M) (m : M) :
    derivationLinear f (ι k m) = ι k (f m) := by
  simp [derivationLinear]

theorem derivationLinear_mul (f : M →ₗ[k] M)
    (x y : ExteriorAlgebra k M) :
    derivationLinear f (x * y) =
      x * derivationLinear f y + derivationLinear f x * y := by
  change (tangentLift f (x * y)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul]
  simp only [tangentLift_fst]
  rfl

/-- The Lie derivation on the commutator Lie algebra underlying an exterior
algebra, induced by a linear endomorphism of its generators. -/
def lieDerivation (f : M →ₗ[k] M) :
    LieDerivation k (ExteriorAlgebra k M) (ExteriorAlgebra k M) where
  toLinearMap := derivationLinear f
  leibniz' x y := by
    change derivationLinear f (x * y - y * x) =
      x * derivationLinear f y - derivationLinear f y * x -
        (y * derivationLinear f x - derivationLinear f x * y)
    simp only [map_sub, derivationLinear_mul]
    noncomm_ring

@[simp]
theorem lieDerivation_ι (f : M →ₗ[k] M) (m : M) :
    lieDerivation f (ι k m) = ι k (f m) :=
  derivationLinear_ι f m

end

end ExteriorAlgebra

namespace Matrix

noncomputable section

universe u v w

variable {k : Type u} [CommRing k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {n : Type w} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Apply a linear endomorphism entrywise to a finite square matrix. -/
def mapLinear (D : A →ₗ[k] A) : Matrix n n A →ₗ[k] Matrix n n A where
  toFun X := X.map D
  map_add' X Y := by
    ext i j
    simp
  map_smul' r X := by
    ext i j
    simp

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem mapLinear_apply (D : A →ₗ[k] A) (X : Matrix n n A) (i j : n) :
    mapLinear D X i j = D (X i j) :=
  rfl

omit [DecidableEq n] in
theorem mapLinear_mul (D : A →ₗ[k] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y)
    (X Y : Matrix n n A) :
    mapLinear D (X * Y) = X * mapLinear D Y + mapLinear D X * Y := by
  ext i j
  simp only [mapLinear_apply, Matrix.mul_apply, map_sum, hD,
    Finset.sum_add_distrib, Matrix.add_apply]

/-- An ordinary product derivation acts entrywise as a Lie derivation on
finite square matrices. -/
def lieDerivationOfProductDerivation (D : A →ₗ[k] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) :
    LieDerivation k (Matrix n n A) (Matrix n n A) where
  toLinearMap := mapLinear D
  leibniz' X Y := by
    change mapLinear D (X * Y - Y * X) =
      X * mapLinear D Y - mapLinear D Y * X -
        (Y * mapLinear D X - mapLinear D X * Y)
    simp only [map_sub, mapLinear_mul D hD]
    noncomm_ring

end

end Matrix
