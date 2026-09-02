/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.ExteriorShiftDerivation
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# A locally-finite-by-one Lie algebra with exponential growth

This file constructs the explicit example used for Theorem F.  Its locally
finite ideal consists of finite matrices over an exterior algebra.  A shift
derivation supplies the one-dimensional extension, while matrix-unit
commutators encode binary words as independent exterior monomials.
-/

namespace HopfAmenability

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The two exterior generators introduced at each shift level. -/
abbrev BinaryGeneratorModule := (ℕ × Bool) →₀ k

/-- The exterior coefficient algebra used in the exponential example. -/
abbrev BinaryExterior := ExteriorAlgebra k (BinaryGeneratorModule k)

/-- Three-by-three matrices over the binary exterior algebra. -/
abbrev BinaryMatrixLieAlgebra := Matrix (Fin 3) (Fin 3) (BinaryExterior k)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Shift both families of exterior generators one step to the right. -/
def binaryGeneratorShift : BinaryGeneratorModule k →ₗ[k] BinaryGeneratorModule k :=
  Finsupp.lmapDomain k k fun p : ℕ × Bool => (p.1 + 1, p.2)

@[simp]
theorem binaryGeneratorShift_single (n : ℕ) (b : Bool) (r : k) :
    binaryGeneratorShift k (Finsupp.single (n, b) r) =
      Finsupp.single (n + 1, b) r := by
  simp [binaryGeneratorShift]

/-- The exterior generator at level `n` in family `b`. -/
def binaryExteriorGenerator (n : ℕ) (b : Bool) : BinaryExterior k :=
  ExteriorAlgebra.ι k (Finsupp.single (n, b) 1)

@[simp]
theorem exteriorShift_generator (n : ℕ) (b : Bool) :
    ExteriorAlgebra.lieDerivation (binaryGeneratorShift k)
        (binaryExteriorGenerator k n b) =
      binaryExteriorGenerator k (n + 1) b := by
  simp [binaryExteriorGenerator]

/-- The shift derivation acting entrywise on three-by-three matrices. -/
def binaryMatrixShiftDerivation :
    LieDerivation k (BinaryMatrixLieAlgebra k) (BinaryMatrixLieAlgebra k) :=
  Matrix.lieDerivationOfProductDerivation
    (ExteriorAlgebra.derivationLinear (binaryGeneratorShift k))
    (ExteriorAlgebra.derivationLinear_mul (binaryGeneratorShift k))

@[simp]
theorem binaryMatrixShiftDerivation_apply
    (X : BinaryMatrixLieAlgebra k) (i j : Fin 3) :
    binaryMatrixShiftDerivation k X i j =
      ExteriorAlgebra.derivationLinear (binaryGeneratorShift k) (X i j) :=
  rfl

/-- The one-dimensional abelian Lie algebra acts through scalar multiples of
the binary shift derivation. -/
def binaryShiftAction :
    k →ₗ⁅k⁆ LieDerivation k (BinaryMatrixLieAlgebra k)
      (BinaryMatrixLieAlgebra k) where
  toFun r := r • binaryMatrixShiftDerivation k
  map_add' r s := by simp [add_smul]
  map_smul' r s := by simp [mul_smul]
  map_lie' := by
    intro r s
    have hrs : r * s - s * r = 0 := sub_eq_zero.mpr (mul_comm r s)
    rw [LieRing.of_associative_ring_bracket, hrs, zero_smul]
    simp

/-- The ambient locally-finite-by-one semidirect product. -/
abbrev BinaryShiftLieAlgebra :=
  BinaryMatrixLieAlgebra k ⋊⁅binaryShiftAction k⁆ k

/-- A matrix unit with a coefficient in the binary exterior algebra. -/
def binaryMatrixUnit (i j : Fin 3) (a : BinaryExterior k) :
    BinaryMatrixLieAlgebra k :=
  Matrix.single i j a

@[simp]
theorem binaryMatrixShiftDerivation_matrixUnit
    (i j : Fin 3) (a : BinaryExterior k) :
    binaryMatrixShiftDerivation k (binaryMatrixUnit k i j a) =
      binaryMatrixUnit k i j
        (ExteriorAlgebra.derivationLinear (binaryGeneratorShift k) a) := by
  ext p q
  change ExteriorAlgebra.derivationLinear (binaryGeneratorShift k)
      (Matrix.single i j a p q) =
    Matrix.single i j
      (ExteriorAlgebra.derivationLinear (binaryGeneratorShift k) a) p q
  simp only [Matrix.single, Matrix.of_apply]
  split <;> simp_all

/-- The first matrix-unit operation used to append an exterior generator. -/
theorem lie_matrixUnit_zero_one_one_two
    (a b : BinaryExterior k) :
    ⁅binaryMatrixUnit k 0 1 a, binaryMatrixUnit k 1 2 b⁆ =
      binaryMatrixUnit k 0 2 (a * b) := by
  rw [LieRing.of_associative_ring_bracket]
  simp [binaryMatrixUnit, Matrix.single_mul_single_of_ne]

/-- The second matrix-unit operation used to append an exterior generator. -/
theorem lie_matrixUnit_zero_two_two_one
    (a b : BinaryExterior k) :
    ⁅binaryMatrixUnit k 0 2 a, binaryMatrixUnit k 2 1 b⁆ =
      binaryMatrixUnit k 0 1 (a * b) := by
  rw [LieRing.of_associative_ring_bracket]
  simp [binaryMatrixUnit, Matrix.single_mul_single_of_ne]

end

end HopfAmenability
