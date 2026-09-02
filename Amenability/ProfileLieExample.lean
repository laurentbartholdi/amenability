/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.ShiftProfileAlgebra
import Amenability.LieGrowth
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The exponential locally-finite-by-one Lie algebra

This file encodes products in the shift-profile algebra by commutators of
four elementary matrices.  It supplies the concrete example used in
Theorem F.
-/

namespace HopfAmenability.ProfileLieExample

noncomputable section

universe u

open LocallyMatrixProfile ShiftProfileAlgebra

variable (k : Type u) [Field k]

abbrev Ambient := Matrix (Fin 3) (Fin 3) (ProfileEnd k)

local instance (priority := 100) ambientLieRing : LieRing (Ambient k) :=
  LieRing.ofAssociativeRing

local instance (priority := 100) ambientLieAlgebra : LieAlgebra k (Ambient k) :=
  LieAlgebra.ofAssociativeAlgebra

def elementary (i j : Fin 3) (r : ProfileEnd k) : Ambient k :=
  Matrix.single i j r

def t : Ambient k := elementary k 1 1 (shift k)
def x : Ambient k := elementary k 0 1 (store k)
def y : Ambient k := elementary k 1 2 (store k)
def z : Ambient k := elementary k 2 1 (store k)

def generatorSet : Set (Ambient k) := {t k, x k, y k, z k}

/-- The four-dimensional generating subspace. -/
def generators : Submodule k (Ambient k) :=
  Submodule.span k (generatorSet k)

instance moduleFinite_generators : Module.Finite k (generators k) :=
  Module.Finite.span_of_finite k (by simp [generatorSet])

theorem t_mem_generators : t k ∈ generators k :=
  Submodule.subset_span (by simp [generatorSet])

theorem x_mem_generators : x k ∈ generators k :=
  Submodule.subset_span (by simp [generatorSet])

theorem y_mem_generators : y k ∈ generators k :=
  Submodule.subset_span (by simp [generatorSet])

theorem z_mem_generators : z k ∈ generators k :=
  Submodule.subset_span (by simp [generatorSet])

/-- The finitely generated Lie algebra used in the example. -/
def ExampleLie : LieSubalgebra k (Ambient k) :=
  LieSubalgebra.lieSpan k (Ambient k) (generatorSet k)

def tLie : ExampleLie k := ⟨t k, LieSubalgebra.subset_lieSpan (by simp [generatorSet])⟩
def xLie : ExampleLie k := ⟨x k, LieSubalgebra.subset_lieSpan (by simp [generatorSet])⟩
def yLie : ExampleLie k := ⟨y k, LieSubalgebra.subset_lieSpan (by simp [generatorSet])⟩
def zLie : ExampleLie k := ⟨z k, LieSubalgebra.subset_lieSpan (by simp [generatorSet])⟩

/-- The generating subspace inside the generated Lie algebra. -/
def exampleGenerators : Submodule k (ExampleLie k) :=
  Submodule.span k {tLie k, xLie k, yLie k, zLie k}

instance moduleFinite_exampleGenerators :
    Module.Finite k (exampleGenerators k) :=
  Module.Finite.span_of_finite k (Set.toFinite _)

set_option synthInstance.maxHeartbeats 100000 in
-- Dependent subtype structures in the two nested Lie spans require deeper instance reduction.
theorem exampleLie_lieSpan_eq_top :
    LieSubalgebra.lieSpan k (ExampleLie k)
      (exampleGenerators k : Set (ExampleLie k)) = ⊤ := by
  let T := LieSubalgebra.lieSpan k (ExampleLie k)
    (exampleGenerators k : Set (ExampleLie k))
  have himage {a : Ambient k} (ha : a ∈ ExampleLie k) :
      ∃ b : T, ((b : ExampleLie k) : Ambient k) = a := by
    induction ha using LieSubalgebra.lieSpan_induction with
    | mem a ha =>
        simp only [generatorSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact ⟨⟨tLie k, LieSubalgebra.subset_lieSpan
            (Submodule.subset_span (by simp [tLie]))⟩, rfl⟩
        · exact ⟨⟨xLie k, LieSubalgebra.subset_lieSpan
            (Submodule.subset_span (by simp [xLie]))⟩, rfl⟩
        · exact ⟨⟨yLie k, LieSubalgebra.subset_lieSpan
            (Submodule.subset_span (by simp [yLie]))⟩, rfl⟩
        · exact ⟨⟨zLie k, LieSubalgebra.subset_lieSpan
            (Submodule.subset_span (by simp [zLie]))⟩, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha
        obtain ⟨b', hb'⟩ := ihb
        exact ⟨a' + b', by simp [ha', hb']⟩
    | smul r a ha iha =>
        obtain ⟨a', ha'⟩ := iha
        refine ⟨⟨r • (a' : ExampleLie k), T.smul_mem r a'.property⟩, ?_⟩
        change r • (((a' : T) : ExampleLie k) : Ambient k) = r • a
        rw [ha']
    | lie a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha
        obtain ⟨b', hb'⟩ := ihb
        exact ⟨⁅a', b'⁆, by simp [ha', hb']⟩
  apply top_unique
  rintro ⟨a, ha⟩ _
  obtain ⟨b, hb⟩ := himage ha
  have heq : (b : ExampleLie k) = ⟨a, ha⟩ := Subtype.ext hb
  rw [← heq]
  exact b.property

theorem exampleLie_isFinitelyGenerated :
    IsFinitelyGeneratedLieAlgebra (k := k) (ExampleLie k) := by
  classical
  let : DecidableEq (ExampleLie k) := Classical.decEq _
  let s : Finset (ExampleLie k) := {tLie k, xLie k, yLie k, zLie k}
  refine ⟨s, ?_⟩
  apply top_unique
  rw [← exampleLie_lieSpan_eq_top k]
  apply LieSubalgebra.lieSpan_le.mpr
  intro a ha
  apply LieSubalgebra.submodule_span_le_lieSpan
  simpa [exampleGenerators, s] using ha

theorem tLie_mem_exampleGenerators : tLie k ∈ exampleGenerators k :=
  Submodule.subset_span (by simp [tLie])

theorem xLie_mem_exampleGenerators : xLie k ∈ exampleGenerators k :=
  Submodule.subset_span (by simp [xLie])

theorem yLie_mem_exampleGenerators : yLie k ∈ exampleGenerators k :=
  Submodule.subset_span (by simp [yLie])

theorem zLie_mem_exampleGenerators : zLie k ∈ exampleGenerators k :=
  Submodule.subset_span (by simp [zLie])

/-- Append copies of the shift generator by right-nested brackets. -/
def appendShift : ℕ → Ambient k → Ambient k
  | 0, a => a
  | n + 1, a => ⁅appendShift n a, t k⁆

/-- The Lie word encoding a weighted profile word. -/
def encodedWord : List ℕ → Ambient k
  | [] => x k
  | i :: word => ⁅⁅appendShift k i (encodedWord word), y k⁆, z k⁆

/-- Number of brackets added after the initial generator in an encoded
profile word. -/
def encodedRadius : List ℕ → ℕ
  | [] => 0
  | i :: word => encodedRadius word + i + 2

theorem encodedRadius_le_twice_profileCost (word : List ℕ) :
    encodedRadius word ≤ 2 * profileCost word := by
  induction word with
  | nil => simp [encodedRadius, profileCost]
  | cons i word ih =>
      simp only [encodedRadius, profileCost_cons]
      omega

theorem exampleLie_lieGrowthBall_le_succ (n : ℕ) :
    lieGrowthBall k (exampleGenerators k) n ≤
      lieGrowthBall k (exampleGenerators k) (n + 1) := by
  rw [lieGrowthBall_succ, lieExpansion]
  exact le_sup_left

theorem exampleLie_lieGrowthBall_mono {m n : ℕ} (hmn : m ≤ n) :
    lieGrowthBall k (exampleGenerators k) m ≤
      lieGrowthBall k (exampleGenerators k) n := by
  induction hmn with
  | refl => exact le_rfl
  | @step n hmn ih => exact ih.trans (exampleLie_lieGrowthBall_le_succ k n)

theorem exampleLie_bracket_right_mem_succ
    {a b : ExampleLie k} {n : ℕ}
    (ha : a ∈ lieGrowthBall k (exampleGenerators k) n)
    (hb : b ∈ exampleGenerators k) :
    ⁅a, b⁆ ∈ lieGrowthBall k (exampleGenerators k) (n + 1) := by
  rw [lieGrowthBall_succ, lieExpansion]
  apply (le_sup_right : lieActionSubspace (exampleGenerators k)
    (lieGrowthBall k (exampleGenerators k) n) ≤ _)
  rw [lieActionSubspace_eq_map₂]
  have hleft : ⁅b, a⁆ ∈
      Submodule.map₂
        (lieActionBilinear (k := k) (L := ExampleLie k) (M := ExampleLie k))
        (exampleGenerators k) (lieGrowthBall k (exampleGenerators k) n) :=
    Submodule.apply_mem_map₂ _ hb ha
  simpa only [lie_skew] using neg_mem hleft

def appendShiftLie : ℕ → ExampleLie k → ExampleLie k
  | 0, a => a
  | n + 1, a => ⁅appendShiftLie n a, tLie k⁆

theorem appendShiftLie_coe (n : ℕ) (a : ExampleLie k) :
    (appendShiftLie k n a : Ambient k) = appendShift k n (a : Ambient k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [appendShiftLie, appendShift, ih, tLie]

def encodedWordLie : List ℕ → ExampleLie k
  | [] => xLie k
  | i :: word =>
      ⁅⁅appendShiftLie k i (encodedWordLie word), yLie k⁆, zLie k⁆

theorem encodedWordLie_coe (word : List ℕ) :
    (encodedWordLie k word : Ambient k) = encodedWord k word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp [encodedWordLie, encodedWord, appendShiftLie_coe, ih, yLie, zLie]

theorem appendShiftLie_mem_lieGrowthBall
    {a : ExampleLie k} {n : ℕ}
    (ha : a ∈ lieGrowthBall k (exampleGenerators k) n) (r : ℕ) :
    appendShiftLie k r a ∈
      lieGrowthBall k (exampleGenerators k) (n + r) := by
  induction r with
  | zero => simpa [appendShiftLie] using ha
  | succ r ih =>
      rw [appendShiftLie]
      have h := exampleLie_bracket_right_mem_succ k ih
        (tLie_mem_exampleGenerators k)
      simpa [Nat.add_assoc] using h

theorem encodedWordLie_mem_lieGrowthBall (word : List ℕ) :
    encodedWordLie k word ∈
      lieGrowthBall k (exampleGenerators k) (encodedRadius word) := by
  induction word with
  | nil =>
      change xLie k ∈ exampleGenerators k
      exact xLie_mem_exampleGenerators k
  | cons i word ih =>
      rw [encodedWordLie, encodedRadius]
      have hs := appendShiftLie_mem_lieGrowthBall k ih i
      have hy := exampleLie_bracket_right_mem_succ k hs
        (yLie_mem_exampleGenerators k)
      have hz := exampleLie_bracket_right_mem_succ k hy
        (zLie_mem_exampleGenerators k)
      simpa [Nat.add_assoc] using hz

theorem encodedWordLie_mem_lieGrowthBall_twice (word : List ℕ) :
    encodedWordLie k word ∈
      lieGrowthBall k (exampleGenerators k) (2 * profileCost word) :=
  exampleLie_lieGrowthBall_mono k (encodedRadius_le_twice_profileCost word)
    (encodedWordLie_mem_lieGrowthBall k word)

theorem lieGrowthBall_le_succ (n : ℕ) :
    lieGrowthBall k (generators k) n ≤
      lieGrowthBall k (generators k) (n + 1) := by
  rw [lieGrowthBall_succ, lieExpansion]
  exact le_sup_left

theorem lieGrowthBall_mono {m n : ℕ} (hmn : m ≤ n) :
    lieGrowthBall k (generators k) m ≤
      lieGrowthBall k (generators k) n := by
  induction hmn with
  | refl => exact le_rfl
  | @step n hmn ih => exact ih.trans (lieGrowthBall_le_succ k n)

theorem bracket_right_mem_lieGrowthBall_succ
    {a b : Ambient k} {n : ℕ}
    (ha : a ∈ lieGrowthBall k (generators k) n)
    (hb : b ∈ generators k) :
    ⁅a, b⁆ ∈ lieGrowthBall k (generators k) (n + 1) := by
  rw [lieGrowthBall_succ, lieExpansion]
  apply (le_sup_right : lieActionSubspace (generators k)
    (lieGrowthBall k (generators k) n) ≤ _)
  rw [lieActionSubspace_eq_map₂]
  have hleft : ⁅b, a⁆ ∈
      Submodule.map₂
        (lieActionBilinear (k := k) (L := Ambient k) (M := Ambient k))
        (generators k) (lieGrowthBall k (generators k) n) := by
    exact Submodule.apply_mem_map₂ _ hb ha
  simpa only [lie_skew] using neg_mem hleft

theorem bracket_elementary_t (r : ProfileEnd k) :
    ⁅elementary k 0 1 r, t k⁆ = elementary k 0 1 (r * shift k) := by
  change Matrix.single 0 1 r * Matrix.single 1 1 (shift k) -
      Matrix.single 1 1 (shift k) * Matrix.single 0 1 r =
    Matrix.single 0 1 (r * shift k)
  have hzero : (Matrix.single 1 1 (shift k) : Ambient k) *
      Matrix.single 0 1 r = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _
      (by decide : (1 : Fin 3) ≠ 0) _
  rw [Matrix.single_mul_single_same, hzero]
  simp

theorem bracket_bracket_elementary_y_z (r : ProfileEnd k) :
    ⁅⁅elementary k 0 1 r, y k⁆, z k⁆ =
      elementary k 0 1 (r * store k) := by
  have h₁ : ⁅elementary k 0 1 r, y k⁆ =
      elementary k 0 2 (r * store k) := by
    change Matrix.single 0 1 r * Matrix.single 1 2 (store k) -
        Matrix.single 1 2 (store k) * Matrix.single 0 1 r =
      (Matrix.single 0 2 (r * store k) : Ambient k)
    have hzero : (Matrix.single 1 2 (store k) : Ambient k) *
        Matrix.single 0 1 r = 0 :=
      Matrix.single_mul_single_of_ne _ _ _ _
        (by decide : (2 : Fin 3) ≠ 0) _
    rw [Matrix.single_mul_single_same, hzero]
    simp
  rw [h₁]
  change (Matrix.single 0 2 (r * store k) : Ambient k) *
        Matrix.single 2 1 (store k) -
      Matrix.single 2 1 (store k) *
        Matrix.single 0 2 (r * store k) =
      Matrix.single 0 1 (r * store k)
  have hzero : (Matrix.single 2 1 (store k) : Ambient k) *
      Matrix.single 0 2 (r * store k) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _
      (by decide : (1 : Fin 3) ≠ 0) _
  rw [Matrix.single_mul_single_same, hzero]
  simp [mul_assoc, store_mul_store]

theorem appendShift_elementary (n : ℕ) (r : ProfileEnd k) :
    appendShift k n (elementary k 0 1 r) =
      elementary k 0 1 (r * (shift k) ^ n) := by
  induction n with
  | zero => simp [appendShift]
  | succ n ih =>
      rw [appendShift, ih, bracket_elementary_t, pow_succ]
      simp [mul_assoc]

theorem encodedWord_eq (word : List ℕ) :
    encodedWord k word =
      elementary k 0 1 (readWord k word.reverse) := by
  induction word with
  | nil => simp [encodedWord, x, elementary, readWord]
  | cons i word ih =>
      rw [encodedWord, ih, appendShift_elementary,
        bracket_bracket_elementary_y_z]
      rw [List.reverse_cons, readWord_append_single]

theorem appendShift_mem_lieGrowthBall
    {a : Ambient k} {n : ℕ}
    (ha : a ∈ lieGrowthBall k (generators k) n) (r : ℕ) :
    appendShift k r a ∈ lieGrowthBall k (generators k) (n + r) := by
  induction r with
  | zero => simpa [appendShift] using ha
  | succ r ih =>
      rw [appendShift]
      have h := bracket_right_mem_lieGrowthBall_succ k ih
        (t_mem_generators k)
      simpa [Nat.add_assoc] using h

theorem encodedWord_mem_lieGrowthBall (word : List ℕ) :
    encodedWord k word ∈
      lieGrowthBall k (generators k) (encodedRadius word) := by
  induction word with
  | nil =>
      change x k ∈ generators k
      exact x_mem_generators k
  | cons i word ih =>
      rw [encodedWord, encodedRadius]
      have hs := appendShift_mem_lieGrowthBall k ih i
      have hy := bracket_right_mem_lieGrowthBall_succ k hs
        (y_mem_generators k)
      have hz := bracket_right_mem_lieGrowthBall_succ k hy
        (z_mem_generators k)
      simpa [Nat.add_assoc] using hz

theorem encodedWord_mem_lieGrowthBall_twice (word : List ℕ) :
    encodedWord k word ∈
      lieGrowthBall k (generators k) (2 * profileCost word) :=
  lieGrowthBall_mono k (encodedRadius_le_twice_profileCost word)
    (encodedWord_mem_lieGrowthBall k word)

/-- Read the `(0,1)` matrix entry at the zeroth free-module basis vector and
then take its zeroth coefficient. -/
def readCoefficient : Ambient k →ₗ[k] Limit k where
  toFun A := (A 0 1 (basisVector k 0)) 0
  map_add' A B := by simp
  map_smul' r A := by simp

theorem readCoefficient_encodedWord (word : List ℕ) :
    readCoefficient k (encodedWord k word) = profileProduct k word := by
  rw [encodedWord_eq, readCoefficient]
  change (readWord k word.reverse (basisVector k 0)) 0 = _
  rw [readWord_basisVector_zero]
  simp

/-- Span of encoded Lie words with weighted profile cost at most `n`. -/
def encodedSpace (n : ℕ) : Submodule k (Ambient k) :=
  Submodule.span k
    {a | ∃ word : List ℕ,
      profileCost word ≤ n ∧ encodedWord k word = a}

instance moduleFinite_encodedSpace (n : ℕ) :
    Module.Finite k (encodedSpace k n) := by
  apply Module.Finite.span_of_finite k
  apply (finite_profileCost_le n).image (encodedWord k) |>.subset
  rintro a ⟨word, hword, rfl⟩
  exact ⟨word, hword, rfl⟩

theorem map_readCoefficient_encodedSpace (n : ℕ) :
    Submodule.map (readCoefficient k) (encodedSpace k n) =
      profileSpace k n := by
  rw [encodedSpace, profileSpace, Submodule.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨word, hword, rfl⟩, rfl⟩
    exact ⟨word, hword, (readCoefficient_encodedWord k word).symm⟩
  · rintro ⟨word, hword, rfl⟩
    exact ⟨encodedWord k word, ⟨word, hword, rfl⟩,
      readCoefficient_encodedWord k word⟩

theorem encodedSpace_le_lieGrowthBall (n : ℕ) :
    encodedSpace k n ≤ lieGrowthBall k (generators k) (2 * n) := by
  apply Submodule.span_le.2
  rintro _ ⟨word, hword, rfl⟩
  exact lieGrowthBall_mono k (Nat.mul_le_mul_left 2 hword)
    (encodedWord_mem_lieGrowthBall_twice k word)

instance moduleFinite_lieGrowthBall (n : ℕ) :
    Module.Finite k (lieGrowthBall k (generators k) n) := by
  induction n with
  | zero =>
      change Module.Finite k (generators k)
      exact moduleFinite_generators k
  | succ n ih =>
      rw [lieGrowthBall_succ, lieExpansion]
      let _ : Module.Finite k (generators k) := moduleFinite_generators k
      let _ : Module.Finite k (lieGrowthBall k (generators k) n) := ih
      have haction : Module.Finite k
          (lieActionSubspace (generators k)
            (lieGrowthBall k (generators k) n)) := by
        rw [lieActionSubspace]
        exact Module.Finite.range _
      exact Module.Finite.of_fg
        (((Submodule.fg_top (lieGrowthBall k (generators k) n)).mp
            Module.Finite.fg_top).sup
          ((Submodule.fg_top
            (lieActionSubspace (generators k)
              (lieGrowthBall k (generators k) n))).mp
            (let _ := haction; Module.Finite.fg_top)))

/-- The Lie ball of radius `2n` has dimension at least the weighted profile
space of radius `n`. -/
theorem finrank_profileSpace_le_lieGrowthBall (n : ℕ) :
    Module.finrank k (profileSpace k n) ≤
      Module.finrank k (lieGrowthBall k (generators k) (2 * n)) := by
  let f := (readCoefficient k).domRestrict (encodedSpace k n)
  have hrange : f.range = profileSpace k n := by
    dsimp [f]
    rw [LinearMap.range_domRestrict, map_readCoefficient_encodedSpace]
  have hmap : Module.finrank k (profileSpace k n) ≤
      Module.finrank k (encodedSpace k n) := by
    rw [← hrange]
    exact LinearMap.finrank_range_le f
  exact hmap.trans (Submodule.finrank_mono (encodedSpace_le_lieGrowthBall k n))

/-- Coefficient reader restricted to the generated Lie algebra. -/
def readCoefficientLie : ExampleLie k →ₗ[k] Limit k :=
  (readCoefficient k).comp (ExampleLie k).toSubmodule.subtype

theorem readCoefficientLie_encodedWord (word : List ℕ) :
    readCoefficientLie k (encodedWordLie k word) = profileProduct k word := by
  change readCoefficient k ((encodedWordLie k word : ExampleLie k) : Ambient k) = _
  rw [encodedWordLie_coe, readCoefficient_encodedWord]

def exampleEncodedSpace (n : ℕ) : Submodule k (ExampleLie k) :=
  Submodule.span k
    {a | ∃ word : List ℕ,
      profileCost word ≤ n ∧ encodedWordLie k word = a}

instance moduleFinite_exampleEncodedSpace (n : ℕ) :
    Module.Finite k (exampleEncodedSpace k n) := by
  apply Module.Finite.span_of_finite k
  apply (finite_profileCost_le n).image (encodedWordLie k) |>.subset
  rintro a ⟨word, hword, rfl⟩
  exact ⟨word, hword, rfl⟩

theorem map_readCoefficientLie_exampleEncodedSpace (n : ℕ) :
    Submodule.map (readCoefficientLie k) (exampleEncodedSpace k n) =
      profileSpace k n := by
  rw [exampleEncodedSpace, profileSpace, Submodule.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨word, hword, rfl⟩, rfl⟩
    exact ⟨word, hword, (readCoefficientLie_encodedWord k word).symm⟩
  · rintro ⟨word, hword, rfl⟩
    exact ⟨encodedWordLie k word, ⟨word, hword, rfl⟩,
      readCoefficientLie_encodedWord k word⟩

theorem exampleEncodedSpace_le_lieGrowthBall (n : ℕ) :
    exampleEncodedSpace k n ≤
      lieGrowthBall k (exampleGenerators k) (2 * n) := by
  apply Submodule.span_le.2
  rintro _ ⟨word, hword, rfl⟩
  exact exampleLie_lieGrowthBall_mono k (Nat.mul_le_mul_left 2 hword)
    (encodedWordLie_mem_lieGrowthBall_twice k word)

instance moduleFinite_exampleLie_lieGrowthBall (n : ℕ) :
    Module.Finite k (lieGrowthBall k (exampleGenerators k) n) := by
  induction n with
  | zero =>
      change Module.Finite k (exampleGenerators k)
      exact moduleFinite_exampleGenerators k
  | succ n ih =>
      rw [lieGrowthBall_succ, lieExpansion]
      let _ : Module.Finite k (exampleGenerators k) :=
        moduleFinite_exampleGenerators k
      let _ : Module.Finite k (lieGrowthBall k (exampleGenerators k) n) := ih
      have haction : Module.Finite k
          (lieActionSubspace (exampleGenerators k)
            (lieGrowthBall k (exampleGenerators k) n)) := by
        rw [lieActionSubspace]
        exact Module.Finite.range _
      exact Module.Finite.of_fg
        (((Submodule.fg_top (lieGrowthBall k (exampleGenerators k) n)).mp
            Module.Finite.fg_top).sup
          ((Submodule.fg_top
            (lieActionSubspace (exampleGenerators k)
              (lieGrowthBall k (exampleGenerators k) n))).mp
            (let _ := haction; Module.Finite.fg_top)))

theorem finrank_profileSpace_le_exampleLieGrowthBall (n : ℕ) :
    Module.finrank k (profileSpace k n) ≤
      Module.finrank k (lieGrowthBall k (exampleGenerators k) (2 * n)) := by
  let f := (readCoefficientLie k).domRestrict (exampleEncodedSpace k n)
  have hrange : f.range = profileSpace k n := by
    dsimp [f]
    rw [LinearMap.range_domRestrict,
      map_readCoefficientLie_exampleEncodedSpace]
  have hmap : Module.finrank k (profileSpace k n) ≤
      Module.finrank k (exampleEncodedSpace k n) := by
    rw [← hrange]
    exact LinearMap.finrank_range_le f
  exact hmap.trans
    (Submodule.finrank_mono (exampleEncodedSpace_le_lieGrowthBall k n))

/-- The generated Lie algebra has exponential growth. -/
theorem exampleLie_hasExponentialGrowth :
    HasExponentialLieGrowth k (ExampleLie k) := by
  refine ⟨exampleGenerators k, moduleFinite_exampleGenerators k,
    exampleLie_lieSpan_eq_top k, (101 : ℚ) / 100, by norm_num, 10, ?_⟩
  intro N hN
  have hhalf : 5 ≤ N / 2 := by omega
  obtain ⟨r, hr, hrnext⟩ := exists_profileRadius_interval hhalf
  have hnext := profileRadius_succ_lt_twenty_mul_two_pow r
  have hNpow : N ≤ 40 * 2 ^ r := by omega
  have hradius : 2 * profileRadius r ≤ N := by omega
  have hq40 : (((101 : ℚ) / 100) ^ 40) ≤ 4 := by norm_num
  have hq : ((101 : ℚ) / 100) ^ N ≤ (4 : ℚ) ^ (2 ^ r) := by
    calc
      ((101 : ℚ) / 100) ^ N ≤
          ((101 : ℚ) / 100) ^ (40 * 2 ^ r) :=
        pow_le_pow_right₀ (by norm_num) hNpow
      _ = (((101 : ℚ) / 100) ^ 40) ^ (2 ^ r) := by
        rw [pow_mul]
      _ ≤ (4 : ℚ) ^ (2 ^ r) := pow_le_pow_left₀ (by positivity) hq40 _
  have hstage := four_pow_two_pow_le_finrank_profileSpace k r
  have hprofile := finrank_profileSpace_le_exampleLieGrowthBall k
    (profileRadius r)
  have hmono : lieGrowthBall k (exampleGenerators k) (2 * profileRadius r) ≤
      lieGrowthBall k (exampleGenerators k) N :=
    exampleLie_lieGrowthBall_mono k hradius
  let _ : Module.Finite k (lieGrowthBall k (exampleGenerators k) N) :=
    moduleFinite_exampleLie_lieGrowthBall k N
  have hdimMono := Submodule.finrank_mono hmono
  have hdim : 4 ^ (2 ^ r) ≤
      Module.finrank k (lieGrowthBall k (exampleGenerators k) N) :=
    hstage.trans (hprofile.trans hdimMono)
  exact hq.trans (by exact_mod_cast hdim)

/-! ## The locally finite kernel -/

/-- Matrices all of whose entries belong to the profile ideal. -/
def matrixProfileIdeal : Submodule k (Ambient k) where
  carrier A := ∀ i j, A i j ∈ profileIdeal k
  zero_mem' i j := by simp
  add_mem' {A B} hA hB i j := by
    exact (profileIdeal k).add_mem (hA i j) (hB i j)
  smul_mem' r A hA i j := by
    exact (profileIdeal k).smul_mem r (hA i j)

theorem elementary_mem_matrixProfileIdeal {i j : Fin 3}
    {r : ProfileEnd k} (hr : r ∈ profileIdeal k) :
    elementary k i j r ∈ matrixProfileIdeal k := by
  intro p q
  by_cases h : i = p ∧ j = q
  · simp [elementary, Matrix.single, h, hr]
  · simp [elementary, Matrix.single, h]

theorem x_mem_matrixProfileIdeal : x k ∈ matrixProfileIdeal k :=
  elementary_mem_matrixProfileIdeal k (store_mem_profileIdeal k)

theorem y_mem_matrixProfileIdeal : y k ∈ matrixProfileIdeal k :=
  elementary_mem_matrixProfileIdeal k (store_mem_profileIdeal k)

theorem z_mem_matrixProfileIdeal : z k ∈ matrixProfileIdeal k :=
  elementary_mem_matrixProfileIdeal k (store_mem_profileIdeal k)

theorem sub_mem_profileIdeal {u v : ProfileEnd k}
    (hu : u ∈ profileIdeal k) (hv : v ∈ profileIdeal k) :
    u - v ∈ profileIdeal k := by
  have hneg : -v ∈ profileIdeal k := by
    exact Submodule.neg_mem (R := k) (M := ProfileEnd k)
      (profileIdeal k) hv
  have hadd : u + -v ∈ profileIdeal k :=
    (profileIdeal k).add_mem hu hneg
  have huv : u - v = u + -v := sub_eq_add_neg u v
  rw [huv]
  exact hadd

/-- Matrices over the profile ideal are closed under multiplication. -/
theorem mul_mem_matrixProfileIdeal {A B : Ambient k}
    (hA : A ∈ matrixProfileIdeal k) (hB : B ∈ matrixProfileIdeal k) :
    A * B ∈ matrixProfileIdeal k := by
  intro i j
  change (∑ l, A i l * B l j) ∈ profileIdeal k
  exact Submodule.sum_mem (profileIdeal k)
    (fun l _ => mul_mem_profileIdeal k (hA i l) (hB l j))

/-- Matrices over the profile ideal are closed under the commutator. -/
theorem bracket_mem_matrixProfileIdeal {A B : Ambient k}
    (hA : A ∈ matrixProfileIdeal k) (hB : B ∈ matrixProfileIdeal k) :
    ⁅A, B⁆ ∈ matrixProfileIdeal k := by
  intro i j
  change (A * B - B * A) i j ∈ profileIdeal k
  exact sub_mem_profileIdeal k
    (mul_mem_matrixProfileIdeal k hA hB i j)
    (mul_mem_matrixProfileIdeal k hB hA i j)

theorem bracket_t_mem_matrixProfileIdeal {A : Ambient k}
    (hA : A ∈ matrixProfileIdeal k) :
    ⁅t k, A⁆ ∈ matrixProfileIdeal k := by
  have hzero : (0 : ProfileEnd k) ∈ profileIdeal k :=
    (profileIdeal k).zero_mem
  intro i j
  change (((Matrix.single 1 1 (shift k) : Ambient k) * A -
    A * (Matrix.single 1 1 (shift k) : Ambient k)) i j) ∈ profileIdeal k
  rw [Matrix.sub_apply]
  by_cases hi : i = 1
  · subst i
    by_cases hj : j = 1
    · subst j
      rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same]
      exact sub_mem_profileIdeal k
        (by simpa only [pow_one] using
          shift_pow_mul_mem_profileIdeal k 1 (hA 1 1))
        (by simpa only [pow_one] using
          mul_shift_pow_mem_profileIdeal k 1 (hA 1 1))
    · rw [Matrix.single_mul_apply_same,
        Matrix.mul_single_apply_of_ne (shift k) 1 1 1 j hj A]
      exact sub_mem_profileIdeal k
        (by simpa only [pow_one] using
          shift_pow_mul_mem_profileIdeal k 1 (hA 1 j)) hzero
  · by_cases hj : j = 1
    · subst j
      rw [Matrix.single_mul_apply_of_ne (shift k) 1 1 i 1 hi A,
        Matrix.mul_single_apply_same]
      exact sub_mem_profileIdeal k hzero
        (by simpa only [pow_one] using
          mul_shift_pow_mem_profileIdeal k 1 (hA i 1))
    · rw [Matrix.single_mul_apply_of_ne (shift k) 1 1 i j hi A,
        Matrix.mul_single_apply_of_ne (shift k) 1 1 i j hj A]
      exact sub_mem_profileIdeal k hzero hzero

set_option maxHeartbeats 800000 in
-- Lie-span induction over the nested matrix endomorphism type requires
-- deeper normalization of its induced Lie-module instances.
/-- Every element of the generated Lie algebra is a scalar multiple of `t`
modulo the profile ideal. -/
theorem exists_eq_smul_t_add_matrixProfileIdeal {A : Ambient k}
    (hA : A ∈ ExampleLie k) :
    ∃ r : k, ∃ I : Ambient k,
      I ∈ matrixProfileIdeal k ∧ A = r • t k + I := by
  induction hA using LieSubalgebra.lieSpan_induction with
  | mem A hA =>
      simp only [generatorSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨1, 0, (matrixProfileIdeal k).zero_mem, by simp⟩
      · exact ⟨0, x k, x_mem_matrixProfileIdeal k, by simp⟩
      · exact ⟨0, y k, y_mem_matrixProfileIdeal k, by simp⟩
      · exact ⟨0, z k, z_mem_matrixProfileIdeal k, by simp⟩
  | zero => exact ⟨0, 0, (matrixProfileIdeal k).zero_mem, by simp⟩
  | add A B _ _ hA hB =>
      obtain ⟨r, I, hI, hrI⟩ := hA
      obtain ⟨s, J, hJ, hsJ⟩ := hB
      refine ⟨r + s, I + J, (matrixProfileIdeal k).add_mem hI hJ, ?_⟩
      rw [hrI, hsJ]
      module
  | smul r A _ hA =>
      obtain ⟨s, I, hI, hsI⟩ := hA
      refine ⟨r * s, r • I, (matrixProfileIdeal k).smul_mem r hI, ?_⟩
      rw [hsI]
      module
  | lie A B _ _ hA hB =>
      obtain ⟨r, I, hI, hrI⟩ := hA
      obtain ⟨s, J, hJ, hsJ⟩ := hB
      have htJ : ⁅t k, J⁆ ∈ matrixProfileIdeal k :=
        bracket_t_mem_matrixProfileIdeal k hJ
      have hIt : ⁅I, t k⁆ ∈ matrixProfileIdeal k := by
        rw [← lie_skew I (t k)]
        exact Submodule.neg_mem (R := k) (M := Ambient k)
          (matrixProfileIdeal k) (bracket_t_mem_matrixProfileIdeal k hI)
      have hIJ : ⁅I, J⁆ ∈ matrixProfileIdeal k :=
        bracket_mem_matrixProfileIdeal k hI hJ
      let K : Ambient k := r • ⁅t k, J⁆ + s • ⁅I, t k⁆ + ⁅I, J⁆
      have hK : K ∈ matrixProfileIdeal k := by
        exact (matrixProfileIdeal k).add_mem
          ((matrixProfileIdeal k).add_mem
            ((matrixProfileIdeal k).smul_mem r htJ)
            ((matrixProfileIdeal k).smul_mem s hIt)) hIJ
      refine ⟨0, K, hK, ?_⟩
      rw [hrI, hsJ]
      simp only [lie_add, add_lie, lie_smul, smul_lie, lie_self,
        smul_zero, zero_add]
      module

/-- The profile ideal is stable under bracketing on the left by every
element of the generated Lie algebra. -/
theorem bracket_exampleLie_mem_matrixProfileIdeal (A : ExampleLie k)
    {B : Ambient k} (hB : B ∈ matrixProfileIdeal k) :
    ⁅(A : Ambient k), B⁆ ∈ matrixProfileIdeal k := by
  obtain ⟨r, I, hI, hA⟩ :=
    exists_eq_smul_t_add_matrixProfileIdeal k A.property
  rw [hA, add_lie, smul_lie]
  exact (matrixProfileIdeal k).add_mem
    ((matrixProfileIdeal k).smul_mem r
      (bracket_t_mem_matrixProfileIdeal k hB))
    (bracket_mem_matrixProfileIdeal k hI hB)

/-- The locally finite ideal in the example Lie algebra. -/
def exampleKernel : LieIdeal k (ExampleLie k) where
  carrier A := (A : Ambient k) ∈ matrixProfileIdeal k
  zero_mem' := (matrixProfileIdeal k).zero_mem
  add_mem' hA hB := (matrixProfileIdeal k).add_mem hA hB
  smul_mem' r _ hA := (matrixProfileIdeal k).smul_mem r hA
  lie_mem {A} {B} hB := by
    change ⁅(A : Ambient k), (B : Ambient k)⁆ ∈ matrixProfileIdeal k
    exact bracket_exampleLie_mem_matrixProfileIdeal k A hB

@[simp]
theorem mem_exampleKernel_iff (A : ExampleLie k) :
    A ∈ exampleKernel k ↔ (A : Ambient k) ∈ matrixProfileIdeal k :=
  by rfl

theorem xLie_mem_exampleKernel : xLie k ∈ exampleKernel k :=
  by
    change x k ∈ matrixProfileIdeal k
    exact x_mem_matrixProfileIdeal k

theorem yLie_mem_exampleKernel : yLie k ∈ exampleKernel k :=
  by
    change y k ∈ matrixProfileIdeal k
    exact y_mem_matrixProfileIdeal k

theorem zLie_mem_exampleKernel : zLie k ∈ exampleKernel k :=
  by
    change z k ∈ matrixProfileIdeal k
    exact z_mem_matrixProfileIdeal k

theorem tLie_not_mem_exampleKernel : tLie k ∉ exampleKernel k := by
  intro ht
  change t k ∈ matrixProfileIdeal k at ht
  have hentry := ht (1 : Fin 3) (1 : Fin 3)
  change shift k ∈ profileIdeal k at hentry
  exact shift_not_mem_profileIdeal k hentry

/-- Every class in the quotient by the profile kernel is a scalar multiple
of the class of `t`. -/
theorem quotient_eq_smul_t (A : ExampleLie k) :
    ∃ r : k, LieIdeal.quotientMkLieHom (exampleKernel k) A =
      r • LieIdeal.quotientMkLieHom (exampleKernel k) (tLie k) := by
  obtain ⟨r, I, hI, hA⟩ :=
    exists_eq_smul_t_add_matrixProfileIdeal k A.property
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq (exampleKernel k).toSubmodule).mpr
  change (A : Ambient k) - r • t k ∈ matrixProfileIdeal k
  rw [hA]
  simpa only [add_sub_cancel_left] using hI

/-- The quotient by the profile kernel is linearly equivalent to the ground
field, with `1` corresponding to the class of `t`. -/
noncomputable def quotientLinearEquiv :
    k ≃ₗ[k] (ExampleLie k ⧸ exampleKernel k) := by
  let qt : ExampleLie k ⧸ exampleKernel k :=
    LieIdeal.quotientMkLieHom (exampleKernel k) (tLie k)
  let f : k →ₗ[k] (ExampleLie k ⧸ exampleKernel k) :=
    LinearMap.smulRight LinearMap.id qt
  have hqt : qt ≠ 0 := by
    intro hzero
    have hmem : tLie k ∈ exampleKernel k :=
      (Submodule.Quotient.mk_eq_zero (exampleKernel k).toSubmodule).mp hzero
    exact tLie_not_mem_exampleKernel k hmem
  apply LinearEquiv.ofBijective f
  constructor
  · intro r s hrs
    apply smul_left_injective k hqt
    simpa [f, qt] using hrs
  · intro q
    obtain ⟨A, rfl⟩ := LieIdeal.quotientMkLieHom_surjective
      (exampleKernel k) q
    obtain ⟨r, hr⟩ := quotient_eq_smul_t k A
    exact ⟨r, by simpa [f, qt] using hr.symm⟩

theorem quotient_finrank_eq_one :
    Module.finrank k (ExampleLie k ⧸ exampleKernel k) = 1 := by
  rw [← (quotientLinearEquiv k).finrank_eq]
  simp

/-! ### Local finite-dimensionality of the kernel -/

/-- Evaluation of an element of the kernel at one matrix entry. -/
def kernelEntry (i j : Fin 3) : exampleKernel k →ₗ[k] ProfileEnd k where
  toFun A := ((A : ExampleLie k) : Ambient k) i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Sum all nine entries chosen from elements of `P`. -/
def kernelEntriesSum (P : Submodule k (exampleKernel k)) :
    ((Fin 3 × Fin 3) →₀ P) →ₗ[k] ProfileEnd k :=
  Finsupp.lsum k fun ij => (kernelEntry k ij.1 ij.2).comp P.subtype

/-- The subspace spanned by all entries of matrices in `P`. -/
def kernelEntrySpace (P : Submodule k (exampleKernel k)) :
    Submodule k (ProfileEnd k) :=
  LinearMap.range (kernelEntriesSum k P)

instance moduleFinite_kernelEntrySpace
    (P : Submodule k (exampleKernel k)) [Module.Finite k P] :
    Module.Finite k (kernelEntrySpace k P) := by
  let : Module.Finite k ((Fin 3 × Fin 3) →₀ P) :=
    Module.Finite.finsupp
  rw [kernelEntrySpace, LinearMap.range_eq_map]
  exact Module.Finite.map (⊤ : Submodule k ((Fin 3 × Fin 3) →₀ P))
    (kernelEntriesSum k P)

theorem kernelEntrySpace_le_profileIdeal
    (P : Submodule k (exampleKernel k)) :
    kernelEntrySpace k P ≤ profileIdeal k := by
  rintro _ ⟨f, rfl⟩
  induction f using Finsupp.induction with
  | zero => simp
  | single_add ij A f _hij _hA hf =>
      rw [map_add]
      change (((Finsupp.lsum k) (fun ij =>
          (kernelEntry k ij.1 ij.2).comp P.subtype))
          (Finsupp.single ij A) + (kernelEntriesSum k P) f) ∈ profileIdeal k
      rw [Finsupp.lsum_single]
      exact (profileIdeal k).add_mem
        ((A : exampleKernel k).property ij.1 ij.2) hf

theorem kernelEntry_mem_kernelEntrySpace
    (P : Submodule k (exampleKernel k)) {A : exampleKernel k}
    (hA : A ∈ P) (i j : Fin 3) :
    kernelEntry k i j A ∈ kernelEntrySpace k P := by
  refine ⟨Finsupp.single (i, j) ⟨A, hA⟩, ?_⟩
  exact Finsupp.lsum_single k
    (fun ij => (kernelEntry k ij.1 ij.2).comp P.subtype) (i, j) ⟨A, hA⟩

theorem sub_mem_profileSubmodule (W : Submodule k (ProfileEnd k))
    {u v : ProfileEnd k} (hu : u ∈ W) (hv : v ∈ W) : u - v ∈ W := by
  have hneg : -v ∈ W := by
    exact Submodule.neg_mem (R := k) (M := ProfileEnd k) W hv
  have hadd : u + -v ∈ W := W.add_mem hu hneg
  have huv : u - v = u + -v := sub_eq_add_neg u v
  rw [huv]
  exact hadd

/-- Matrices in the kernel whose entries lie in a fixed multiplicatively
closed subspace. -/
def boundedKernelLieSubalgebra (W : Submodule k (ProfileEnd k))
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) :
    LieSubalgebra k (exampleKernel k) where
  carrier A := ∀ i j, ((A : ExampleLie k) : Ambient k) i j ∈ W
  zero_mem' i j := W.zero_mem
  add_mem' hA hB i j := W.add_mem (hA i j) (hB i j)
  smul_mem' r _ hA i j := W.smul_mem r (hA i j)
  lie_mem' {A} {B} hA hB := by
    intro i j
    change (∑ l, (((A : exampleKernel k) : ExampleLie k) : Ambient k) i l *
        (((B : exampleKernel k) : ExampleLie k) : Ambient k) l j) -
      (∑ l, (((B : exampleKernel k) : ExampleLie k) : Ambient k) i l *
        (((A : exampleKernel k) : ExampleLie k) : Ambient k) l j) ∈ W
    apply sub_mem_profileSubmodule k W
    · exact Submodule.sum_mem W fun l _ => hmul _ (hA i l) _ (hB l j)
    · exact Submodule.sum_mem W fun l _ => hmul _ (hB i l) _ (hA l j)

/-- Embed a bounded matrix Lie subalgebra into the finite matrix space over
its entry subspace. -/
def boundedKernelMatrixMap (W : Submodule k (ProfileEnd k))
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) :
    boundedKernelLieSubalgebra k W hmul →ₗ[k] Matrix (Fin 3) (Fin 3) W where
  toFun A i j := ⟨(((A : exampleKernel k) : ExampleLie k) : Ambient k) i j,
    A.property i j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem boundedKernelMatrixMap_injective (W : Submodule k (ProfileEnd k))
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) :
    Function.Injective (boundedKernelMatrixMap k W hmul) := by
  intro A B hAB
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact congrArg Subtype.val (congrFun (congrFun hAB i) j)

instance moduleFinite_boundedKernelLieSubalgebra
    (W : Submodule k (ProfileEnd k)) [Module.Finite k W]
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) :
    Module.Finite k (boundedKernelLieSubalgebra k W hmul) := by
  let : AddCommGroup W := @Submodule.addCommGroup k (ProfileEnd k) _ _
    (inferInstance : Module k (ProfileEnd k)) W
  let rowFinite : Module.Finite k (Fin 3 → W) := Module.Finite.pi
  let (i : Fin 3) : Module.Finite k (Fin 3 → W) := rowFinite
  let : Module.Finite k (Matrix (Fin 3) (Fin 3) W) := Module.Finite.pi
  exact Module.Finite.of_injective (boundedKernelMatrixMap k W hmul)
    (boundedKernelMatrixMap_injective k W hmul)

/-- The profile kernel is locally finite-dimensional. -/
theorem exampleKernel_isLocallyFiniteDimensional :
    IsLocallyFiniteDimensionalLieAlgebra k (exampleKernel k) := by
  intro P hP
  let : Module.Finite k P := hP
  obtain ⟨W, hPW, hW, hmul⟩ :=
    exists_finite_mulClosed_of_le_profileIdeal k (kernelEntrySpace k P)
      (kernelEntrySpace_le_profileIdeal k P)
  let : Module.Finite k W := hW
  let S := boundedKernelLieSubalgebra k W hmul
  refine ⟨S, ?_, ?_⟩
  · intro A hA i j
    apply hPW
    exact kernelEntry_mem_kernelEntrySpace k P hA i j
  · exact moduleFinite_boundedKernelLieSubalgebra k W hmul

end

end HopfAmenability.ProfileLieExample
