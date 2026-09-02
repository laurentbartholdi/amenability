/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# The locally matrix profile algebra

This file constructs the direct limit of the tower
`M₂(k) → End(M₂(k)) → End(End(M₂(k))) → ⋯` used in the exponential-growth
example.  We realize each left-regular embedding as a repeated diagonal block
inside a full matrix algebra.
-/

namespace HopfAmenability.LocallyMatrixProfile

noncomputable section

universe u

/-- The matrix size at stage `n`; each successor is the square of the
preceding size. -/
def stageDimension : ℕ → ℕ
  | 0 => 2
  | n + 1 => stageDimension n * stageDimension n

theorem stageDimension_pos (n : ℕ) : 0 < stageDimension n := by
  induction n with
  | zero => norm_num [stageDimension]
  | succ n ih => simpa [stageDimension] using Nat.mul_pos ih ih

/-- The full matrix algebra at stage `n`. -/
abbrev Stage (k : Type u) [Field k] (n : ℕ) :=
  Matrix (Fin (stageDimension n)) (Fin (stageDimension n)) k

/-- The left-regular inclusion of one stage into the next, written as a
constant block-diagonal matrix and reindexed by `Fin m × Fin m ≃ Fin (m*m)`. -/
def step (k : Type u) [Field k] (n : ℕ) :
    Stage k n →ₐ[k] Stage k (n + 1) := by
  let e := finProdFinEquiv
    (m := stageDimension n) (n := stageDimension n)
  refine (Matrix.reindexAlgEquiv k k e).toAlgHom.comp ?_
  refine
    { toFun := fun A =>
        Matrix.blockDiagonal fun _ : Fin (stageDimension n) => A
      map_one' := by
        ext ⟨i, a⟩ ⟨j, b⟩
        by_cases hab : a = b <;> by_cases hij : i = j <;>
          simp [Matrix.blockDiagonal_apply, Matrix.one_apply, hab, hij]
      map_mul' := fun A B => by rw [← Matrix.blockDiagonal_mul]
      map_zero' := by
        ext ⟨i, a⟩ ⟨j, b⟩
        simp [Matrix.blockDiagonal_apply]
      map_add' := fun A B => by
        ext ⟨i, a⟩ ⟨j, b⟩
        by_cases hab : a = b <;> simp [Matrix.blockDiagonal_apply, hab]
      commutes' := fun r => by
        ext ⟨i, a⟩ ⟨j, b⟩
        by_cases hab : a = b <;> by_cases hij : i = j <;>
          simp [Matrix.blockDiagonal_apply, hab, hij,
            Matrix.algebraMap_matrix_apply] }

/-- Every left-regular stage inclusion is injective. -/
theorem step_injective (k : Type u) [Field k] (n : ℕ) :
    Function.Injective (step k n) := by
  intro A B hAB
  let e := finProdFinEquiv
    (m := stageDimension n) (n := stageDimension n)
  have hblock :
      Matrix.blockDiagonal (fun _ : Fin (stageDimension n) => A) =
        Matrix.blockDiagonal (fun _ : Fin (stageDimension n) => B) := by
    apply (Matrix.reindexAlgEquiv k k e).injective
    exact hAB
  have hfun := Matrix.blockDiagonal_injective hblock
  let i : Fin (stageDimension n) := ⟨0, stageDimension_pos n⟩
  exact congrFun hfun i

/-- The iterated transition map between two stages. -/
def stageMap (k : Type u) [Field k] (i j : ℕ) (h : i ≤ j) :
    Stage k i →ₐ[k] Stage k j :=
  Nat.leRecOn h (fun {n} g => (step k n).comp g) (AlgHom.id k _)

@[simp]
theorem stageMap_refl (k : Type u) [Field k] (i : ℕ) :
    stageMap k i i le_rfl = AlgHom.id k _ := by
  unfold stageMap
  rw [Nat.leRecOn_self]

@[simp]
theorem stageMap_succ (k : Type u) [Field k]
    (i j : ℕ) (h : i ≤ j) :
    stageMap k i (j + 1) (Nat.le.step h) =
      (step k j).comp (stageMap k i j h) := by
  simp [stageMap, Nat.leRecOn_succ h]

/-- Transition maps compose as expected. -/
theorem stageMap_comp (k : Type u) [Field k]
    (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    (stageMap k j l hjl).comp (stageMap k i j hij) =
      stageMap k i l (hij.trans hjl) := by
  induction hjl with
  | refl => simp
  | @step l hjl ih =>
      rw [stageMap_succ k j l hjl,
        stageMap_succ k i l (hij.trans hjl)]
      rw [AlgHom.comp_assoc, ih]

/-- All transition maps in the tower are injective. -/
theorem stageMap_injective (k : Type u) [Field k]
    (i j : ℕ) (h : i ≤ j) :
    Function.Injective (stageMap k i j h) := by
  induction h with
  | refl =>
      rw [stageMap_refl]
      exact Function.injective_id
  | @step j h ih =>
      rw [stageMap_succ k i j h]
      exact (step_injective k j).comp ih

instance stageDirectedSystem (k : Type u) [Field k] :
    DirectedSystem (Stage k) (fun {_ _} h => stageMap k _ _ h) where
  map_self := by
    intro i x
    rw [stageMap_refl]
    rfl
  map_map := by
    intro l j i hij hjl x
    exact DFunLike.congr_fun (stageMap_comp k i j l hij hjl) x

/-- The locally matrix algebra obtained from the tower. -/
abbrev Limit (k : Type u) [Field k] :=
  DirectLimit (Stage k) fun _ _ h => stageMap k _ _ h

/-- The canonical algebra map from a finite stage to the limit. -/
def ofStage (k : Type u) [Field k] (n : ℕ) :
    Stage k n →ₐ[k] Limit k :=
  DirectLimit.Algebra.of (Stage k)
    (fun _ _ h => stageMap k _ _ h) n

@[simp]
theorem ofStage_stageMap (k : Type u) [Field k]
    {i j : ℕ} (h : i ≤ j) (x : Stage k i) :
    ofStage k j (stageMap k i j h x) = ofStage k i x :=
  DirectLimit.Algebra.of_f h x

/-- Each finite stage embeds in the direct limit. -/
theorem ofStage_injective (k : Type u) [Field k] (n : ℕ) :
    Function.Injective (ofStage k n) := by
  exact DirectLimit.mk_injective
    (f := fun {_ _} h => stageMap k _ _ h)
    (fun i j h => stageMap_injective k i j h) n

/-- Every element of the limit is represented at a finite stage. -/
theorem exists_ofStage (k : Type u) [Field k] (x : Limit k) :
    ∃ n a, ofStage k n a = x := by
  obtain ⟨n, a, rfl⟩ := DirectLimit.exists_eq_mk
    (f := fun _ _ h => stageMap k _ _ h) x
  exact ⟨n, a, rfl⟩

/-- A finite family of elements of the limit is represented in one common
finite stage. -/
theorem exists_stage_containing_finset (k : Type u) [Field k]
    (s : Finset (Limit k)) :
    ∃ n : ℕ, ∀ x ∈ s, ∃ a : Stage k n, ofStage k n a = x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨i, a, ha⟩ := exists_ofStage k x
      obtain ⟨j, hj⟩ := ih
      let n := max i j
      have hin : i ≤ n := Nat.le_max_left _ _
      have hjn : j ≤ n := Nat.le_max_right _ _
      refine ⟨n, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ⟨stageMap k i n hin a, by
          rw [ofStage_stageMap, ha]⟩
      · obtain ⟨b, hb⟩ := hj y hy
        exact ⟨stageMap k j n hjn b, by
          rw [ofStage_stageMap, hb]⟩

/-- The image of a finite matrix stage as a subalgebra of the direct limit. -/
def stageAlgebra (k : Type u) [Field k] (n : ℕ) : Subalgebra k (Limit k) :=
  Subalgebra.map (ofStage k n) ⊤

instance finiteDimensional_stageAlgebra (k : Type u) [Field k] (n : ℕ) :
    FiniteDimensional k (stageAlgebra k n) := by
  let f : Stage k n →ₗ[k] stageAlgebra k n :=
    (ofStage k n).toLinearMap.codRestrict
      (stageAlgebra k n).toSubmodule fun x => ⟨x, trivial, rfl⟩
  apply FiniteDimensional.of_surjective f
  rintro ⟨x, hx⟩
  obtain ⟨a, _, ha⟩ := hx
  exact ⟨a, Subtype.ext ha⟩

theorem mem_stageAlgebra_of_eq_ofStage (k : Type u) [Field k]
    {n : ℕ} {x : Limit k} {a : Stage k n} (ha : ofStage k n a = x) :
    x ∈ stageAlgebra k n := by
  exact ⟨a, trivial, ha⟩

/-- Every finite set in the locally matrix limit lies in one finite matrix
subalgebra. -/
theorem exists_stageAlgebra_of_finset (k : Type u) [Field k]
    (s : Finset (Limit k)) :
    ∃ n : ℕ, ∀ x ∈ s, x ∈ stageAlgebra k n := by
  obtain ⟨n, hn⟩ := exists_stage_containing_finset k s
  refine ⟨n, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hn x hx
  exact mem_stageAlgebra_of_eq_ofStage k ha

/-! ## Rank-one amplification -/

/-- Before reindexing, the rank-one operator `x ↦ tr(x) · 1` on a matrix
stage. -/
def rankOneProjectorRaw (k : Type u) [Field k] (n : ℕ) :
    Matrix (Fin (stageDimension n) × Fin (stageDimension n))
      (Fin (stageDimension n) × Fin (stageDimension n)) k :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

theorem blockDiagonal_mul_rankOneProjectorRaw_apply
    (k : Type u) [Field k] (n : ℕ) (A : Stage k n)
    (x c s f : Fin (stageDimension n)) :
    (Matrix.blockDiagonal (fun _ : Fin (stageDimension n) => A) *
        rankOneProjectorRaw k n) (x, c) (s, f) =
      if s = f then A x c else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (c, c)]
  · simp [Matrix.blockDiagonal_apply, rankOneProjectorRaw]
  · rintro ⟨r, e⟩ _ hne
    by_cases hce : c = e
    · by_cases hre : r = e
      · subst e
        subst r
        exact (hne rfl).elim
      · simp [Matrix.blockDiagonal_apply, rankOneProjectorRaw, hce, hre]
    · simp [Matrix.blockDiagonal_apply, rankOneProjectorRaw, hce]
  · simp

/-- Multiplying the rank-one projector on both sides by suitable matrix
units produces every matrix unit of the next stage. -/
theorem blockDiagonal_mul_projector_mul_blockDiagonal
    (k : Type u) [Field k] (n : ℕ)
    (i a j b : Fin (stageDimension n)) :
    Matrix.blockDiagonal
        (fun _ : Fin (stageDimension n) => Matrix.single i a 1) *
        rankOneProjectorRaw k n *
        Matrix.blockDiagonal
          (fun _ : Fin (stageDimension n) => Matrix.single b j 1) =
      Matrix.single (i, a) (j, b) 1 := by
  ext ⟨x, c⟩ ⟨y, d⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single (d, d)]
  · simp only [blockDiagonal_mul_rankOneProjectorRaw_apply,
      Matrix.blockDiagonal_apply_eq, Matrix.single, Matrix.of_apply,
      mul_ite, mul_one, mul_zero]
    by_cases hbd : b = d <;> by_cases hjy : j = y <;>
      by_cases hix : i = x <;> by_cases hac : a = c <;> simp_all
  · rintro ⟨s, f⟩ _ hne
    by_cases hfd : f = d
    · by_cases hsf : s = f
      · subst f
        subst s
        exact (hne rfl).elim
      · simp_all [blockDiagonal_mul_rankOneProjectorRaw_apply,
          Matrix.blockDiagonal_apply]
    · simp_all [blockDiagonal_mul_rankOneProjectorRaw_apply,
        Matrix.blockDiagonal_apply]
  · simp

/-- The rank-one projector as an element of the successor stage. -/
def stageProjector (k : Type u) [Field k] (n : ℕ) : Stage k (n + 1) :=
  Matrix.reindexAlgEquiv k k finProdFinEquiv (rankOneProjectorRaw k n)

/-- The reindexed form of the matrix-unit amplification identity. -/
theorem step_single_mul_stageProjector_mul_step_single
    (k : Type u) [Field k] (n : ℕ)
    (i a j b : Fin (stageDimension n)) :
    step k n (Matrix.single i a 1) * stageProjector k n *
        step k n (Matrix.single b j 1) =
      Matrix.reindexAlgEquiv k k finProdFinEquiv
        (Matrix.single (i, a) (j, b) 1) := by
  change Matrix.reindexAlgEquiv k k finProdFinEquiv
      (Matrix.blockDiagonal
          (fun _ : Fin (stageDimension n) => Matrix.single i a 1)) *
      Matrix.reindexAlgEquiv k k finProdFinEquiv
        (rankOneProjectorRaw k n) *
      Matrix.reindexAlgEquiv k k finProdFinEquiv
        (Matrix.blockDiagonal
          (fun _ : Fin (stageDimension n) => Matrix.single b j 1)) = _
  rw [← map_mul, ← map_mul,
    blockDiagonal_mul_projector_mul_blockDiagonal]

/-- Rank-one amplification: `Aₙ pₙ Aₙ` linearly spans `Aₙ₊₁`. -/
theorem span_step_mul_stageProjector_mul_step (k : Type u) [Field k]
    (n : ℕ) :
    Submodule.span k
        (Set.range fun p : Stage k n × Stage k n =>
          step k n p.1 * stageProjector k n * step k n p.2) = ⊤ := by
  apply top_unique
  let b : Module.Basis
      (Fin (stageDimension n * stageDimension n) ×
        Fin (stageDimension n * stageDimension n))
      k (Stage k (n + 1)) :=
    Matrix.stdBasis k
      (Fin (stageDimension n * stageDimension n))
      (Fin (stageDimension n * stageDimension n))
  rw [← Module.Basis.span_eq b]
  apply Submodule.span_mono
  rintro _ ⟨⟨u, v⟩, rfl⟩
  change Matrix.stdBasis k
      (Fin (stageDimension n * stageDimension n))
      (Fin (stageDimension n * stageDimension n)) (u, v) ∈ _
  rw [Matrix.stdBasis_eq_single]
  let ua := finProdFinEquiv.symm u
  let vb := finProdFinEquiv.symm v
  have hunit := step_single_mul_stageProjector_mul_step_single k n
    ua.1 ua.2 vb.1 vb.2
  refine ⟨(Matrix.single ua.1 ua.2 1, Matrix.single vb.2 vb.1 1), ?_⟩
  change step k n (Matrix.single ua.1 ua.2 1) * stageProjector k n *
      step k n (Matrix.single vb.2 vb.1 1) = Matrix.single u v 1
  rw [hunit]
  ext p q
  have hpair (r s : Fin (stageDimension n * stageDimension n))
      (hdiv : r.divNat = s.divNat) (hmod : r.modNat = s.modNat) : r = s := by
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hdiv hmod
  have hu : (u.divNat = p.divNat ∧ u.modNat = p.modNat) ↔ u = p :=
    ⟨fun h => hpair u p h.1 h.2, by rintro rfl; exact ⟨rfl, rfl⟩⟩
  have hv : (v.divNat = q.divNat ∧ v.modNat = q.modNat) ↔ v = q :=
    ⟨fun h => hpair v q h.1 h.2, by rintro rfl; exact ⟨rfl, rfl⟩⟩
  simp [Matrix.reindex, Matrix.single, ua, vb, hu, hv]

/-! ## The weighted profile -/

/-- The profile sequence from the article: `1`, the two off-diagonal matrix
units generating `M₂(k)`, followed by the rank-one projectors. -/
def profileElement (k : Type u) [Field k] : ℕ → Limit k
  | 0 => 1
  | 1 => ofStage k 0
      (Matrix.single ⟨0, by norm_num [stageDimension]⟩
        ⟨1, by norm_num [stageDimension]⟩ 1)
  | 2 => ofStage k 0
      (Matrix.single ⟨1, by norm_num [stageDimension]⟩
        ⟨0, by norm_num [stageDimension]⟩ 1)
  | n + 3 => ofStage k (n + 1) (stageProjector k n)

/-- The weighted cost of a profile word; index `i` has weight `i+1`. -/
def profileCost (word : List ℕ) : ℕ :=
  (word.map Nat.succ).sum

/-- Evaluation of a word in the profile sequence. -/
def profileProduct (k : Type u) [Field k] (word : List ℕ) : Limit k :=
  (word.map (profileElement k)).prod

@[simp]
theorem profileCost_nil : profileCost [] = 0 :=
  rfl

@[simp]
theorem profileCost_cons (i : ℕ) (word : List ℕ) :
    profileCost (i :: word) = (i + 1) + profileCost word := by
  simp [profileCost]

@[simp]
theorem profileCost_append (word₁ word₂ : List ℕ) :
    profileCost (word₁ ++ word₂) =
      profileCost word₁ + profileCost word₂ := by
  simp [profileCost, List.sum_append]

theorem length_le_profileCost (word : List ℕ) :
    word.length ≤ profileCost word := by
  induction word with
  | nil => simp
  | cons i word ih =>
      simp only [List.length_cons, profileCost_cons]
      omega

theorem succ_le_profileCost_of_mem {i : ℕ} {word : List ℕ}
    (hi : i ∈ word) : i + 1 ≤ profileCost word := by
  induction word with
  | nil => simp at hi
  | cons j word ih =>
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [profileCost]
      · have := ih hi
        simp only [profileCost_cons]
        omega

/-- There are only finitely many words of bounded weighted profile cost. -/
theorem finite_profileCost_le (n : ℕ) :
    {word : List ℕ | profileCost word ≤ n}.Finite := by
  let encode : ℕ → Fin (n + 1) := fun i =>
    ⟨min i n, Nat.lt_succ_iff.mpr (min_le_right i n)⟩
  let decode : Fin (n + 1) → ℕ := fun i => i
  apply ((List.finite_length_le (Fin (n + 1)) n).image
    (List.map decode)).subset
  intro word hword
  change profileCost word ≤ n at hword
  refine ⟨word.map encode, ?_, ?_⟩
  · simpa using (length_le_profileCost word).trans hword
  · rw [List.map_map]
    have heq : List.map (decode ∘ encode) word = List.map id word := by
      rw [List.map_inj_left]
      intro i hi
      have hin : i ≤ n := by
        have := succ_le_profileCost_of_mem hi
        omega
      simp [encode, decode, Nat.min_eq_left hin]
    simpa using heq

@[simp]
theorem profileProduct_nil (k : Type u) [Field k] :
    profileProduct k [] = 1 :=
  rfl

@[simp]
theorem profileProduct_append (k : Type u) [Field k]
    (word₁ word₂ : List ℕ) :
    profileProduct k (word₁ ++ word₂) =
      profileProduct k word₁ * profileProduct k word₂ := by
  simp [profileProduct, List.map_append, List.prod_append]

/-- The span of all profile words of weighted cost at most `n`. -/
def profileSpace (k : Type u) [Field k] (n : ℕ) : Submodule k (Limit k) :=
  Submodule.span k
    {x | ∃ word : List ℕ, profileCost word ≤ n ∧ profileProduct k word = x}

theorem finite_profileSpace_generators (k : Type u) [Field k] (n : ℕ) :
    {x | ∃ word : List ℕ,
      profileCost word ≤ n ∧ profileProduct k word = x}.Finite := by
  have h := (finite_profileCost_le n).image (profileProduct k)
  apply h.subset
  rintro x ⟨word, hword, rfl⟩
  exact ⟨word, hword, rfl⟩

instance finiteDimensional_profileSpace (k : Type u) [Field k] (n : ℕ) :
    FiniteDimensional k (profileSpace k n) := by
  rw [profileSpace]
  exact FiniteDimensional.span_of_finite k
    (finite_profileSpace_generators k n)

theorem profileProduct_mem_profileSpace (k : Type u) [Field k]
    {word : List ℕ} {n : ℕ} (hword : profileCost word ≤ n) :
    profileProduct k word ∈ profileSpace k n :=
  Submodule.subset_span ⟨word, hword, rfl⟩

theorem profileSpace_mono (k : Type u) [Field k]
    {m n : ℕ} (hmn : m ≤ n) :
    profileSpace k m ≤ profileSpace k n := by
  apply Submodule.span_mono
  rintro x ⟨word, hword, rfl⟩
  exact ⟨word, hword.trans hmn, rfl⟩

/-- Multiplication adds weighted profile radii. -/
theorem mul_mem_profileSpace (k : Type u) [Field k]
    {m n : ℕ} {x y : Limit k}
    (hx : x ∈ profileSpace k m) (hy : y ∈ profileSpace k n) :
    x * y ∈ profileSpace k (m + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨word₁, hword₁, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨word₂, hword₂, rfl⟩ := hy
          rw [← profileProduct_append]
          apply profileProduct_mem_profileSpace
          rw [profileCost_append]
          omega
      | zero => simp
      | add y z _ _ ihy ihz => simpa [mul_add] using add_mem ihy ihz
      | smul r y _ ih =>
          rw [mul_smul_comm]
          exact (profileSpace k (m + n)).smul_mem r ih
  | zero => simp
  | add x z _ _ ihx ihz => simpa [add_mul] using add_mem ihx ihz
  | smul r x _ ih =>
      rw [smul_mul_assoc]
      exact (profileSpace k (m + n)).smul_mem r ih

/-- The initial matrix stage lies in weighted profile radius five. -/
theorem ofStage_zero_le_profileSpace_five (k : Type u) [Field k] :
    Submodule.map (ofStage k 0).toLinearMap ⊤ ≤ profileSpace k 5 := by
  rw [Submodule.map_top]
  rintro _ ⟨x, rfl⟩
  let Q := (profileSpace k 5).comap (ofStage k 0).toLinearMap
  suffices hQ : Q = ⊤ by
    exact hQ.ge (show x ∈ (⊤ : Submodule k (Stage k 0)) from trivial)
  apply top_unique
  change (⊤ : Submodule k (Stage k 0)) ≤ Q
  let b : Module.Basis (Fin 2 × Fin 2) k (Stage k 0) :=
    Matrix.stdBasis k (Fin 2) (Fin 2)
  rw [← Module.Basis.span_eq b]
  apply Submodule.span_le.2
  rintro _ ⟨⟨i, j⟩, rfl⟩
  change ofStage k 0 (Matrix.stdBasis k (Fin 2) (Fin 2) (i, j)) ∈
    profileSpace k 5
  rw [Matrix.stdBasis_eq_single]
  let i0 : Fin (stageDimension 0) := ⟨0, by norm_num [stageDimension]⟩
  let i1 : Fin (stageDimension 0) := ⟨1, by norm_num [stageDimension]⟩
  fin_cases i <;> fin_cases j
  · have h := profileProduct_mem_profileSpace k
        (word := [1, 2]) (n := 5) (by norm_num [profileCost])
    have hprod :
      ofStage k 0 (Matrix.single i0 i1 1) *
          ofStage k 0 (Matrix.single i1 i0 1) ∈ profileSpace k 5 := by
      simpa [profileProduct, profileElement, i0, i1] using h
    rw [← map_mul] at hprod
    change ofStage k 0 (Matrix.single i0 i0 1) ∈ profileSpace k 5
    simpa [Matrix.single_mul_single_same] using hprod
  · have h := profileProduct_mem_profileSpace k
        (word := [1]) (n := 5) (by norm_num [profileCost])
    change ofStage k 0 (Matrix.single i0 i1 1) ∈ profileSpace k 5
    simpa [profileProduct, profileElement, i0, i1] using h
  · have h := profileProduct_mem_profileSpace k
        (word := [2]) (n := 5) (by norm_num [profileCost])
    change ofStage k 0 (Matrix.single i1 i0 1) ∈ profileSpace k 5
    simpa [profileProduct, profileElement, i0, i1] using h
  · have h := profileProduct_mem_profileSpace k
        (word := [2, 1]) (n := 5) (by norm_num [profileCost])
    have hprod :
      ofStage k 0 (Matrix.single i1 i0 1) *
          ofStage k 0 (Matrix.single i0 i1 1) ∈ profileSpace k 5 := by
      simpa [profileProduct, profileElement, i0, i1] using h
    rw [← map_mul] at hprod
    change ofStage k 0 (Matrix.single i1 i1 1) ∈ profileSpace k 5
    simpa [Matrix.single_mul_single_same] using hprod

/-- A recursive weighted radius containing the whole `n`th matrix stage. -/
def profileRadius : ℕ → ℕ
  | 0 => 5
  | n + 1 => 2 * profileRadius n + (n + 4)

/-- Addition form of the closed profile-radius formula, convenient over the
naturals. -/
theorem profileRadius_add (n : ℕ) :
    profileRadius n + n + 5 = 10 * 2 ^ n := by
  induction n with
  | zero => norm_num [profileRadius]
  | succ n ih =>
      rw [profileRadius, pow_succ]
      calc
        2 * profileRadius n + (n + 4) + (n + 1) + 5 =
            2 * (profileRadius n + n + 5) := by omega
        _ = 2 * (10 * 2 ^ n) := by rw [ih]
        _ = 10 * (2 ^ n * 2) := by ring

/-- Closed form of the recursive profile radius. -/
theorem profileRadius_eq (n : ℕ) :
    profileRadius n = 10 * 2 ^ n - n - 5 := by
  have h := profileRadius_add n
  omega

theorem profileRadius_pos (n : ℕ) : 0 < profileRadius n := by
  induction n with
  | zero => norm_num [profileRadius]
  | succ n ih =>
      rw [profileRadius]
      omega

theorem profileRadius_strictMono : StrictMono profileRadius := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [profileRadius]
  have hpos := profileRadius_pos n
  omega

/-- Every radius at least five lies between two adjacent recursive profile
radii. -/
theorem exists_profileRadius_interval {N : ℕ} (hN : 5 ≤ N) :
    ∃ n : ℕ, profileRadius n ≤ N ∧ N < profileRadius (n + 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
      exact ⟨0, by norm_num [profileRadius]⟩
  | @succ N hN ih =>
      obtain ⟨n, hn, hn'⟩ := ih
      by_cases hnext : N + 1 < profileRadius (n + 1)
      · exact ⟨n, hn.trans (Nat.le_succ N), hnext⟩
      · have heq : N + 1 = profileRadius (n + 1) := by omega
        refine ⟨n + 1, heq.ge, ?_⟩
        rw [heq]
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          profileRadius_strictMono (Nat.lt_succ_self (n + 1))

theorem profileRadius_succ_lt_twenty_mul_two_pow (n : ℕ) :
    profileRadius (n + 1) < 20 * 2 ^ n := by
  have h := profileRadius_add (n + 1)
  rw [pow_succ] at h
  omega

/-- Closed form of the matrix size in the tower. -/
theorem stageDimension_eq (n : ℕ) :
    stageDimension n = 2 ^ (2 ^ n) := by
  induction n with
  | zero => norm_num [stageDimension]
  | succ n ih =>
      rw [stageDimension, ih, pow_succ, pow_mul]
      simp [pow_two]

/-- Every finite matrix stage lies in its corresponding weighted profile
space. -/
theorem ofStage_le_profileSpace (k : Type u) [Field k] (n : ℕ) :
    Submodule.map (ofStage k n).toLinearMap ⊤ ≤
      profileSpace k (profileRadius n) := by
  induction n with
  | zero =>
      exact ofStage_zero_le_profileSpace_five k
  | succ n ih =>
      rw [Submodule.map_top]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span k
          (Set.range fun p : Stage k n × Stage k n =>
            step k n p.1 * stageProjector k n * step k n p.2) := by
        rw [span_step_mul_stageProjector_mul_step]
        trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨⟨a, b⟩, rfl⟩ := hx
          have ha : ofStage k n a ∈ profileSpace k (profileRadius n) :=
            ih ⟨a, trivial, rfl⟩
          have hb : ofStage k n b ∈ profileSpace k (profileRadius n) :=
            ih ⟨b, trivial, rfl⟩
          have hp : ofStage k (n + 1) (stageProjector k n) ∈
              profileSpace k (n + 4) := by
            have h := profileProduct_mem_profileSpace k
              (word := [n + 3]) (n := n + 4) (by simp [profileCost])
            simpa [profileProduct, profileElement] using h
          have ha' : ofStage k (n + 1) (step k n a) ∈
              profileSpace k (profileRadius n) := by
            have hm : stageMap k n (n + 1) (Nat.le_succ n) = step k n := by
              rw [stageMap_succ k n n le_rfl, stageMap_refl]
              rfl
            rw [← hm, ofStage_stageMap k (Nat.le_succ n) a]
            exact ha
          have hb' : ofStage k (n + 1) (step k n b) ∈
              profileSpace k (profileRadius n) := by
            have hm : stageMap k n (n + 1) (Nat.le_succ n) = step k n := by
              rw [stageMap_succ k n n le_rfl, stageMap_refl]
              rfl
            rw [← hm, ofStage_stageMap k (Nat.le_succ n) b]
            exact hb
          have hap := mul_mem_profileSpace k ha' hp
          have hapb := mul_mem_profileSpace k hap hb'
          simpa [profileRadius, two_mul, add_assoc, add_left_comm, add_comm,
            mul_assoc] using hapb
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul r x _ hx => simpa using (profileSpace k (profileRadius (n + 1))).smul_mem r hx

/-- The profile space at the recursive radius contains a full matrix stage,
and hence has at least the matrix stage's dimension. -/
theorem stageDimension_sq_le_finrank_profileSpace
    (k : Type u) [Field k] (n : ℕ) :
    stageDimension n * stageDimension n ≤
      Module.finrank k (profileSpace k (profileRadius n)) := by
  let f : Stage k n →ₗ[k] profileSpace k (profileRadius n) :=
    (ofStage k n).toLinearMap.codRestrict
      (profileSpace k (profileRadius n)) fun x =>
        ofStage_le_profileSpace k n ⟨x, trivial, rfl⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply ofStage_injective k n
    exact congrArg Subtype.val hxy
  have hdim := f.finrank_le_finrank_of_injective hf
  simpa [f, Module.finrank_matrix] using hdim

/-- The lower bound in the closed dimension form used in the exponential
growth estimate. -/
theorem four_pow_two_pow_le_finrank_profileSpace
    (k : Type u) [Field k] (n : ℕ) :
    4 ^ (2 ^ n) ≤ Module.finrank k (profileSpace k (profileRadius n)) := by
  calc
    4 ^ (2 ^ n) = stageDimension n * stageDimension n := by
      rw [stageDimension_eq, ← pow_two,
        show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ _ := stageDimension_sq_le_finrank_profileSpace k n

end

end HopfAmenability.LocallyMatrixProfile
