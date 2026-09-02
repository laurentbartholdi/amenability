/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.UniversalEnvelopingCoalgebra
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.Sum.Order
import Mathlib.RingTheory.AlgebraTower

/-!
# The Poincare-Birkhoff-Witt basis

This file develops the PBW basis for the universal enveloping algebra of a
Lie algebra over a field.  It is independent of the amenability argument and
is organized as reusable universal-enveloping-algebra infrastructure.
-/

open Module

namespace UniversalEnvelopingAlgebra

noncomputable section

universe u v w

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Recovering a basis over an intermediate algebra -/

/-- If a `k`-basis of an algebra `A` multiplied by a family `v` is a
`k`-basis of an `A`-module, then `v` is an `A`-basis.  Relative PBW uses
this with the absolute PBW bases of `U(L)` and `U(Q)`. -/
noncomputable def basisOfTowerFactors
    {A : Type*} [Ring A] [Algebra k A]
    {Q : Type*} [AddCommGroup Q] [Module k Q] [Module A Q]
    [IsScalarTower k A Q]
    {I J : Type*} (a : Basis I k A) (q : Basis (I × J) k Q)
    (v : J → Q) (hq : ∀ i j, q (i, j) = a i • v j) :
    Basis J A Q := by
  let c : Basis J A (J →₀ A) := Finsupp.basisSingleOne
  let d : Basis (I × J) k (J →₀ A) := a.smulTower c
  let e : (J →₀ A) ≃ₗ[k] Q := d.equiv q (Equiv.refl _)
  let lc : (J →₀ A) →ₗ[A] Q := Finsupp.linearCombination A v
  have heq : lc.restrictScalars k = e.toLinearMap := by
    apply d.ext
    intro ij
    rcases ij with ⟨i, j⟩
    change lc (d (i, j)) = e (d (i, j))
    rw [Basis.equiv_apply, hq]
    simp [lc, d, c]
  have hlc : Function.Bijective lc := by
    have hrestricted : Function.Bijective (lc.restrictScalars k) := by
      rw [heq]
      exact e.bijective
    exact hrestricted
  exact c.map (LinearEquiv.ofBijective lc hlc : (J →₀ A) ≃ₗ[A] Q)

@[simp]
theorem basisOfTowerFactors_apply
    {A : Type*} [Ring A] [Algebra k A]
    {Q : Type*} [AddCommGroup Q] [Module k Q] [Module A Q]
    [IsScalarTower k A Q]
    {I J : Type*} (a : Basis I k A) (q : Basis (I × J) k Q)
    (v : J → Q) (hq : ∀ i j, q (i, j) = a i • v j) (j : J) :
    basisOfTowerFactors a q v hq j = v j := by
  rw [basisOfTowerFactors, Basis.map_apply]
  change Finsupp.linearCombination A v (Finsupp.single j 1) = _
  simp

/-! ## Relative PBW infrastructure -/

/-- The algebra map on enveloping algebras induced by a Lie homomorphism.
This local formulation keeps the relative PBW module structure independent
of the amenability development. -/
noncomputable def pbwMap {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : LieHom k L Q) : AlgHom k
      (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) :=
  UniversalEnvelopingAlgebra.lift k
    ((UniversalEnvelopingAlgebra.ι k).comp f)

@[simp]
theorem pbwMap_iota {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : LieHom k L Q) (x : L) :
    pbwMap f (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.ι k (f x) := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply k _ x

/-- Restriction of the regular `U(Q)`-module along the enveloping-algebra
map induced by `f`. -/
@[instance_reducible]
noncomputable def relativeModule {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : LieHom k L Q) :
    Module (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) :=
  Module.compHom _ (pbwMap f).toRingHom

/-- The output type of relative PBW: a basis of `U(Q)` as a left `U(L)`-
module through a Lie homomorphism `f`.  When `f` is injective, relative PBW
constructs such a basis from a basis of a complement of its range. -/
noncomputable def RelativePBWBasis {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : LieHom k L Q)
    (ι : Type*) : Type _ :=
  let _ : Module (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) := relativeModule f
  Basis ι (UniversalEnvelopingAlgebra k L)
    (UniversalEnvelopingAlgebra k Q)

/-- A nondecreasing word in a linearly ordered alphabet. -/
abbrev PBWWord (ι : Type w) [LinearOrder ι] :=
  {word : List ι // word.Pairwise (· ≤ ·)}

/-! ## Ordered words in a basis extension -/

/-- The indices from the left summand of a word in a lexicographic sum. -/
def sumLexLeftIndices {α β : Type*} : List (α ⊕ₗ β) → List α :=
  List.filterMap fun x => match ofLex x with
    | Sum.inl a => some a
    | Sum.inr _ => none

/-- The indices from the right summand of a word in a lexicographic sum. -/
def sumLexRightIndices {α β : Type*} : List (α ⊕ₗ β) → List β :=
  List.filterMap fun x => match ofLex x with
    | Sum.inl _ => none
    | Sum.inr b => some b

/-- An ordered word in a lexicographic sum consists of all its left
indices followed by all its right indices. -/
theorem ordered_sumLex_decomposition {α β : Type*}
    [LinearOrder α] [LinearOrder β] (word : List (α ⊕ₗ β))
    (hword : word.Pairwise (· ≤ ·)) :
    (sumLexLeftIndices word).map
          (fun a => toLex (Sum.inl a : α ⊕ β)) ++
      (sumLexRightIndices word).map
          (fun b => toLex (Sum.inr b : α ⊕ β)) = word := by
  induction word with
  | nil => rfl
  | cons x word ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hword
      have ih' := ih htail
      cases hx : ofLex x with
      | inl a =>
          have hxto : x = toLex (Sum.inl a : α ⊕ β) := by
            rw [← hx]
            exact (toLex.apply_symm_apply x).symm
          simpa [sumLexLeftIndices, sumLexRightIndices, List.filterMap,
            hxto, ofLex_toLex] using congrArg (List.cons x) ih'
      | inr b =>
          have hxto : x = toLex (Sum.inr b : α ⊕ β) := by
            rw [← hx]
            exact (toLex.apply_symm_apply x).symm
          have hleft : sumLexLeftIndices word = [] := by
            change List.filterMap (fun x => match ofLex x with
              | Sum.inl a => some a
              | Sum.inr _ => none) word = []
            rw [List.filterMap_eq_nil_iff]
            intro y hy
            have hxy := hhead y hy
            cases hy' : ofLex y with
            | inl a =>
                have hyto : y = toLex (Sum.inl a : α ⊕ β) := by
                  rw [← hy']
                  exact (toLex.apply_symm_apply y).symm
                rw [hxto, hyto] at hxy
                simp at hxy
            | inr c => simp
          have hright :
              (sumLexRightIndices word).map
                  (fun c => toLex (Sum.inr c : α ⊕ β)) = word := by
            simpa [hleft] using ih'
          have hleftCons :
              sumLexLeftIndices (x :: word) = sumLexLeftIndices word := by
            simp [sumLexLeftIndices, List.filterMap, hxto, ofLex_toLex]
          have hrightCons :
              sumLexRightIndices (x :: word) =
                b :: sumLexRightIndices word := by
            simp [sumLexRightIndices, List.filterMap, hxto, ofLex_toLex]
          rw [hleftCons, hrightCons, hleft, hxto]
          simp only [List.map, List.nil_append]
          exact congrArg
            (List.cons (toLex (Sum.inr b : α ⊕ β))) hright

/-- The left component of an ordered word in a lexicographic sum remains
ordered. -/
theorem sumLexLeftIndices_pairwise {α β : Type*}
    [LinearOrder α] [LinearOrder β] (word : List (α ⊕ₗ β))
    (hword : word.Pairwise (· ≤ ·)) :
    (sumLexLeftIndices word).Pairwise (· ≤ ·) := by
  apply hword.filterMap
  intro x y hxy a hxa b hyb
  cases hx : ofLex x <;> simp [hx] at hxa
  case inl c =>
    subst a
    cases hy : ofLex y <;> simp [hy] at hyb
    case inl d =>
      subst b
      rw [← toLex_ofLex x, ← toLex_ofLex y, hx, hy, Sum.Lex.le_def] at hxy
      change Sum.Lex (fun a b : α => a ≤ b) (fun a b : β => a ≤ b)
        (Sum.inl c) (Sum.inl d) at hxy
      cases hxy with
      | inl h => exact h

/-- The right component of an ordered word in a lexicographic sum remains
ordered. -/
theorem sumLexRightIndices_pairwise {α β : Type*}
    [LinearOrder α] [LinearOrder β] (word : List (α ⊕ₗ β))
    (hword : word.Pairwise (· ≤ ·)) :
    (sumLexRightIndices word).Pairwise (· ≤ ·) := by
  apply hword.filterMap
  intro x y hxy a hxa b hyb
  cases hx : ofLex x <;> simp [hx] at hxa
  case inr c =>
    subst a
    cases hy : ofLex y <;> simp [hy] at hyb
    case inr d =>
      subst b
      rw [← toLex_ofLex x, ← toLex_ofLex y, hx, hy, Sum.Lex.le_def] at hxy
      change Sum.Lex (fun a b : α => a ≤ b) (fun a b : β => a ≤ b)
        (Sum.inr c) (Sum.inr d) at hxy
      cases hxy with
      | inr h => exact h

/-- Concatenate an ordered word in the left index type with an ordered
word in the right index type. -/
def combinePBWWords {α β : Type*} [LinearOrder α] [LinearOrder β]
    (words : PBWWord α × PBWWord β) : PBWWord (α ⊕ₗ β) := by
  refine ⟨words.1.1.map (fun a => toLex (Sum.inl a : α ⊕ β)) ++
    words.2.1.map (fun b => toLex (Sum.inr b : α ⊕ β)), ?_⟩
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact words.1.2.imp fun h => by
      rw [Sum.Lex.le_def]
      exact Sum.Lex.inl h
  · rw [List.pairwise_map]
    exact words.2.2.imp fun h => by
      rw [Sum.Lex.le_def]
      exact Sum.Lex.inr h
  · intro a ha b hb
    rcases List.mem_map.1 ha with ⟨a, ha, rfl⟩
    rcases List.mem_map.1 hb with ⟨b, hb, rfl⟩
    rw [Sum.Lex.le_def]
    exact Sum.Lex.sep a b

/-- Split an ordered word over a basis extension into its subalgebra and
complement words. -/
def splitPBWWord {α β : Type*} [LinearOrder α] [LinearOrder β]
    (word : PBWWord (α ⊕ₗ β)) : PBWWord α × PBWWord β :=
  (⟨sumLexLeftIndices word.1,
      sumLexLeftIndices_pairwise word.1 word.2⟩,
    ⟨sumLexRightIndices word.1,
      sumLexRightIndices_pairwise word.1 word.2⟩)

theorem combinePBWWords_splitPBWWord {α β : Type*}
    [LinearOrder α] [LinearOrder β] (word : PBWWord (α ⊕ₗ β)) :
    combinePBWWords (splitPBWWord word) = word := by
  apply Subtype.ext
  exact ordered_sumLex_decomposition word.1 word.2

theorem splitPBWWord_combinePBWWords {α β : Type*}
    [LinearOrder α] [LinearOrder β] (words : PBWWord α × PBWWord β) :
    splitPBWWord (combinePBWWords words) = words := by
  rcases words with ⟨left, right⟩
  apply Prod.ext
  · apply Subtype.ext
    simp [splitPBWWord, combinePBWWords, sumLexLeftIndices,
      List.filterMap_map, Function.comp_def, ofLex_toLex]
  · apply Subtype.ext
    simp [splitPBWWord, combinePBWWords, sumLexRightIndices,
      List.filterMap_map, Function.comp_def, ofLex_toLex]

/-- Ordered words over the lexicographic sum of two index types are
canonically pairs of ordered words.  This is the combinatorial core of the
relative PBW basis. -/
def pbwWordSumLexEquiv {α β : Type*} [LinearOrder α] [LinearOrder β] :
    PBWWord (α ⊕ₗ β) ≃ PBWWord α × PBWWord β where
  toFun := splitPBWWord
  invFun := combinePBWWords
  left_inv := combinePBWWords_splitPBWWord
  right_inv := splitPBWWord_combinePBWWords

instance {ι : Type w} [LinearOrder ι] : DecidableEq (PBWWord ι) :=
  Classical.decEq _

/-- The ordered product in the enveloping algebra associated to a word in
an ordered basis. -/
def pbwMonomial {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : List ι) : UniversalEnvelopingAlgebra k L :=
  (word.map fun i => UniversalEnvelopingAlgebra.ι k (b i)).prod

/-- The enveloping-algebra monomial indexed by an ordered word. -/
def orderedMonomial {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : PBWWord ι) :
    UniversalEnvelopingAlgebra k L :=
  pbwMonomial b word.1

/-- The subspace spanned by the ordered PBW monomials. -/
def orderedMonomialSpan {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : Submodule k (UniversalEnvelopingAlgebra k L) :=
  Submodule.span k (Set.range (orderedMonomial b))

theorem orderedMonomial_mem_span {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : PBWWord ι) :
    orderedMonomial b word ∈ orderedMonomialSpan b :=
  Submodule.subset_span ⟨word, rfl⟩

@[simp]
theorem pbwMonomial_nil {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) :
    pbwMonomial b [] = 1 :=
  rfl

@[simp]
theorem pbwMonomial_cons {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (i : ι) (word : List ι) :
    pbwMonomial b (i :: word) =
      UniversalEnvelopingAlgebra.ι k (b i) * pbwMonomial b word :=
  rfl

theorem pbwMonomial_append {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (u v : List ι) :
    pbwMonomial b (u ++ v) = pbwMonomial b u * pbwMonomial b v := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih, mul_assoc]

/-! ## Extending a Lie-algebra basis -/

/-- `Basis.sumExtend` retains the original linearly independent family on
the left summand of its index type.  This useful API lemma is not currently
provided by mathlib. -/
theorem Module.Basis.sumExtend_apply_inl
    {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {v : ι → V} (hv : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  unfold Module.Basis.sumExtend
  rw [Module.Basis.reindex_apply]
  change Module.Basis.extend hv.linearIndepOn_id _ = v i
  rw [Module.Basis.extend_apply_self]
  rfl

/-- The image of a basis under an injective Lie homomorphism is linearly
independent.  It is named so that every dependent relative-PBW definition
uses exactly the same proof term. -/
theorem mappedBasisLinearIndependent
    {ι : Type*} {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :
    LinearIndependent k (fun i => f (b i)) :=
  b.linearIndependent.map' f.toLinearMap
    (LinearMap.ker_eq_bot.2 hf)

/-- The index type for the complementary vectors added when extending the
image of a basis along an injective Lie homomorphism. -/
abbrev RelativeComplementIndex
    {ι : Type*} {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :=
  Module.Basis.sumExtendIndex (mappedBasisLinearIndependent b f hf)

/-- Extend the image of a basis along an injective Lie homomorphism to a
basis of the target Lie algebra. -/
noncomputable def extendMappedBasis
    {ι : Type*} {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :
    Basis (ι ⊕ RelativeComplementIndex b f hf) k Q :=
  Module.Basis.sumExtend (mappedBasisLinearIndependent b f hf)

@[simp]
theorem extendMappedBasis_apply_inl
    {ι : Type*} {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (i : ι) :
    extendMappedBasis b f hf (Sum.inl i) = f (b i) := by
  exact Module.Basis.sumExtend_apply_inl
    (mappedBasisLinearIndependent b f hf) i

/-- A fixed classical order on the complement indices.  Naming this
instance is essential because the relative PBW word type depends on the
chosen order. -/
@[instance_reducible]
noncomputable def relativeComplementLinearOrder
    {ι : Type*} {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :
    LinearOrder (RelativeComplementIndex b f hf) :=
  WellOrderingRel.isWellOrder.linearOrder

/-- The extended basis, reindexed by the lexicographic sum so that all
subalgebra indices precede all complement indices. -/
noncomputable def extendMappedBasisLex
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    Basis (ι ⊕ₗ RelativeComplementIndex b f hf) k Q := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  exact (extendMappedBasis b f hf).reindex toLex

@[simp]
theorem extendMappedBasisLex_apply_inl
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (i : ι) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    extendMappedBasisLex b f hf (toLex (Sum.inl i)) = f (b i) := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  rw [extendMappedBasisLex, Module.Basis.reindex_apply]
  change extendMappedBasis b f hf (Sum.inl i) = _
  exact extendMappedBasis_apply_inl b f hf i

/-- Mapping a basis monomial into a larger enveloping algebra gives the
monomial whose indices lie in the left summand of the extended basis. -/
theorem pbwMap_pbwMonomial
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (word : List ι) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    pbwMap f (pbwMonomial b word) =
      pbwMonomial (extendMappedBasisLex b f hf)
        (word.map fun i =>
          toLex (Sum.inl i : ι ⊕ RelativeComplementIndex b f hf)) := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  induction word with
  | nil => simp
  | cons i word ih =>
      rw [pbwMonomial_cons, map_mul, pbwMap_iota, ih]
      change UniversalEnvelopingAlgebra.ι k (f (b i)) * _ =
        pbwMonomial (extendMappedBasisLex b f hf)
          (toLex (Sum.inl i :
            ι ⊕ RelativeComplementIndex b f hf) :: _)
      rw [pbwMonomial_cons, extendMappedBasisLex_apply_inl]

/-- The empty ordered word. -/
def emptyPBWWord (α : Type*) [LinearOrder α] : PBWWord α :=
  ⟨[], by simp⟩

/-- The PBW monomial in the target enveloping algebra associated to an
ordered word consisting only of complement indices. -/
noncomputable def relativeComplementMonomial
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (word : let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
      PBWWord (RelativeComplementIndex b f hf)) :
    UniversalEnvelopingAlgebra k Q := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  exact orderedMonomial (extendMappedBasisLex b f hf)
    (combinePBWWords (emptyPBWWord ι, word))

/-- Under the ordered-word decomposition, an extended-basis monomial is
the product of the mapped subalgebra monomial and its complement
monomial. -/
theorem orderedMonomial_combinePBWWords
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (left : PBWWord ι)
    (right : let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
      PBWWord (RelativeComplementIndex b f hf)) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    orderedMonomial (extendMappedBasisLex b f hf)
        (combinePBWWords (left, right)) =
      pbwMap f (orderedMonomial b left) *
        relativeComplementMonomial b f hf right := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  rw [orderedMonomial, orderedMonomial, combinePBWWords,
    pbwMonomial_append, pbwMap_pbwMonomial]
  rfl

/-- The span of all (not necessarily ordered) monomials in a chosen basis. -/
def monomialSpan {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : Submodule k (UniversalEnvelopingAlgebra k L) :=
  Submodule.span k (Set.range (pbwMonomial b))

theorem one_mem_monomialSpan {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) :
    (1 : UniversalEnvelopingAlgebra k L) ∈ monomialSpan b := by
  apply Submodule.subset_span
  exact ⟨[], pbwMonomial_nil b⟩

theorem mul_mem_monomialSpan {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) {x y : UniversalEnvelopingAlgebra k L}
    (hx : x ∈ monomialSpan b) (hy : y ∈ monomialSpan b) :
    x * y ∈ monomialSpan b := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => x * y ∈ monomialSpan b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    rw [← pbwMonomial_append]
    exact Submodule.subset_span ⟨u ++ v, rfl⟩
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz hxz hyz
    simpa [add_mul] using (monomialSpan b).add_mem hxz hyz
  · intro x y z hx hy hz hxy hxz
    simpa [mul_add] using (monomialSpan b).add_mem hxy hxz
  · intro r x y hx hy hxy
    simpa [smul_mul_assoc] using (monomialSpan b).smul_mem r hxy
  · intro r x y hx hy hxy
    simpa [mul_smul_comm] using (monomialSpan b).smul_mem r hxy

/-- The subalgebra spanned by all basis monomials. -/
def monomialSubalgebra {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) :
    Subalgebra k (UniversalEnvelopingAlgebra k L) where
  carrier := monomialSpan b
  add_mem' := (monomialSpan b).add_mem
  mul_mem' := mul_mem_monomialSpan b
  algebraMap_mem' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (monomialSpan b).smul_mem r (one_mem_monomialSpan b)

theorem iota_mem_monomialSubalgebra {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (x : L) :
    UniversalEnvelopingAlgebra.ι k x ∈ monomialSubalgebra b := by
  have hx : ∑ i ∈ (b.repr x).support, (b.repr x i) • b i = x := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      b.linearCombination_repr x
  rw [← hx, map_sum]
  apply Submodule.sum_mem
  intro i hi
  simp only [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨[i], by simp [pbwMonomial]⟩

/-- Arbitrary basis monomials span the universal enveloping algebra. -/
theorem monomialSpan_eq_top {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : monomialSpan b = ⊤ := by
  let A := monomialSubalgebra b
  let of : L →ₗ⁅k⁆ A := {
    toLinearMap := (UniversalEnvelopingAlgebra.ι k).toLinearMap.codRestrict
      A.toSubmodule (iota_mem_monomialSubalgebra b)
    map_lie' := fun {x y} => by
      apply Subtype.ext
      exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι k) x y }
  let liftA : UniversalEnvelopingAlgebra k L →ₐ[k] A :=
    UniversalEnvelopingAlgebra.lift k of
  have hval : A.val.comp liftA = AlgHom.id k _ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro x
    change A.val (liftA (UniversalEnvelopingAlgebra.ι k x)) =
      UniversalEnvelopingAlgebra.ι k x
    rw [show liftA (UniversalEnvelopingAlgebra.ι k x) = of x from
      UniversalEnvelopingAlgebra.lift_ι_apply k of x]
    rfl
  apply top_unique
  intro x hx
  have hxA : A.val (liftA x) = x := DFunLike.congr_fun hval x
  rw [← hxA]
  exact (liftA x).property

/-- The elementary adjacent-transposition relation underlying PBW. -/
theorem iota_mul_iota_swap (x y : L) :
    UniversalEnvelopingAlgebra.ι k x * UniversalEnvelopingAlgebra.ι k y =
      UniversalEnvelopingAlgebra.ι k y * UniversalEnvelopingAlgebra.ι k x +
        UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι k) x y
  change UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ =
    UniversalEnvelopingAlgebra.ι k x * UniversalEnvelopingAlgebra.ι k y -
      UniversalEnvelopingAlgebra.ι k y * UniversalEnvelopingAlgebra.ι k x at h
  rw [h]
  abel

/-- Expand the bracket of two basis vectors in its finitely supported basis
coordinates after mapping it into the enveloping algebra. -/
theorem iota_bracket_eq_sum_support {ι : Type w}
    (b : Basis ι k L) (i j : ι) :
    UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ =
      ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
        (b.repr ⁅b i, b j⁆ l) •
        UniversalEnvelopingAlgebra.ι k (b l) := by
  have hrecon :
      ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
          (b.repr ⁅b i, b j⁆ l) • b l = ⁅b i, b j⁆ := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      b.linearCombination_repr ⁅b i, b j⁆
  calc
    UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ =
        UniversalEnvelopingAlgebra.ι k
          (∑ l ∈ (b.repr ⁅b i, b j⁆).support,
            (b.repr ⁅b i, b j⁆ l) • b l) := congrArg _ hrecon.symm
    _ = ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
          (b.repr ⁅b i, b j⁆ l) •
            UniversalEnvelopingAlgebra.ι k (b l) := by simp

/-- The word-length filtration on the span of basis monomials. -/
def monomialFiltration {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (n : ℕ) :
    Submodule k (UniversalEnvelopingAlgebra k L) :=
  Submodule.span k {x | ∃ word : List ι,
    word.length ≤ n ∧ pbwMonomial b word = x}

theorem pbwMonomial_mem_filtration {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : List ι) {n : ℕ}
    (hword : word.length ≤ n) :
    pbwMonomial b word ∈ monomialFiltration b n := by
  apply Submodule.subset_span
  exact ⟨word, hword, rfl⟩

theorem monomialFiltration_mono {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) {m n : ℕ} (hmn : m ≤ n) :
    monomialFiltration b m ≤ monomialFiltration b n := by
  apply Submodule.span_mono
  rintro x ⟨word, hword, rfl⟩
  exact ⟨word, hword.trans hmn, rfl⟩

theorem iota_mul_mem_monomialFiltration_succ
    {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (i : ι) {n : ℕ}
    {x : UniversalEnvelopingAlgebra k L}
    (hx : x ∈ monomialFiltration b n) :
    UniversalEnvelopingAlgebra.ι k (b i) * x ∈
      monomialFiltration b (n + 1) := by
  refine Submodule.span_induction (p := fun x _ =>
      UniversalEnvelopingAlgebra.ι k (b i) * x ∈
        monomialFiltration b (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨word, hword, rfl⟩
    rw [← pbwMonomial_cons]
    apply pbwMonomial_mem_filtration
    simp only [List.length_cons]
    omega
  · simp
  · intro x y hx hy hxi hyi
    simpa [mul_add] using (monomialFiltration b (n + 1)).add_mem hxi hyi
  · intro r x hx hxi
    simpa [mul_smul_comm] using
      (monomialFiltration b (n + 1)).smul_mem r hxi

theorem pbwMonomial_perm_sub_mem_filtration
    {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) {u v : List ι} (huv : u.Perm v) :
    pbwMonomial b u - pbwMonomial b v ∈
      monomialFiltration b (u.length - 1) := by
  induction huv with
  | nil => simp
  | @cons i u v huv ih =>
      rw [pbwMonomial_cons, pbwMonomial_cons, ← mul_sub]
      have hmem := iota_mul_mem_monomialFiltration_succ b i ih
      by_cases hu : u = []
      · subst u
        have hv : v = [] := List.Perm.eq_nil huv.symm
        subst v
        simp
      · have hpos : 0 < u.length := List.length_pos_of_ne_nil hu
        have hindex : u.length - 1 + 1 = u.length := by omega
        rw [hindex] at hmem
        exact hmem
  | @swap i j word =>
      rw [pbwMonomial_cons, pbwMonomial_cons, pbwMonomial_cons,
        pbwMonomial_cons]
      have hswap := iota_mul_iota_swap (k := k) (L := L) (b i) (b j)
      have heq :
          UniversalEnvelopingAlgebra.ι k (b i) *
                (UniversalEnvelopingAlgebra.ι k (b j) *
                  pbwMonomial b word) -
              UniversalEnvelopingAlgebra.ι k (b j) *
                (UniversalEnvelopingAlgebra.ι k (b i) *
                  pbwMonomial b word) =
            UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ *
              pbwMonomial b word := by
        rw [← mul_assoc, ← mul_assoc, hswap]
        rw [add_mul]
        abel
      have hbracket :
          UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ *
              pbwMonomial b word ∈
            monomialFiltration b ((i :: j :: word).length - 1) := by
        rw [iota_bracket_eq_sum_support b i j, Finset.sum_mul]
        apply Submodule.sum_mem
        intro l hl
        rw [smul_mul_assoc, ← pbwMonomial_cons]
        apply Submodule.smul_mem
        apply pbwMonomial_mem_filtration
        simp
      have hneg := (monomialFiltration b
        ((i :: j :: word).length - 1)).neg_mem hbracket
      rw [← heq] at hneg
      simpa only [neg_sub, List.length_cons] using hneg
  | @trans u v w huv hvw ihuv ihvw =>
      have hlen : u.length = v.length := huv.length_eq
      rw [hlen] at ihuv ⊢
      have hadd := (monomialFiltration b (v.length - 1)).add_mem ihuv ihvw
      rw [show pbwMonomial b u - pbwMonomial b w =
        (pbwMonomial b u - pbwMonomial b v) +
          (pbwMonomial b v - pbwMonomial b w) by abel]
      exact hadd

/-- Every basis monomial is a linear combination of ordered monomials. -/
theorem pbwMonomial_mem_orderedMonomialSpan
    {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : List ι) :
    pbwMonomial b word ∈ orderedMonomialSpan b := by
  induction h : word.length using Nat.strong_induction_on generalizing word with
  | h n ih =>
      by_cases hnil : word = []
      · subst word
        exact orderedMonomial_mem_span b ⟨[], by simp⟩
      let sorted := word.mergeSort (fun i j => i ≤ j)
      have hperm : word.Perm sorted := (List.mergeSort_perm word _).symm
      have hsorted : sorted.Pairwise (· ≤ ·) :=
        List.pairwise_mergeSort' (· ≤ ·) word
      have hlower : monomialFiltration b (word.length - 1) ≤
          orderedMonomialSpan b := by
        apply Submodule.span_le.2
        rintro _ ⟨v, hv, rfl⟩
        apply ih v.length
        · have hpos : 0 < word.length := List.length_pos_of_ne_nil hnil
          omega
        · rfl
      have hdiff := hlower (pbwMonomial_perm_sub_mem_filtration b hperm)
      have hsort : pbwMonomial b sorted ∈ orderedMonomialSpan b := by
        exact orderedMonomial_mem_span b ⟨sorted, hsorted⟩
      have := (orderedMonomialSpan b).add_mem hdiff hsort
      rw [show pbwMonomial b word =
        (pbwMonomial b word - pbwMonomial b sorted) +
          pbwMonomial b sorted by abel]
      exact this

/-- Ordered PBW monomials span the universal enveloping algebra. -/
theorem orderedMonomialSpan_eq_top {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : orderedMonomialSpan b = ⊤ := by
  rw [← monomialSpan_eq_top b]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨word, rfl⟩
    apply Submodule.subset_span
    exact ⟨word.1, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨word, rfl⟩
    exact pbwMonomial_mem_orderedMonomialSpan b word

/-- Package the spanning theorem and linear independence into the absolute
PBW basis.  The remaining absolute PBW task is precisely to supply the
linear-independence argument. -/
noncomputable def orderedMonomialBasisOfLinearIndependent
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (h : LinearIndependent k (orderedMonomial b)) :
    Basis (PBWWord ι) k (UniversalEnvelopingAlgebra k L) :=
  Basis.mk h (orderedMonomialSpan_eq_top b).ge

@[simp]
theorem orderedMonomialBasisOfLinearIndependent_apply
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (h : LinearIndependent k (orderedMonomial b)) (word : PBWWord ι) :
    orderedMonomialBasisOfLinearIndependent b h word =
      orderedMonomial b word :=
  Basis.mk_apply _ _ _

/-! ## Relative PBW from the absolute basis theorem -/

/-- Once absolute PBW linear independence is known for a basis and its
extension, the complement monomials form the relative PBW basis. -/
noncomputable def relativePBWBasisOfLinearIndependent
    {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (hL : LinearIndependent k (orderedMonomial b))
    (hQ : let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
      LinearIndependent k (orderedMonomial (extendMappedBasisLex b f hf))) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    RelativePBWBasis f (PBWWord (RelativeComplementIndex b f hf)) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  let _ : Module UL UQ := relativeModule f
  let _ : IsScalarTower k UL UQ :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change pbwMap f (algebraMap k UL r) * x = r • x
      rw [(pbwMap f).commutes, Algebra.smul_def])
  let aBasis : Basis (PBWWord ι) k UL :=
    orderedMonomialBasisOfLinearIndependent b hL
  let qBasis0 : Basis
      (PBWWord (ι ⊕ₗ RelativeComplementIndex b f hf)) k UQ :=
    orderedMonomialBasisOfLinearIndependent
      (extendMappedBasisLex b f hf) hQ
  let qBasis : Basis
      (PBWWord ι × PBWWord (RelativeComplementIndex b f hf)) k UQ :=
    qBasis0.reindex pbwWordSumLexEquiv
  let v : PBWWord (RelativeComplementIndex b f hf) → UQ :=
    relativeComplementMonomial b f hf
  apply basisOfTowerFactors aBasis qBasis v
  intro left right
  dsimp [qBasis, qBasis0, aBasis, v, pbwWordSumLexEquiv]
  rw [Basis.reindex_apply,
    orderedMonomialBasisOfLinearIndependent_apply,
    orderedMonomialBasisOfLinearIndependent_apply]
  change orderedMonomial (extendMappedBasisLex b f hf)
      (combinePBWWords (left, right)) =
    pbwMap f (orderedMonomial b left) *
      relativeComplementMonomial b f hf right
  exact orderedMonomial_combinePBWWords b f hf left right

/-- The canonical linear combination map from formal finite combinations
of ordered words to the enveloping algebra. -/
noncomputable def orderedMonomialLinearCombination
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    (PBWWord ι →₀ k) →ₗ[k] UniversalEnvelopingAlgebra k L :=
  Finsupp.linearCombination k (orderedMonomial b)

theorem orderedMonomialLinearCombination_surjective
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    Function.Surjective (orderedMonomialLinearCombination b) := by
  rw [← LinearMap.range_eq_top, orderedMonomialLinearCombination,
    Finsupp.range_linearCombination]
  exact orderedMonomialSpan_eq_top b

/-! ## Termination data for the PBW normal-form construction -/

/-- The number of inversions in a finite word. -/
def inversionCount {ι : Type w} [LinearOrder ι] : List ι → ℕ
  | [] => 0
  | i :: word => (word.filter fun j => j < i).length + inversionCount word

@[simp]
theorem inversionCount_nil {ι : Type w} [LinearOrder ι] :
    inversionCount ([] : List ι) = 0 :=
  rfl

@[simp]
theorem inversionCount_cons {ι : Type w} [LinearOrder ι]
    (i : ι) (word : List ι) :
    inversionCount (i :: word) =
      (word.filter fun j => j < i).length + inversionCount word :=
  rfl

theorem inversionCount_le_length_sq {ι : Type w} [LinearOrder ι]
    (word : List ι) : inversionCount word ≤ word.length ^ 2 := by
  induction word with
  | nil => simp
  | cons i word ih =>
      rw [inversionCount_cons, List.length_cons]
      have hfilter : (word.filter fun j => j < i).length ≤ word.length :=
        List.length_filter_le _ _
      nlinarith

theorem inversionCount_swap_adjacent {ι : Type w} [LinearOrder ι]
    (pre suffix : List ι) {i j : ι} (hji : j < i) :
    inversionCount (pre ++ i :: j :: suffix) =
      inversionCount (pre ++ j :: i :: suffix) + 1 := by
  induction pre with
  | nil =>
      simp [inversionCount, hji, not_lt_of_ge hji.le]
      omega
  | cons a pre ih =>
      simp only [List.cons_append, inversionCount_cons]
      have hperm : (pre ++ i :: j :: suffix).Perm
          (pre ++ j :: i :: suffix) :=
        List.Perm.append_left pre (List.Perm.swap j i suffix)
      have hfilter := (hperm.filter fun x => x < a).length_eq
      rw [hfilter, ih]
      omega

/-- A single natural-valued measure which decreases both when an adjacent
inversion is swapped and when a bracket shortens a word. -/
def pbwWordMeasure {ι : Type w} [LinearOrder ι] (word : List ι) : ℕ :=
  word.length ^ 3 + inversionCount word

theorem pbwWordMeasure_swap_adjacent {ι : Type w} [LinearOrder ι]
    (pre suffix : List ι) {i j : ι} (hji : j < i) :
    pbwWordMeasure (pre ++ j :: i :: suffix) <
      pbwWordMeasure (pre ++ i :: j :: suffix) := by
  rw [pbwWordMeasure, pbwWordMeasure,
    inversionCount_swap_adjacent pre suffix hji]
  have hlen : (pre ++ j :: i :: suffix).length =
      (pre ++ i :: j :: suffix).length := by simp
  rw [hlen]
  omega

theorem pbwWordMeasure_shorter {ι : Type w} [LinearOrder ι]
    {u v : List ι} (hlen : u.length < v.length) :
    pbwWordMeasure u < pbwWordMeasure v := by
  rw [pbwWordMeasure, pbwWordMeasure]
  have hinv := inversionCount_le_length_sq u
  have hlen' : u.length + 1 ≤ v.length := hlen
  calc
    u.length ^ 3 + inversionCount u ≤
        u.length ^ 3 + u.length ^ 2 := Nat.add_le_add_left hinv _
    _ < (u.length + 1) ^ 3 := by nlinarith
    _ ≤ v.length ^ 3 := Nat.pow_le_pow_left hlen' 3
    _ ≤ v.length ^ 3 + inversionCount v := Nat.le_add_right _ _

/-- A non-ordered word contains an adjacent inversion. -/
theorem exists_adjacent_inversion_of_not_pairwise
    {ι : Type w} [LinearOrder ι] {word : List ι}
    (hword : ¬ word.Pairwise (· ≤ ·)) :
    ∃ (pre suffix : List ι) (i j : ι),
      word = pre ++ i :: j :: suffix ∧ j < i := by
  have hchain : ¬ word.IsChain (· ≤ ·) := by
    simpa [List.isChain_iff_pairwise] using hword
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
  push Not at hchain
  obtain ⟨i, j, pre, suffix, hsplit, hij⟩ := hchain
  exact ⟨pre, suffix, i, j, hsplit, hij⟩

/-- The data of a chosen adjacent inversion in a word. -/
structure AdjacentInversion {ι : Type w} [LinearOrder ι]
    (word : List ι) where
  pre : List ι
  suffix : List ι
  left : ι
  right : ι
  word_eq : word = pre ++ left :: right :: suffix
  right_lt_left : right < left

namespace AdjacentInversion

variable {ι : Type w} [LinearOrder ι] {word : List ι}

/-- Swap the distinguished adjacent inversion. -/
def swapped (d : AdjacentInversion word) : List ι :=
  d.pre ++ d.right :: d.left :: d.suffix

/-- Replace the distinguished adjacent pair by one letter. -/
def bracketWord (d : AdjacentInversion word) (i : ι) : List ι :=
  d.pre ++ i :: d.suffix

theorem swapped_measure_lt (d : AdjacentInversion word) :
    pbwWordMeasure d.swapped < pbwWordMeasure word := by
  calc
    pbwWordMeasure d.swapped <
        pbwWordMeasure (d.pre ++ d.left :: d.right :: d.suffix) :=
      pbwWordMeasure_swap_adjacent d.pre d.suffix d.right_lt_left
    _ = pbwWordMeasure word := congrArg pbwWordMeasure d.word_eq.symm

theorem bracketWord_length_lt (d : AdjacentInversion word) (i : ι) :
    (d.bracketWord i).length < word.length := by
  calc
    (d.bracketWord i).length <
        (d.pre ++ d.left :: d.right :: d.suffix).length := by
      simp [bracketWord]
    _ = word.length := congrArg List.length d.word_eq.symm

theorem bracketWord_measure_lt (d : AdjacentInversion word) (i : ι) :
    pbwWordMeasure (d.bracketWord i) < pbwWordMeasure word :=
  pbwWordMeasure_shorter (d.bracketWord_length_lt i)

end AdjacentInversion

/-- The rightmost adjacent inversion in a nonordered word.  Making the
choice deterministic is essential for the word-level Jacobi calculation
in the PBW representation; the rightmost convention makes reduction
compatible with adding a letter on the left until the suffix is ordered. -/
def chosenAdjacentInversion
    {ι : Type w} [LinearOrder ι] (word : List ι)
    (hword : ¬ word.Pairwise (· ≤ ·)) : AdjacentInversion word :=
  match word with
  | [] => False.elim (hword (by simp))
  | [_] => False.elim (hword (by simp))
  | left :: right :: suffix =>
      if htail : ¬ (right :: suffix).Pairwise (· ≤ ·) then
        let d := chosenAdjacentInversion (right :: suffix) htail
        ⟨left :: d.pre, d.suffix, d.left, d.right, by
          simp only [List.cons_append]
          rw [← d.word_eq], d.right_lt_left⟩
      else
        have hright : right < left := lt_of_not_ge fun hleft =>
          hword ((List.pairwise_cons_cons_iff_of_trans).2
            ⟨hleft, not_not.mp htail⟩)
        ⟨[], suffix, left, right, rfl, hright⟩
termination_by word.length
decreasing_by simp

theorem chosenAdjacentInversion_of_head
    {ι : Type w} [LinearOrder ι] (left right : ι) (suffix : List ι)
    (hright : right < left)
    (htail : (right :: suffix).Pairwise (· ≤ ·))
    (hword : ¬ (left :: right :: suffix).Pairwise (· ≤ ·)) :
    chosenAdjacentInversion (left :: right :: suffix) hword =
      ⟨[], suffix, left, right, rfl, hright⟩ := by
  rw [chosenAdjacentInversion]
  rw [dite_eq_right (not_not.mpr htail)]

/-- If the tail is not ordered, rightmost reduction ignores a newly
adjoined head letter and chooses the same inversion in the tail. -/
theorem chosenAdjacentInversion_cons_of_not_pairwise
    {ι : Type w} [LinearOrder ι] (head : ι) (tail : List ι)
    (htail : ¬ tail.Pairwise (· ≤ ·))
    (hword : ¬ (head :: tail).Pairwise (· ≤ ·)) :
    chosenAdjacentInversion (head :: tail) hword =
      let d := chosenAdjacentInversion tail htail
      ⟨head :: d.pre, d.suffix, d.left, d.right, by
        simp only [List.cons_append]
        rw [← d.word_eq], d.right_lt_left⟩ := by
  match tail with
  | [] => exact False.elim (htail (by simp))
  | [_] => exact False.elim (htail (by simp))
  | right :: next :: suffix =>
      rw [chosenAdjacentInversion]
      rw [dite_eq_left htail]

/-- Reduction of a word to a finite linear combination of ordered words.
The recursion is the usual PBW adjacent-transposition rule. -/
noncomputable def pbwNormalForm {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (word : List ι) : PBWWord ι →₀ k :=
  if hword : word.Pairwise (· ≤ ·) then
    Finsupp.single ⟨word, hword⟩ 1
  else
    let d := chosenAdjacentInversion word hword
    pbwNormalForm b d.swapped +
      ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
        (b.repr ⁅b d.left, b d.right⁆ i) •
          pbwNormalForm b (d.bracketWord i)
termination_by pbwWordMeasure word
decreasing_by
  · exact d.swapped_measure_lt
  · exact d.bracketWord_measure_lt i

theorem pbwNormalForm_of_pairwise {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) {word : List ι}
    (hword : word.Pairwise (· ≤ ·)) :
    pbwNormalForm b word = Finsupp.single ⟨word, hword⟩ 1 := by
  rw [pbwNormalForm]
  split
  · rfl
  · contradiction

theorem pbwNormalForm_of_not_pairwise {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) {word : List ι}
    (hword : ¬ word.Pairwise (· ≤ ·)) :
    pbwNormalForm b word =
      let d := chosenAdjacentInversion word hword
      pbwNormalForm b d.swapped +
        ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
          (b.repr ⁅b d.left, b d.right⁆ i) •
            pbwNormalForm b (d.bracketWord i) := by
  rw [pbwNormalForm]
  split
  · contradiction
  · rfl

/-- The normal-form equation at a leftmost adjacent inversion. -/
theorem pbwNormalForm_cons_cons_of_lt
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (left right : ι) (suffix : List ι) (hright : right < left)
    (htail : (right :: suffix).Pairwise (· ≤ ·)) :
    pbwNormalForm b (left :: right :: suffix) =
      pbwNormalForm b (right :: left :: suffix) +
        ∑ i ∈ (b.repr ⁅b left, b right⁆).support,
          (b.repr ⁅b left, b right⁆ i) •
            pbwNormalForm b (i :: suffix) := by
  have hword : ¬ (left :: right :: suffix).Pairwise (· ≤ ·) := by
    intro hordered
    exact (not_le_of_gt hright)
      ((List.pairwise_cons_cons_iff_of_trans).1 hordered).1
  rw [pbwNormalForm_of_not_pairwise b hword]
  rw [chosenAdjacentInversion_of_head left right suffix hright htail hword]
  rfl

/-- Rightmost normal-form reduction commutes with adjoining a head letter
as long as the old word still contains an inversion. -/
theorem pbwNormalForm_cons_of_not_pairwise
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (head : ι) (word : List ι) (hword : ¬ word.Pairwise (· ≤ ·)) :
    let d := chosenAdjacentInversion word hword
    pbwNormalForm b (head :: word) =
      pbwNormalForm b (head :: d.swapped) +
        ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
          (b.repr ⁅b d.left, b d.right⁆ i) •
            pbwNormalForm b (head :: d.bracketWord i) := by
  have hcons : ¬ (head :: word).Pairwise (· ≤ ·) := fun hordered =>
    hword (List.pairwise_cons.1 hordered).2
  rw [pbwNormalForm_of_not_pairwise b hcons]
  rw [chosenAdjacentInversion_cons_of_not_pairwise head word hword hcons]
  rfl

/-! ## The degree filtration on formal PBW combinations -/

/-- Formal ordered-word combinations supported in degree at most `n`. -/
def pbwNormalFormFiltration {ι : Type w} [LinearOrder ι] (n : ℕ) :
    Submodule k (PBWWord ι →₀ k) :=
  Finsupp.supported k k {word | word.1.length ≤ n}

theorem pbwNormalFormFiltration_mono
    {ι : Type w} [LinearOrder ι] {m n : ℕ} (hmn : m ≤ n) :
    pbwNormalFormFiltration (k := k) (ι := ι) m ≤
      pbwNormalFormFiltration (k := k) (ι := ι) n := by
  exact Finsupp.supported_mono fun _ h => h.trans hmn

theorem single_mem_pbwNormalFormFiltration
    {ι : Type w} [LinearOrder ι] (word : PBWWord ι) {n : ℕ}
    (hword : word.1.length ≤ n) :
    Finsupp.single word (1 : k) ∈
      pbwNormalFormFiltration (k := k) n := by
  exact Finsupp.single_mem_supported k 1 hword

/-- Normalization never increases word length. -/
theorem pbwNormalForm_mem_filtration
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (word : List ι) :
    pbwNormalForm b word ∈
      pbwNormalFormFiltration (k := k) word.length := by
  apply (InvImage.wf pbwWordMeasure Nat.lt_wfRel.wf).induction word
  intro word ih
  by_cases hword : word.Pairwise (· ≤ ·)
  · rw [pbwNormalForm_of_pairwise b hword]
    exact single_mem_pbwNormalFormFiltration ⟨word, hword⟩ le_rfl
  · rw [pbwNormalForm_of_not_pairwise b hword]
    let d := chosenAdjacentInversion word hword
    apply Submodule.add_mem
    · have hlen : d.swapped.length = word.length := by
        simp [AdjacentInversion.swapped, d.word_eq]
      rw [← hlen]
      exact ih d.swapped d.swapped_measure_lt
    · apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      apply pbwNormalFormFiltration_mono
        (Nat.le_of_lt (d.bracketWord_length_lt l))
      exact ih (d.bracketWord l) (d.bracketWord_measure_lt l)

/-- The ordered word obtained by sorting a list of basis indices. -/
def sortedPBWWord {ι : Type w} [LinearOrder ι] (word : List ι) : PBWWord ι :=
  ⟨word.mergeSort (· ≤ ·), List.pairwise_mergeSort' (· ≤ ·) word⟩

@[simp]
theorem sortedPBWWord_length
    {ι : Type w} [LinearOrder ι] (word : List ι) :
    (sortedPBWWord word).1.length = word.length := by
  exact List.Perm.length_eq (List.mergeSort_perm word (· ≤ ·))

theorem sortedPBWWord_eq_of_pairwise
    {ι : Type w} [LinearOrder ι] {word : List ι}
    (hword : word.Pairwise (· ≤ ·)) :
    sortedPBWWord word = ⟨word, hword⟩ := by
  apply Subtype.ext
  exact List.mergeSort_eq_self (· ≤ ·) hword

theorem sortedPBWWord_eq_of_perm
    {ι : Type w} [LinearOrder ι] {u v : List ι} (huv : u.Perm v) :
    sortedPBWWord u = sortedPBWWord v := by
  apply Subtype.ext
  have hperm :
      (u.mergeSort (· ≤ ·)).Perm (v.mergeSort (· ≤ ·)) :=
    (List.mergeSort_perm u (· ≤ ·)).trans
      (huv.trans (List.mergeSort_perm v (· ≤ ·)).symm)
  exact List.Perm.eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) u)
    (List.pairwise_mergeSort' (· ≤ ·) v) hperm

theorem AdjacentInversion.swapped_perm
    {ι : Type w} [LinearOrder ι] {word : List ι}
    (d : AdjacentInversion word) : d.swapped.Perm word := by
  calc
    d.swapped.Perm
        (d.pre ++ d.left :: d.right :: d.suffix) :=
      ((List.Perm.swap d.right d.left d.suffix).append_left d.pre).symm
    _ = word := d.word_eq.symm

/-- The top-degree part of a normal form is the single sorted permutation
of the original word; every bracket correction has strictly smaller
degree. -/
theorem pbwNormalForm_sub_sorted_mem_filtration
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (word : List ι) :
    pbwNormalForm b word - Finsupp.single (sortedPBWWord word) 1 ∈
      pbwNormalFormFiltration (k := k) (word.length - 1) := by
  apply (InvImage.wf pbwWordMeasure Nat.lt_wfRel.wf).induction word
  intro word ih
  by_cases hword : word.Pairwise (· ≤ ·)
  · rw [pbwNormalForm_of_pairwise b hword,
      sortedPBWWord_eq_of_pairwise hword, sub_self]
    exact Submodule.zero_mem _
  · rw [pbwNormalForm_of_not_pairwise b hword]
    let d := chosenAdjacentInversion word hword
    have hlen : d.swapped.length = word.length :=
      d.swapped_perm.length_eq
    have hsorted : sortedPBWWord d.swapped = sortedPBWWord word :=
      sortedPBWWord_eq_of_perm d.swapped_perm
    have hswap :
        pbwNormalForm b d.swapped -
            Finsupp.single (sortedPBWWord word) 1 ∈
          pbwNormalFormFiltration (k := k) (word.length - 1) := by
      rw [← hsorted, ← hlen]
      exact ih d.swapped d.swapped_measure_lt
    have hbracket :
        (∑ l ∈ (b.repr ⁅b d.left, b d.right⁆).support,
          (b.repr ⁅b d.left, b d.right⁆ l) •
            pbwNormalForm b (d.bracketWord l)) ∈
          pbwNormalFormFiltration (k := k) (word.length - 1) := by
      apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      have hlength : (d.bracketWord l).length = word.length - 1 := by
        simp [AdjacentInversion.bracketWord, d.word_eq]
      rw [← hlength]
      exact pbwNormalForm_mem_filtration b (d.bracketWord l)
    have hadd := (pbwNormalFormFiltration (k := k)
      (ι := ι) (word.length - 1)).add_mem hswap hbracket
    change (pbwNormalForm b d.swapped +
        ∑ l ∈ (b.repr ⁅b d.left, b d.right⁆).support,
          (b.repr ⁅b d.left, b d.right⁆ l) •
            pbwNormalForm b (d.bracketWord l)) -
      Finsupp.single (sortedPBWWord word) 1 ∈ _
    rw [show (pbwNormalForm b d.swapped +
          ∑ l ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ l) •
              pbwNormalForm b (d.bracketWord l)) -
        Finsupp.single (sortedPBWWord word) 1 =
      (pbwNormalForm b d.swapped -
        Finsupp.single (sortedPBWWord word) 1) +
          ∑ l ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ l) •
              pbwNormalForm b (d.bracketWord l) by abel]
    exact hadd

/-- The word normal form extended linearly from the tensor-word basis to
the whole tensor algebra. -/
noncomputable def tensorPBWNormalForm {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) :
    TensorAlgebra k L →ₗ[k] (PBWWord ι →₀ k) :=
  b.tensorAlgebra.constr k fun word : FreeMonoid ι =>
    pbwNormalForm b word.toList

@[simp]
theorem tensorPBWNormalForm_basis_apply
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (word : FreeMonoid ι) :
    tensorPBWNormalForm b (b.tensorAlgebra word) =
      pbwNormalForm b word.toList := by
  exact b.tensorAlgebra.constr_basis k _ word

/-- The tensor-word basis vector is the product of the corresponding
degree-one generators. -/
theorem tensorAlgebraBasis_apply_eq_list_prod
    {ι : Type w} (b : Basis ι k L) (word : FreeMonoid ι) :
    b.tensorAlgebra word =
      (word.toList.map fun i => TensorAlgebra.ι k (b i)).prod := by
  induction word using FreeMonoid.recOn with
  | one =>
      change (TensorAlgebra.equivFreeAlgebra b).symm
          (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
            (MonoidAlgebra.single 1 1)) = 1
      rw [show MonoidAlgebra.single (1 : FreeMonoid ι) (1 : k) = 1 from
        MonoidAlgebra.one_def.symm]
      simp
  | of_mul i word ih =>
      rw [FreeMonoid.toList_of_mul, List.map_cons, List.prod_cons, ← ih]
      rw [← TensorAlgebra.equivFreeAlgebra_symm_ι b i]
      change (TensorAlgebra.equivFreeAlgebra b).symm
          (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
            (MonoidAlgebra.single (FreeMonoid.of i * word) 1)) =
        (TensorAlgebra.equivFreeAlgebra b).symm (FreeAlgebra.ι k i) *
          (TensorAlgebra.equivFreeAlgebra b).symm
            (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
              (MonoidAlgebra.single word 1))
      rw [← map_mul]
      apply (TensorAlgebra.equivFreeAlgebra b).injective
      simp only [AlgEquiv.apply_symm_apply]
      change FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
          (MonoidAlgebra.single (FreeMonoid.of i * word) 1) =
        FreeAlgebra.ι k i *
          FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
            (MonoidAlgebra.single word 1)
      apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
      simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

theorem tensorPBWNormalForm_word
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (word : List ι) :
    tensorPBWNormalForm b
        ((word.map fun i => TensorAlgebra.ι k (b i)).prod) =
      pbwNormalForm b word := by
  let freeWord : FreeMonoid ι := FreeMonoid.ofList word
  change tensorPBWNormalForm b
      ((freeWord.toList.map fun i => TensorAlgebra.ι k (b i)).prod) = _
  rw [← tensorAlgebraBasis_apply_eq_list_prod b freeWord,
    tensorPBWNormalForm_basis_apply]
  simp [freeWord]

/-- The ordered word consisting of one basis index. -/
def singletonPBWWord {ι : Type w} [LinearOrder ι] (i : ι) : PBWWord ι :=
  ⟨[i], by simp⟩

/-- Recover the degree-one component of a formal PBW combination. -/
noncomputable def pbwDegreeOneRecover
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    (PBWWord ι →₀ k) →ₗ[k] L :=
  Finsupp.linearCombination k fun word =>
    match word.1 with
    | [i] => b i
    | _ => 0

@[simp]
theorem pbwDegreeOneRecover_singleton
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (i : ι) :
    pbwDegreeOneRecover b (Finsupp.single (singletonPBWWord i) 1) = b i := by
  simp [pbwDegreeOneRecover, singletonPBWWord]

/-- Tensor normal form is injective on the degree-one generators. -/
theorem tensorPBWNormalForm_comp_iota_injective
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    Function.Injective
      ((tensorPBWNormalForm b).comp (TensorAlgebra.ι k)) := by
  apply Function.LeftInverse.injective
    (g := pbwDegreeOneRecover b)
  have hleft : (pbwDegreeOneRecover b).comp
      ((tensorPBWNormalForm b).comp (TensorAlgebra.ι k)) =
      LinearMap.id := by
    apply b.ext
    intro i
    change pbwDegreeOneRecover b
        (tensorPBWNormalForm b (TensorAlgebra.ι k (b i))) = b i
    rw [show TensorAlgebra.ι k (b i) =
        (([i].map fun j => TensorAlgebra.ι k (b j)).prod) by simp]
    rw [tensorPBWNormalForm_word, pbwNormalForm_of_pairwise]
    exact pbwDegreeOneRecover_singleton b i
  intro x
  exact LinearMap.congr_fun hleft x

/-- The precise Diamond-lemma obligation: tensor normal form is constant
on the congruence defining the universal enveloping algebra. -/
def TensorPBWNormalFormRespectsRingCon
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) : Prop :=
  ∀ a c : TensorAlgebra k L,
    UniversalEnvelopingAlgebra.ringCon k L a c →
      tensorPBWNormalForm b a = tensorPBWNormalForm b c

/-- Congruence invariance of tensor normal form implies injectivity of the
canonical Lie map. -/
theorem iota_injective_of_tensorPBWNormalForm_respectsRingCon
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (h : TensorPBWNormalFormRespectsRingCon b) :
    Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k) := by
  intro x y hxy
  change UniversalEnvelopingAlgebra.mkAlgHom k L
      (TensorAlgebra.ι k x) =
    UniversalEnvelopingAlgebra.mkAlgHom k L
      (TensorAlgebra.ι k y) at hxy
  have hrel : UniversalEnvelopingAlgebra.ringCon k L
      (TensorAlgebra.ι k x) (TensorAlgebra.ι k y) :=
    Quotient.exact hxy
  exact tensorPBWNormalForm_comp_iota_injective b (h _ _ hrel)

theorem pbwMonomial_adjacent_swap
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    {word : List ι} (d : AdjacentInversion word) :
    pbwMonomial b word =
      pbwMonomial b d.swapped +
        ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
          (b.repr ⁅b d.left, b d.right⁆ i) •
            pbwMonomial b (d.bracketWord i) := by
  let P := pbwMonomial b d.pre
  let S := pbwMonomial b d.suffix
  have hswap := iota_mul_iota_swap (k := k) (L := L)
    (b d.left) (b d.right)
  have hbracket := iota_bracket_eq_sum_support b d.left d.right
  have hexpanded :
      pbwMonomial b (d.pre ++ d.left :: d.right :: d.suffix) =
        pbwMonomial b (d.pre ++ d.right :: d.left :: d.suffix) +
          ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ i) •
              pbwMonomial b (d.pre ++ i :: d.suffix) := by
    simp only [pbwMonomial_append, pbwMonomial_cons]
    change P * (UniversalEnvelopingAlgebra.ι k (b d.left) *
          (UniversalEnvelopingAlgebra.ι k (b d.right) * S)) =
      P * (UniversalEnvelopingAlgebra.ι k (b d.right) *
          (UniversalEnvelopingAlgebra.ι k (b d.left) * S)) + _
    rw [← mul_assoc (UniversalEnvelopingAlgebra.ι k (b d.left)),
      hswap, add_mul, mul_add]
    congr 1
    · rw [mul_assoc]
    · rw [hbracket, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_mul_assoc, mul_smul_comm]
  calc
    pbwMonomial b word =
        pbwMonomial b (d.pre ++ d.left :: d.right :: d.suffix) :=
      congrArg (pbwMonomial b) d.word_eq
    _ = pbwMonomial b (d.pre ++ d.right :: d.left :: d.suffix) +
          ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ i) •
              pbwMonomial b (d.pre ++ i :: d.suffix) := hexpanded
    _ = pbwMonomial b d.swapped +
          ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ i) •
              pbwMonomial b (d.bracketWord i) := rfl

/-- Evaluating the normal form gives back the original enveloping-algebra
monomial.  This is the spanning half of PBW in explicit retraction form. -/
theorem orderedMonomialLinearCombination_pbwNormalForm
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (word : List ι) :
    orderedMonomialLinearCombination b (pbwNormalForm b word) =
      pbwMonomial b word := by
  apply (InvImage.wf pbwWordMeasure Nat.lt_wfRel.wf).induction word
  intro word ih
  by_cases hword : word.Pairwise (· ≤ ·)
  · rw [pbwNormalForm_of_pairwise b hword]
    change (Finsupp.linearCombination k (orderedMonomial b))
      (Finsupp.single (⟨word, hword⟩ : PBWWord ι) 1) = _
    simp only [Finsupp.linearCombination_single, one_smul]
    rfl
  · rw [pbwNormalForm_of_not_pairwise b hword]
    let d := chosenAdjacentInversion word hword
    rw [map_add, map_sum]
    simp only [map_smul]
    have ihswap := ih d.swapped (by
      change pbwWordMeasure d.swapped < pbwWordMeasure word
      exact d.swapped_measure_lt)
    rw [ihswap]
    have ihbracket (i : ι) := ih (d.bracketWord i) (by
      change pbwWordMeasure (d.bracketWord i) < pbwWordMeasure word
      exact d.bracketWord_measure_lt i)
    have hsum :
        ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ i) •
              orderedMonomialLinearCombination b
                (pbwNormalForm b (d.bracketWord i)) =
          ∑ i ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ i) •
              pbwMonomial b (d.bracketWord i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ihbracket i]
    rw [hsum]
    exact (pbwMonomial_adjacent_swap b d).symm

/-- Evaluating the tensor-algebra normal form agrees with the canonical
quotient map to the universal enveloping algebra. -/
theorem orderedMonomialLinearCombination_comp_tensorPBWNormalForm
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    (orderedMonomialLinearCombination b).comp (tensorPBWNormalForm b) =
      (UniversalEnvelopingAlgebra.mkAlgHom k L).toLinearMap := by
  apply b.tensorAlgebra.ext
  intro word
  rw [LinearMap.comp_apply, tensorPBWNormalForm_basis_apply,
    orderedMonomialLinearCombination_pbwNormalForm]
  rw [tensorAlgebraBasis_apply_eq_list_prod]
  change pbwMonomial b word.toList =
    UniversalEnvelopingAlgebra.mkAlgHom k L
      ((word.toList.map fun i => TensorAlgebra.ι k (b i)).prod)
  rw [map_list_prod]
  rw [List.map_map]
  rfl

/-! ## The left action on PBW normal forms -/

/-- Left multiplication by a basis element, expressed on formal ordered
words through the PBW normal-form algorithm. -/
noncomputable def pbwLeftActionBasis {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) (i : ι) : Module.End k (PBWWord ι →₀ k) :=
  Finsupp.linearCombination k fun word => pbwNormalForm b (i :: word.1)

/-- Normalizing a word before adjoining a letter on the left does not
change the result.  The rightmost-reduction convention makes this a direct
well-founded induction. -/
theorem pbwLeftActionBasis_pbwNormalForm
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i : ι) (word : List ι) :
    pbwLeftActionBasis b i (pbwNormalForm b word) =
      pbwNormalForm b (i :: word) := by
  apply (InvImage.wf pbwWordMeasure Nat.lt_wfRel.wf).induction word
  intro word ih
  by_cases hword : word.Pairwise (· ≤ ·)
  · rw [pbwNormalForm_of_pairwise b hword, pbwLeftActionBasis,
      Finsupp.linearCombination_single, one_smul]
  · let d := chosenAdjacentInversion word hword
    rw [pbwNormalForm_of_not_pairwise b hword,
      pbwNormalForm_cons_of_not_pairwise b i word hword]
    change pbwLeftActionBasis b i
        (pbwNormalForm b d.swapped +
          ∑ j ∈ (b.repr ⁅b d.left, b d.right⁆).support,
            (b.repr ⁅b d.left, b d.right⁆ j) •
              pbwNormalForm b (d.bracketWord j)) = _
    rw [map_add, map_sum]
    simp only [map_smul]
    rw [ih d.swapped d.swapped_measure_lt]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih (d.bracketWord j) (d.bracketWord_measure_lt j)]

/-- Two successive basis actions on an ordered-word vector are the normal
form of the corresponding two-letter prefix. -/
theorem pbwLeftActionBasis_comp_single
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i j : ι) (word : PBWWord ι) :
    pbwLeftActionBasis b i
        (pbwLeftActionBasis b j (Finsupp.single word 1)) =
      pbwNormalForm b (i :: j :: word.1) := by
  have hinner : pbwLeftActionBasis b j (Finsupp.single word 1) =
      pbwNormalForm b (j :: word.1) := by
    rw [pbwLeftActionBasis, Finsupp.linearCombination_single, one_smul]
  rw [hinner, pbwLeftActionBasis_pbwNormalForm]

/-- A basis action raises the formal PBW filtration by at most one. -/
theorem pbwLeftActionBasis_mem_filtration
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i : ι) {n : ℕ} {z : PBWWord ι →₀ k}
    (hz : z ∈ pbwNormalFormFiltration (k := k) n) :
    pbwLeftActionBasis b i z ∈
      pbwNormalFormFiltration (k := k) (n + 1) := by
  rw [pbwNormalFormFiltration, Finsupp.supported_eq_span_single] at hz
  refine Submodule.span_induction (p := fun z _ =>
      pbwLeftActionBasis b i z ∈
        pbwNormalFormFiltration (k := k) (n + 1)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨word, hword, rfl⟩
    change word.1.length ≤ n at hword
    rw [pbwLeftActionBasis, Finsupp.linearCombination_single, one_smul]
    exact pbwNormalFormFiltration_mono
      (m := (i :: word.1).length) (n := n + 1)
      (by simp only [List.length_cons]; omega)
      (pbwNormalForm_mem_filtration b (i :: word.1))
  · exact map_zero (pbwLeftActionBasis b i) ▸ Submodule.zero_mem _
  · intro x y hx hy hxi hyi
    rw [map_add]
    exact Submodule.add_mem _ hxi hyi
  · intro r x hx hxi
    rw [map_smul]
    exact Submodule.smul_mem _ r hxi

theorem orderedMonomialLinearCombination_pbwLeftActionBasis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (i : ι)
    (z : PBWWord ι →₀ k) :
    orderedMonomialLinearCombination b (pbwLeftActionBasis b i z) =
      UniversalEnvelopingAlgebra.ι k (b i) *
        orderedMonomialLinearCombination b z := by
  classical
  induction z using Finsupp.induction with
  | zero => simp [pbwLeftActionBasis]
  | @single_add word r z hword hz ih =>
      have hsingle : orderedMonomialLinearCombination b
          (pbwLeftActionBasis b i (Finsupp.single word r)) =
        UniversalEnvelopingAlgebra.ι k (b i) *
          orderedMonomialLinearCombination b (Finsupp.single word r) := by
        rw [pbwLeftActionBasis, Finsupp.linearCombination_single,
          map_smul, orderedMonomialLinearCombination_pbwNormalForm]
        rw [pbwMonomial_cons]
        simp [orderedMonomialLinearCombination, orderedMonomial]
      simp only [map_add, hsingle, ih, mul_add]

/-- The linear left action of the Lie algebra on formal ordered PBW words. -/
noncomputable def pbwLeftAction {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : L →ₗ[k] Module.End k (PBWWord ι →₀ k) :=
  b.constr k (pbwLeftActionBasis b)

@[simp]
theorem pbwLeftAction_apply_basis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (i : ι) :
    pbwLeftAction b (b i) = pbwLeftActionBasis b i := by
  exact b.constr_basis k _ i

/-- An arbitrary Lie-algebra action raises the formal PBW filtration by at
most one. -/
theorem pbwLeftAction_mem_filtration
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (x : L) {n : ℕ} {z : PBWWord ι →₀ k}
    (hz : z ∈ pbwNormalFormFiltration (k := k) n) :
    pbwLeftAction b x z ∈
      pbwNormalFormFiltration (k := k) (n + 1) := by
  have hrecon :
      ∑ i ∈ (b.repr x).support, (b.repr x i) • b i = x := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      b.linearCombination_repr x
  rw [← hrecon, map_sum]
  simp_rw [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [pbwLeftAction_apply_basis]
  exact pbwLeftActionBasis_mem_filtration b i hz

/-- Expand the action of a basis-vector bracket in structure
coefficients. -/
theorem pbwLeftAction_bracket_single
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i j : ι) (word : PBWWord ι) :
    pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1) =
      ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
        (b.repr ⁅b i, b j⁆ l) •
          pbwNormalForm b (l :: word.1) := by
  have hrecon :
      ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
          (b.repr ⁅b i, b j⁆ l) • b l = ⁅b i, b j⁆ := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      b.linearCombination_repr ⁅b i, b j⁆
  calc
    pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1) =
        pbwLeftAction b
          (∑ l ∈ (b.repr ⁅b i, b j⁆).support,
            (b.repr ⁅b i, b j⁆ l) • b l)
          (Finsupp.single word 1) := congrArg
            (fun x => pbwLeftAction b x (Finsupp.single word 1)) hrecon.symm
    _ = ∑ l ∈ (b.repr ⁅b i, b j⁆).support,
          (b.repr ⁅b i, b j⁆ l) •
            pbwNormalForm b (l :: word.1) := by
      rw [map_sum]
      simp only [map_smul]
      simp_rw [LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      rw [pbwLeftAction_apply_basis, pbwLeftActionBasis,
        Finsupp.linearCombination_single, one_smul]

/-- The PBW Lie-action identity at an ordered word when the smaller of two
basis letters can already be adjoined in order. -/
theorem pbwLeftAction_lie_single_of_lt_of_cons_pairwise
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i j : ι) (word : PBWWord ι) (hij : i < j)
    (hiword : (i :: word.1).Pairwise (· ≤ ·)) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
        (Finsupp.single word 1) =
      pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1) := by
  have hswap := pbwNormalForm_cons_cons_of_lt b j i word.1 hij hiword
  have hbracketSwap :
      (∑ l ∈ (b.repr ⁅b j, b i⁆).support,
          (b.repr ⁅b j, b i⁆ l) • pbwNormalForm b (l :: word.1)) =
        -(∑ l ∈ (b.repr ⁅b i, b j⁆).support,
          (b.repr ⁅b i, b j⁆ l) • pbwNormalForm b (l :: word.1)) := by
    rw [← pbwLeftAction_bracket_single b j i word,
      ← pbwLeftAction_bracket_single b i j word]
    have hskew : ⁅b j, b i⁆ = -⁅b i, b j⁆ :=
      (lie_skew (b j) (b i)).symm
    rw [hskew, map_neg]
    rfl
  rw [pbwLeftAction_apply_basis, pbwLeftAction_apply_basis]
  change pbwLeftActionBasis b i
        (pbwLeftActionBasis b j (Finsupp.single word 1)) -
      pbwLeftActionBasis b j
        (pbwLeftActionBasis b i (Finsupp.single word 1)) = _
  rw [pbwLeftActionBasis_comp_single, pbwLeftActionBasis_comp_single,
    pbwLeftAction_bracket_single]
  rw [hswap, hbracketSwap]
  abel

/-- The symmetric version of the preceding triangular case. -/
theorem pbwLeftAction_lie_single_of_gt_of_cons_pairwise
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i j : ι) (word : PBWWord ι) (hji : j < i)
    (hjword : (j :: word.1).Pairwise (· ≤ ·)) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
        (Finsupp.single word 1) =
      pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1) := by
  have h := pbwLeftAction_lie_single_of_lt_of_cons_pairwise
    b j i word hji hjword
  let Ai := pbwLeftAction b (b i)
  let Aj := pbwLeftAction b (b j)
  let z : PBWWord ι →₀ k := Finsupp.single word 1
  calc
    ⁅Ai, Aj⁆ z = -⁅Aj, Ai⁆ z := by
      have hskew : ⁅Ai, Aj⁆ = -⁅Aj, Ai⁆ :=
        (lie_skew Ai Aj).symm
      rw [hskew]
      rfl
    _ = -(pbwLeftAction b ⁅b j, b i⁆ z) := congrArg Neg.neg h
    _ = pbwLeftAction b ⁅b i, b j⁆ z := by
      have hskew : ⁅b i, b j⁆ = -⁅b j, b i⁆ :=
        (lie_skew (b i) (b j)).symm
      rw [hskew, map_neg]
      rfl

/-- The local Lie-action identity is automatic for equal basis letters. -/
theorem pbwLeftAction_lie_single_self
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i : ι) (word : PBWWord ι) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b i)⁆
        (Finsupp.single word 1) =
      pbwLeftAction b ⁅b i, b i⁆ (Finsupp.single word 1) := by
  have hself : ⁅b i, b i⁆ = 0 := lie_self (b i)
  rw [hself, map_zero]
  change ((pbwLeftAction b (b i) * pbwLeftAction b (b i) -
    pbwLeftAction b (b i) * pbwLeftAction b (b i))
      (Finsupp.single word 1)) = 0
  change pbwLeftAction b (b i)
      (pbwLeftAction b (b i) (Finsupp.single word 1)) -
    pbwLeftAction b (b i)
      (pbwLeftAction b (b i) (Finsupp.single word 1)) = 0
  exact sub_self _

/-- Bilinearity reduces the Lie-action identity at one fixed formal vector
to pairs of basis vectors. -/
theorem pbwLeftAction_lie_at_of_basis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (z : PBWWord ι →₀ k)
    (h : ∀ i j : ι,
      ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆ z =
        pbwLeftAction b ⁅b i, b j⁆ z) :
    ∀ x y : L, ⁅pbwLeftAction b x, pbwLeftAction b y⁆ z =
      pbwLeftAction b ⁅x, y⁆ z := by
  intro x y
  let left : L →ₗ[k] (PBWWord ι →₀ k) := {
    toFun := fun a => ⁅pbwLeftAction b a, pbwLeftAction b y⁆ z
    map_add' := fun a a' => by
      rw [map_add]
      change (pbwLeftAction b a + pbwLeftAction b a')
          (pbwLeftAction b y z) -
        pbwLeftAction b y
          ((pbwLeftAction b a + pbwLeftAction b a') z) = _
      simp only [LinearMap.add_apply, map_add]
      change pbwLeftAction b a (pbwLeftAction b y z) +
          pbwLeftAction b a' (pbwLeftAction b y z) -
        (pbwLeftAction b y (pbwLeftAction b a z) +
          pbwLeftAction b y (pbwLeftAction b a' z)) =
        (pbwLeftAction b a (pbwLeftAction b y z) -
          pbwLeftAction b y (pbwLeftAction b a z)) +
        (pbwLeftAction b a' (pbwLeftAction b y z) -
          pbwLeftAction b y (pbwLeftAction b a' z))
      abel
    map_smul' := fun r a => by
      rw [map_smul]
      change (r • pbwLeftAction b a) (pbwLeftAction b y z) -
        pbwLeftAction b y ((r • pbwLeftAction b a) z) = _
      simp only [LinearMap.smul_apply, map_smul]
      exact (smul_sub r _ _).symm }
  let right : L →ₗ[k] (PBWWord ι →₀ k) := {
    toFun := fun a => pbwLeftAction b ⁅a, y⁆ z
    map_add' := fun a a' => by rw [add_lie, map_add, LinearMap.add_apply]
    map_smul' := fun r a => by
      rw [smul_lie, map_smul, LinearMap.smul_apply]
      simp only [RingHom.id_apply] }
  have hxy : left = right := by
    apply b.ext
    intro i
    let lefti : L →ₗ[k] (PBWWord ι →₀ k) := {
      toFun := fun c => ⁅pbwLeftAction b (b i), pbwLeftAction b c⁆ z
      map_add' := fun c c' => by
        rw [map_add]
        change pbwLeftAction b (b i)
            ((pbwLeftAction b c + pbwLeftAction b c') z) -
          (pbwLeftAction b c + pbwLeftAction b c')
            (pbwLeftAction b (b i) z) = _
        simp only [LinearMap.add_apply, map_add]
        change pbwLeftAction b (b i) (pbwLeftAction b c z) +
            pbwLeftAction b (b i) (pbwLeftAction b c' z) -
          (pbwLeftAction b c (pbwLeftAction b (b i) z) +
            pbwLeftAction b c' (pbwLeftAction b (b i) z)) =
          (pbwLeftAction b (b i) (pbwLeftAction b c z) -
            pbwLeftAction b c (pbwLeftAction b (b i) z)) +
          (pbwLeftAction b (b i) (pbwLeftAction b c' z) -
            pbwLeftAction b c' (pbwLeftAction b (b i) z))
        abel
      map_smul' := fun r c => by
        rw [map_smul]
        change pbwLeftAction b (b i) ((r • pbwLeftAction b c) z) -
          (r • pbwLeftAction b c) (pbwLeftAction b (b i) z) = _
        simp only [LinearMap.smul_apply, map_smul]
        exact (smul_sub r _ _).symm }
    let righti : L →ₗ[k] (PBWWord ι →₀ k) := {
      toFun := fun c => pbwLeftAction b ⁅b i, c⁆ z
      map_add' := fun c c' => by rw [lie_add, map_add, LinearMap.add_apply]
      map_smul' := fun r c => by
        rw [lie_smul, map_smul, LinearMap.smul_apply]
        simp only [RingHom.id_apply] }
    have hi : lefti = righti := by
      apply b.ext
      intro j
      exact h i j
    exact LinearMap.congr_fun hi y
  exact LinearMap.congr_fun hxy x

/-- The Lie-action identity on the vacuum vector. -/
theorem pbwLeftAction_lie_vacuum
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (x y : L) :
    ⁅pbwLeftAction b x, pbwLeftAction b y⁆
        (Finsupp.single (emptyPBWWord ι) 1) =
      pbwLeftAction b ⁅x, y⁆
        (Finsupp.single (emptyPBWWord ι) 1) := by
  apply pbwLeftAction_lie_at_of_basis b
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · apply pbwLeftAction_lie_single_of_lt_of_cons_pairwise b i j
      (emptyPBWWord ι) hij
    simp [emptyPBWWord]
  · subst j
    exact pbwLeftAction_lie_single_self b i (emptyPBWWord ι)
  · apply pbwLeftAction_lie_single_of_gt_of_cons_pairwise b i j
      (emptyPBWWord ι) hij
    simp [emptyPBWWord]

@[simp]
theorem pbwLeftAction_basis_vacuum
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (i : ι) :
    pbwLeftAction b (b i) (Finsupp.single (emptyPBWWord ι) 1) =
      Finsupp.single (singletonPBWWord i) 1 := by
  rw [pbwLeftAction_apply_basis, pbwLeftActionBasis,
    Finsupp.linearCombination_single, one_smul,
    pbwNormalForm_of_pairwise]
  rfl

/-- The PBW Lie identity at a fixed formal combination. -/
def PBWLieIdentityAt
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (z : PBWWord ι →₀ k) : Prop :=
  ∀ x y : L, ⁅pbwLeftAction b x, pbwLeftAction b y⁆ z =
    pbwLeftAction b ⁅x, y⁆ z

theorem PBWLieIdentityAt.add
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    {z z' : PBWWord ι →₀ k}
    (hz : PBWLieIdentityAt b z) (hz' : PBWLieIdentityAt b z') :
    PBWLieIdentityAt b (z + z') := by
  intro x y
  have hzx := hz x y
  have hz'x := hz' x y
  change pbwLeftAction b x (pbwLeftAction b y z) -
    pbwLeftAction b y (pbwLeftAction b x z) =
      pbwLeftAction b ⁅x, y⁆ z at hzx
  change pbwLeftAction b x (pbwLeftAction b y z') -
    pbwLeftAction b y (pbwLeftAction b x z') =
      pbwLeftAction b ⁅x, y⁆ z' at hz'x
  change pbwLeftAction b x (pbwLeftAction b y (z + z')) -
    pbwLeftAction b y (pbwLeftAction b x (z + z')) =
      pbwLeftAction b ⁅x, y⁆ (z + z')
  simp only [map_add]
  rw [show pbwLeftAction b x (pbwLeftAction b y z) +
          pbwLeftAction b x (pbwLeftAction b y z') -
        (pbwLeftAction b y (pbwLeftAction b x z) +
          pbwLeftAction b y (pbwLeftAction b x z')) =
      (pbwLeftAction b x (pbwLeftAction b y z) -
        pbwLeftAction b y (pbwLeftAction b x z)) +
      (pbwLeftAction b x (pbwLeftAction b y z') -
        pbwLeftAction b y (pbwLeftAction b x z')) by abel,
    hzx, hz'x]

/-- The unique three-letter critical overlap.  Here `k` lies below both
`i` and `j`; expanding the two rightmost reductions leaves precisely the
Lie Jacobi identity. -/
theorem pbwLeftAction_lie_singleton_critical
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (k₀ i j : ι) (hki : k₀ < i) (hij : i < j) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
        (Finsupp.single (singletonPBWWord k₀) 1) =
      pbwLeftAction b ⁅b i, b j⁆
        (Finsupp.single (singletonPBWWord k₀) 1) := by
  have hkj : k₀ < j := hki.trans hij
  let v : PBWWord ι →₀ k := Finsupp.single (emptyPBWWord ι) 1
  let Ai := pbwLeftAction b (b i)
  let Aj := pbwLeftAction b (b j)
  let Ak := pbwLeftAction b (b k₀)
  let Aik := pbwLeftAction b ⁅b i, b k₀⁆
  let Ajk := pbwLeftAction b ⁅b j, b k₀⁆
  let Aij := pbwLeftAction b ⁅b i, b j⁆
  have hkv : Ak v = Finsupp.single (singletonPBWWord k₀) 1 := by
    exact pbwLeftAction_basis_vacuum b k₀
  have hiv : Ai v = Finsupp.single (singletonPBWWord i) 1 := by
    exact pbwLeftAction_basis_vacuum b i
  have hjv : Aj v = Finsupp.single (singletonPBWWord j) 1 := by
    exact pbwLeftAction_basis_vacuum b j
  have hjk : Aj (Ak v) = Ak (Aj v) + Ajk v := by
    have h := pbwLeftAction_lie_vacuum b (b j) (b k₀)
    change Aj (Ak v) - Ak (Aj v) = Ajk v at h
    rw [← h]
    abel
  have hik : Ai (Ak v) = Ak (Ai v) + Aik v := by
    have h := pbwLeftAction_lie_vacuum b (b i) (b k₀)
    change Ai (Ak v) - Ak (Ai v) = Aik v at h
    rw [← h]
    abel
  have hikj : Ai (Ak (Aj v)) = Ak (Ai (Aj v)) + Aik (Aj v) := by
    have h := pbwLeftAction_lie_single_of_gt_of_cons_pairwise
      b i k₀ (singletonPBWWord j) hki (by
        simp [singletonPBWWord, hkj.le])
    rw [← hjv] at h
    change Ai (Ak (Aj v)) - Ak (Ai (Aj v)) = Aik (Aj v) at h
    rw [← h]
    abel
  have hjki : Aj (Ak (Ai v)) = Ak (Aj (Ai v)) + Ajk (Ai v) := by
    have h := pbwLeftAction_lie_single_of_gt_of_cons_pairwise
      b j k₀ (singletonPBWWord i) hkj (by
        simp [singletonPBWWord, hki.le])
    rw [← hiv] at h
    change Aj (Ak (Ai v)) - Ak (Aj (Ai v)) = Ajk (Ai v) at h
    rw [← h]
    abel
  have hijv : Ai (Aj v) - Aj (Ai v) = Aij v := by
    have h := pbwLeftAction_lie_vacuum b (b i) (b j)
    exact h
  have hcomm₁ : Aik (Aj v) - Aj (Aik v) =
      pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ v := by
    exact pbwLeftAction_lie_vacuum b ⁅b i, b k₀⁆ (b j)
  have hcomm₂ : Ai (Ajk v) - Ajk (Ai v) =
      pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ v := by
    exact pbwLeftAction_lie_vacuum b (b i) ⁅b j, b k₀⁆
  have hcomm₃ : Aij (Ak v) - Ak (Aij v) =
      pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ v := by
    exact pbwLeftAction_lie_vacuum b ⁅b i, b j⁆ (b k₀)
  have hjacobi :
      ⁅⁅b i, b k₀⁆, b j⁆ + ⁅b i, ⁅b j, b k₀⁆⁆ =
        ⁅⁅b i, b j⁆, b k₀⁆ := by
    have h := lie_jacobi (b i) (b j) (b k₀)
    rw [show ⁅⁅b i, b k₀⁆, b j⁆ = -⁅b j, ⁅b i, b k₀⁆⁆ from
      (lie_skew ⁅b i, b k₀⁆ (b j)).symm]
    rw [show ⁅b j, ⁅b k₀, b i⁆⁆ = -⁅b j, ⁅b i, b k₀⁆⁆ by
      rw [show ⁅b k₀, b i⁆ = -⁅b i, b k₀⁆ from
        (lie_skew (b k₀) (b i)).symm, lie_neg]] at h
    rw [show ⁅⁅b i, b j⁆, b k₀⁆ = -⁅b k₀, ⁅b i, b j⁆⁆ from
      (lie_skew ⁅b i, b j⁆ (b k₀)).symm]
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_assoc, add_comm, add_left_comm] using h
  rw [← hkv]
  change Ai (Aj (Ak v)) - Aj (Ai (Ak v)) = Aij (Ak v)
  rw [hjk, map_add, hikj, hik, map_add, hjki]
  calc
    (Ak (Ai (Aj v)) + Aik (Aj v) + Ai (Ajk v)) -
        (Ak (Aj (Ai v)) + Ajk (Ai v) + Aj (Aik v)) =
      Ak (Ai (Aj v) - Aj (Ai v)) +
        (Aik (Aj v) - Aj (Aik v)) +
        (Ai (Ajk v) - Ajk (Ai v)) := by
          rw [map_sub]
          abel
    _ = Ak (Aij v) +
        pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ v +
        pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ v := by
      rw [hijv, hcomm₁, hcomm₂]
    _ = Ak (Aij v) +
        pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ v := by
      rw [add_assoc]
      congr 1
      calc
        pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ v +
            pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ v =
          pbwLeftAction b
            (⁅⁅b i, b k₀⁆, b j⁆ + ⁅b i, ⁅b j, b k₀⁆⁆) v := by
              rw [map_add, LinearMap.add_apply]
        _ = pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ v := by rw [hjacobi]
    _ = Aij (Ak v) := by
      rw [← hcomm₃]
      abel

/-- Abstract form of the critical-overlap calculation.  The identity at
`z`, together with the two overlaps obtained after applying `i` and `j`,
implies the identity at `A_k z`. -/
theorem pbwLeftAction_lie_critical_of
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (k₀ i j : ι) (z : PBWWord ι →₀ k)
    (hz : PBWLieIdentityAt b z)
    (hikj :
      ⁅pbwLeftAction b (b i), pbwLeftAction b (b k₀)⁆
          (pbwLeftAction b (b j) z) =
        pbwLeftAction b ⁅b i, b k₀⁆
          (pbwLeftAction b (b j) z))
    (hjki :
      ⁅pbwLeftAction b (b j), pbwLeftAction b (b k₀)⁆
          (pbwLeftAction b (b i) z) =
        pbwLeftAction b ⁅b j, b k₀⁆
          (pbwLeftAction b (b i) z)) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
        (pbwLeftAction b (b k₀) z) =
      pbwLeftAction b ⁅b i, b j⁆
        (pbwLeftAction b (b k₀) z) := by
  let Ai := pbwLeftAction b (b i)
  let Aj := pbwLeftAction b (b j)
  let Ak := pbwLeftAction b (b k₀)
  let Aik := pbwLeftAction b ⁅b i, b k₀⁆
  let Ajk := pbwLeftAction b ⁅b j, b k₀⁆
  let Aij := pbwLeftAction b ⁅b i, b j⁆
  have hjk : Aj (Ak z) = Ak (Aj z) + Ajk z := by
    have h := hz (b j) (b k₀)
    change Aj (Ak z) - Ak (Aj z) = Ajk z at h
    rw [← h]
    abel
  have hik : Ai (Ak z) = Ak (Ai z) + Aik z := by
    have h := hz (b i) (b k₀)
    change Ai (Ak z) - Ak (Ai z) = Aik z at h
    rw [← h]
    abel
  have hikj' : Ai (Ak (Aj z)) = Ak (Ai (Aj z)) + Aik (Aj z) := by
    change Ai (Ak (Aj z)) - Ak (Ai (Aj z)) = Aik (Aj z) at hikj
    rw [← hikj]
    abel
  have hjki' : Aj (Ak (Ai z)) = Ak (Aj (Ai z)) + Ajk (Ai z) := by
    change Aj (Ak (Ai z)) - Ak (Aj (Ai z)) = Ajk (Ai z) at hjki
    rw [← hjki]
    abel
  have hijz : Ai (Aj z) - Aj (Ai z) = Aij z := hz (b i) (b j)
  have hcomm₁ : Aik (Aj z) - Aj (Aik z) =
      pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ z :=
    hz ⁅b i, b k₀⁆ (b j)
  have hcomm₂ : Ai (Ajk z) - Ajk (Ai z) =
      pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ z :=
    hz (b i) ⁅b j, b k₀⁆
  have hcomm₃ : Aij (Ak z) - Ak (Aij z) =
      pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ z :=
    hz ⁅b i, b j⁆ (b k₀)
  have hjacobi :
      ⁅⁅b i, b k₀⁆, b j⁆ + ⁅b i, ⁅b j, b k₀⁆⁆ =
        ⁅⁅b i, b j⁆, b k₀⁆ := by
    have h := lie_jacobi (b i) (b j) (b k₀)
    rw [show ⁅⁅b i, b k₀⁆, b j⁆ = -⁅b j, ⁅b i, b k₀⁆⁆ from
      (lie_skew ⁅b i, b k₀⁆ (b j)).symm]
    rw [show ⁅b j, ⁅b k₀, b i⁆⁆ = -⁅b j, ⁅b i, b k₀⁆⁆ by
      rw [show ⁅b k₀, b i⁆ = -⁅b i, b k₀⁆ from
        (lie_skew (b k₀) (b i)).symm, lie_neg]] at h
    rw [show ⁅⁅b i, b j⁆, b k₀⁆ = -⁅b k₀, ⁅b i, b j⁆⁆ from
      (lie_skew ⁅b i, b j⁆ (b k₀)).symm]
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_assoc, add_comm, add_left_comm] using h
  change Ai (Aj (Ak z)) - Aj (Ai (Ak z)) = Aij (Ak z)
  rw [hjk, map_add, hikj', hik, map_add, hjki']
  calc
    (Ak (Ai (Aj z)) + Aik (Aj z) + Ai (Ajk z)) -
        (Ak (Aj (Ai z)) + Ajk (Ai z) + Aj (Aik z)) =
      Ak (Ai (Aj z) - Aj (Ai z)) +
        (Aik (Aj z) - Aj (Aik z)) +
        (Ai (Ajk z) - Ajk (Ai z)) := by
          rw [map_sub]
          abel
    _ = Ak (Aij z) +
        pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ z +
        pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ z := by
      rw [hijz, hcomm₁, hcomm₂]
    _ = Ak (Aij z) +
        pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ z := by
      rw [add_assoc]
      congr 1
      calc
        pbwLeftAction b ⁅⁅b i, b k₀⁆, b j⁆ z +
            pbwLeftAction b ⁅b i, ⁅b j, b k₀⁆⁆ z =
          pbwLeftAction b
            (⁅⁅b i, b k₀⁆, b j⁆ + ⁅b i, ⁅b j, b k₀⁆⁆) z := by
              rw [map_add, LinearMap.add_apply]
        _ = pbwLeftAction b ⁅⁅b i, b j⁆, b k₀⁆ z := by rw [hjacobi]
    _ = Aij (Ak z) := by
      rw [← hcomm₃]
      abel

/-- The Lie-action identity on every one-letter ordered word. -/
theorem pbwLeftAction_lie_singleton_basis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (i j k₀ : ι) :
    ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
        (Finsupp.single (singletonPBWWord k₀) 1) =
      pbwLeftAction b ⁅b i, b j⁆
        (Finsupp.single (singletonPBWWord k₀) 1) := by
  rcases lt_trichotomy i j with hij | hij | hji
  · by_cases hik : i ≤ k₀
    · apply pbwLeftAction_lie_single_of_lt_of_cons_pairwise b i j
        (singletonPBWWord k₀) hij
      simp [singletonPBWWord, hik]
    · exact pbwLeftAction_lie_singleton_critical b k₀ i j
        (lt_of_not_ge hik) hij
  · subst j
    exact pbwLeftAction_lie_single_self b i (singletonPBWWord k₀)
  · by_cases hjk : j ≤ k₀
    · apply pbwLeftAction_lie_single_of_gt_of_cons_pairwise b i j
        (singletonPBWWord k₀) hji
      simp [singletonPBWWord, hjk]
    · have h := pbwLeftAction_lie_singleton_critical b k₀ j i
        (lt_of_not_ge hjk) hji
      let Ai := pbwLeftAction b (b i)
      let Aj := pbwLeftAction b (b j)
      let z : PBWWord ι →₀ k :=
        Finsupp.single (singletonPBWWord k₀) 1
      calc
        ⁅Ai, Aj⁆ z = -⁅Aj, Ai⁆ z := by
          have hskew : ⁅Ai, Aj⁆ = -⁅Aj, Ai⁆ :=
            (lie_skew Ai Aj).symm
          rw [hskew]
          rfl
        _ = -(pbwLeftAction b ⁅b j, b i⁆ z) := congrArg Neg.neg h
        _ = pbwLeftAction b ⁅b i, b j⁆ z := by
          have hskew : ⁅b i, b j⁆ = -⁅b j, b i⁆ :=
            (lie_skew (b i) (b j)).symm
          rw [hskew, map_neg]
          rfl

/-- A degree-bounded basis check gives the Lie identity on the whole
formal PBW filtration. -/
theorem pbwLieIdentityAt_of_filtration
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (n : ℕ)
    (h : ∀ (word : PBWWord ι), word.1.length ≤ n →
      ∀ i j : ι,
        ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
            (Finsupp.single word 1) =
          pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1))
    {z : PBWWord ι →₀ k}
    (hz : z ∈ pbwNormalFormFiltration (k := k) n) :
    PBWLieIdentityAt b z := by
  rw [pbwNormalFormFiltration, Finsupp.supported_eq_span_single] at hz
  refine Submodule.span_induction (p := fun z _ => PBWLieIdentityAt b z)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨word, hword, rfl⟩
    change word.1.length ≤ n at hword
    exact pbwLeftAction_lie_at_of_basis b _ (h word hword)
  · intro x y
    change (pbwLeftAction b x * pbwLeftAction b y -
        pbwLeftAction b y * pbwLeftAction b x) 0 =
      pbwLeftAction b ⁅x, y⁆ 0
    simp only [map_zero]
  · intro z z' hz hz' hzLie hz'Lie x y
    change (pbwLeftAction b x * pbwLeftAction b y -
          pbwLeftAction b y * pbwLeftAction b x) (z + z') =
      pbwLeftAction b ⁅x, y⁆ (z + z')
    simp only [map_add]
    change (pbwLeftAction b x (pbwLeftAction b y z) -
          pbwLeftAction b y (pbwLeftAction b x z)) +
        (pbwLeftAction b x (pbwLeftAction b y z') -
          pbwLeftAction b y (pbwLeftAction b x z')) =
      pbwLeftAction b ⁅x, y⁆ z + pbwLeftAction b ⁅x, y⁆ z'
    have hzxy := hzLie x y
    have hz'xy := hz'Lie x y
    change pbwLeftAction b x (pbwLeftAction b y z) -
      pbwLeftAction b y (pbwLeftAction b x z) =
        pbwLeftAction b ⁅x, y⁆ z at hzxy
    change pbwLeftAction b x (pbwLeftAction b y z') -
      pbwLeftAction b y (pbwLeftAction b x z') =
        pbwLeftAction b ⁅x, y⁆ z' at hz'xy
    rw [hzxy, hz'xy]
  · intro r z hz hzLie x y
    change (pbwLeftAction b x * pbwLeftAction b y -
          pbwLeftAction b y * pbwLeftAction b x) (r • z) =
      pbwLeftAction b ⁅x, y⁆ (r • z)
    simp only [map_smul]
    change r • (pbwLeftAction b x (pbwLeftAction b y z) -
        pbwLeftAction b y (pbwLeftAction b x z)) =
      r • pbwLeftAction b ⁅x, y⁆ z
    have hzxy := hzLie x y
    change pbwLeftAction b x (pbwLeftAction b y z) -
      pbwLeftAction b y (pbwLeftAction b x z) =
        pbwLeftAction b ⁅x, y⁆ z at hzxy
    rw [hzxy]

/-- Induction on ordered-word degree closes all PBW critical overlaps. -/
theorem pbwLeftAction_lie_single_degree
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (n : ℕ) :
    ∀ (word : PBWWord ι), word.1.length ≤ n →
      ∀ i j : ι,
        ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
            (Finsupp.single word 1) =
          pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1) := by
  induction n with
  | zero =>
      intro word hword i j
      have hnil : word = emptyPBWWord ι := by
        apply Subtype.ext
        exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hword)
      subst word
      exact pbwLeftAction_lie_vacuum b (b i) (b j)
  | succ n ih =>
      intro word hword i j
      by_cases hsmall : word.1.length ≤ n
      · exact ih word hsmall i j
      have hlength : word.1.length = n + 1 := by omega
      obtain ⟨k₀, tail, hwordList⟩ := List.exists_cons_of_length_pos
        (show 0 < word.1.length by omega)
      have hordered : (k₀ :: tail).Pairwise (· ≤ ·) := by
        rw [← hwordList]
        exact word.2
      have htailLength : tail.length = n := by
        rw [hwordList] at hlength
        simp only [List.length_cons] at hlength
        omega
      let tailWord : PBWWord ι := ⟨tail, hordered.of_cons⟩
      let z : PBWWord ι →₀ k := Finsupp.single tailWord 1
      have hzmem : z ∈ pbwNormalFormFiltration (k := k) n := by
        apply single_mem_pbwNormalFormFiltration
        exact htailLength.le
      have hzLie : PBWLieIdentityAt b z :=
        pbwLieIdentityAt_of_filtration b n ih hzmem
      have haction (a q : ι) (hka : k₀ < a) (hkq : k₀ < q) :
          ⁅pbwLeftAction b (b q), pbwLeftAction b (b k₀)⁆
              (pbwLeftAction b (b a) z) =
            pbwLeftAction b ⁅b q, b k₀⁆
              (pbwLeftAction b (b a) z) := by
        let top : PBWWord ι := sortedPBWWord (a :: tail)
        let lower : PBWWord ι →₀ k :=
          pbwLeftAction b (b a) z - Finsupp.single top 1
        have hactionForm : pbwLeftAction b (b a) z =
            pbwNormalForm b (a :: tail) := by
          rw [pbwLeftAction_apply_basis, pbwLeftActionBasis]
          change (Finsupp.linearCombination k fun word =>
            pbwNormalForm b (a :: word.1)) (Finsupp.single tailWord 1) = _
          rw [Finsupp.linearCombination_single, one_smul]
        have hlower : lower ∈ pbwNormalFormFiltration (k := k) n := by
          dsimp [lower]
          rw [hactionForm]
          have htop := pbwNormalForm_sub_sorted_mem_filtration b (a :: tail)
          simpa only [List.length_cons, Nat.add_sub_cancel, htailLength] using htop
        have htopOrdered : (k₀ :: top.1).Pairwise (· ≤ ·) := by
          apply List.pairwise_cons.2
          refine ⟨?_, top.2⟩
          intro x hx
          have hx' : x = a ∨ x ∈ tail := by
            have hp := List.mergeSort_perm (a :: tail) (· ≤ ·)
            have : x ∈ a :: tail := hp.mem_iff.mp hx
            simpa only [List.mem_cons] using this
          rcases hx' with rfl | hx'
          · exact hka.le
          · exact (List.pairwise_cons.1 hordered).1 x hx'
        have htopIdentity :=
          pbwLeftAction_lie_single_of_gt_of_cons_pairwise
            b q k₀ top hkq htopOrdered
        have hlowerIdentity :=
          (pbwLieIdentityAt_of_filtration b n ih hlower) (b q) (b k₀)
        have hdecomp : pbwLeftAction b (b a) z =
            Finsupp.single top 1 + lower := by
          dsimp [lower]
          abel
        rw [hdecomp]
        change pbwLeftAction b (b q)
              (pbwLeftAction b (b k₀)
                (Finsupp.single top 1 + lower)) -
            pbwLeftAction b (b k₀)
              (pbwLeftAction b (b q)
                (Finsupp.single top 1 + lower)) =
          pbwLeftAction b ⁅b q, b k₀⁆
            (Finsupp.single top 1 + lower)
        simp only [map_add]
        have htopIdentity' := htopIdentity
        have hlowerIdentity' := hlowerIdentity
        change pbwLeftAction b (b q)
              (pbwLeftAction b (b k₀) (Finsupp.single top 1)) -
            pbwLeftAction b (b k₀)
              (pbwLeftAction b (b q) (Finsupp.single top 1)) =
          pbwLeftAction b ⁅b q, b k₀⁆
            (Finsupp.single top 1) at htopIdentity'
        change pbwLeftAction b (b q) (pbwLeftAction b (b k₀) lower) -
            pbwLeftAction b (b k₀) (pbwLeftAction b (b q) lower) =
          pbwLeftAction b ⁅b q, b k₀⁆ lower at hlowerIdentity'
        rw [show
          (pbwLeftAction b (b q)
              (pbwLeftAction b (b k₀) (Finsupp.single top 1)) +
            pbwLeftAction b (b q) (pbwLeftAction b (b k₀) lower)) -
          (pbwLeftAction b (b k₀)
              (pbwLeftAction b (b q) (Finsupp.single top 1)) +
            pbwLeftAction b (b k₀) (pbwLeftAction b (b q) lower)) =
          (pbwLeftAction b (b q)
              (pbwLeftAction b (b k₀) (Finsupp.single top 1)) -
            pbwLeftAction b (b k₀)
              (pbwLeftAction b (b q) (Finsupp.single top 1))) +
          (pbwLeftAction b (b q) (pbwLeftAction b (b k₀) lower) -
            pbwLeftAction b (b k₀) (pbwLeftAction b (b q) lower)) by abel,
          htopIdentity', hlowerIdentity']
      have hcurrent : pbwLeftAction b (b k₀) z =
          Finsupp.single word 1 := by
        rw [pbwLeftAction_apply_basis, pbwLeftActionBasis]
        change (Finsupp.linearCombination k fun w =>
          pbwNormalForm b (k₀ :: w.1)) (Finsupp.single tailWord 1) = _
        rw [Finsupp.linearCombination_single, one_smul,
          pbwNormalForm_of_pairwise b hordered]
        apply congrArg (fun w : PBWWord ι => Finsupp.single w (1 : k))
        apply Subtype.ext
        exact hwordList.symm
      rcases lt_trichotomy i j with hij | hij | hji
      · by_cases hik : i ≤ k₀
        · apply pbwLeftAction_lie_single_of_lt_of_cons_pairwise b i j word hij
          rw [hwordList]
          exact (List.pairwise_cons_cons_iff_of_trans).2 ⟨hik, hordered⟩
        · rw [← hcurrent]
          exact pbwLeftAction_lie_critical_of b k₀ i j z hzLie
            (haction j i ((lt_of_not_ge hik).trans hij) (lt_of_not_ge hik))
            (haction i j (lt_of_not_ge hik) ((lt_of_not_ge hik).trans hij))
      · subst j
        exact pbwLeftAction_lie_single_self b i word
      · by_cases hjk : j ≤ k₀
        · apply pbwLeftAction_lie_single_of_gt_of_cons_pairwise b i j word hji
          rw [hwordList]
          exact (List.pairwise_cons_cons_iff_of_trans).2 ⟨hjk, hordered⟩
        · rw [← hcurrent]
          exact pbwLeftAction_lie_critical_of b k₀ i j z hzLie
            (haction j i (lt_of_not_ge hjk) ((lt_of_not_ge hjk).trans hji))
            (haction i j ((lt_of_not_ge hjk).trans hji) (lt_of_not_ge hjk))

theorem orderedMonomialLinearCombination_pbwLeftAction
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (x : L)
    (z : PBWWord ι →₀ k) :
    orderedMonomialLinearCombination b (pbwLeftAction b x z) =
      UniversalEnvelopingAlgebra.ι k x *
        orderedMonomialLinearCombination b z := by
  let lhs : L →ₗ[k] UniversalEnvelopingAlgebra k L :=
    (orderedMonomialLinearCombination b).comp
      ((LinearMap.applyₗ (R := k) z).comp (pbwLeftAction b))
  let rhs : L →ₗ[k] UniversalEnvelopingAlgebra k L := {
    toFun := fun y => UniversalEnvelopingAlgebra.ι k y *
      orderedMonomialLinearCombination b z
    map_add' := fun y y' => by simp [add_mul]
    map_smul' := fun r y => by simp }
  have heq : lhs = rhs := by
    apply b.ext
    intro i
    change orderedMonomialLinearCombination b (pbwLeftAction b (b i) z) =
      UniversalEnvelopingAlgebra.ι k (b i) *
        orderedMonomialLinearCombination b z
    rw [pbwLeftAction_apply_basis]
    exact orderedMonomialLinearCombination_pbwLeftActionBasis b i z
  exact LinearMap.congr_fun heq x

/-- The remaining local PBW identity for the triangular action: commutators
of the normal-form operators agree with the Lie bracket.  Isolating this
identity keeps the Diamond/Jacobi calculation separate from the universal
property argument. -/
def PBWLeftActionIsLie {ι : Type w} [LinearOrder ι]
    (b : Basis ι k L) : Prop :=
  ∀ x y : L, ⁅pbwLeftAction b x, pbwLeftAction b y⁆ =
    pbwLeftAction b ⁅x, y⁆

/-- It suffices to verify the PBW action identity on pairs of basis
vectors. -/
theorem pbwLeftAction_isLie_of_basis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (h : ∀ i j : ι,
      ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆ =
        pbwLeftAction b ⁅b i, b j⁆) :
    PBWLeftActionIsLie b := by
  intro x y
  let left : L →ₗ[k] Module.End k (PBWWord ι →₀ k) := {
    toFun := fun z => ⁅pbwLeftAction b z, pbwLeftAction b y⁆
    map_add' := fun z z' => by
      rw [map_add]
      change ((pbwLeftAction b z + pbwLeftAction b z') *
          pbwLeftAction b y - pbwLeftAction b y *
          (pbwLeftAction b z + pbwLeftAction b z')) =
        (pbwLeftAction b z * pbwLeftAction b y -
          pbwLeftAction b y * pbwLeftAction b z) +
        (pbwLeftAction b z' * pbwLeftAction b y -
          pbwLeftAction b y * pbwLeftAction b z')
      rw [add_mul, mul_add]
      abel
    map_smul' := fun r z => by
      rw [map_smul]
      change ((r • pbwLeftAction b z) * pbwLeftAction b y -
          pbwLeftAction b y * (r • pbwLeftAction b z)) = _
      rw [smul_mul_assoc, mul_smul_comm]
      change r • (pbwLeftAction b z * pbwLeftAction b y) -
          r • (pbwLeftAction b y * pbwLeftAction b z) =
        r • (pbwLeftAction b z * pbwLeftAction b y -
          pbwLeftAction b y * pbwLeftAction b z)
      apply LinearMap.ext
      intro q
      exact (smul_sub r
        ((pbwLeftAction b z) ((pbwLeftAction b y) q) : PBWWord ι →₀ k)
        ((pbwLeftAction b y) ((pbwLeftAction b z) q))).symm }
  let right : L →ₗ[k] Module.End k (PBWWord ι →₀ k) := {
    toFun := fun z => pbwLeftAction b ⁅z, y⁆
    map_add' := fun z z' => by simp
    map_smul' := fun r z => by simp }
  have hxy : left = right := by
    apply b.ext
    intro i
    let lefti : L →ₗ[k] Module.End k (PBWWord ι →₀ k) := {
      toFun := fun z => ⁅pbwLeftAction b (b i), pbwLeftAction b z⁆
      map_add' := fun z z' => by
        rw [map_add]
        change (pbwLeftAction b (b i) *
            (pbwLeftAction b z + pbwLeftAction b z') -
          (pbwLeftAction b z + pbwLeftAction b z') *
            pbwLeftAction b (b i)) =
          (pbwLeftAction b (b i) * pbwLeftAction b z -
            pbwLeftAction b z * pbwLeftAction b (b i)) +
          (pbwLeftAction b (b i) * pbwLeftAction b z' -
            pbwLeftAction b z' * pbwLeftAction b (b i))
        rw [mul_add, add_mul]
        abel
      map_smul' := fun r z => by
        rw [map_smul]
        change (pbwLeftAction b (b i) * (r • pbwLeftAction b z) -
          (r • pbwLeftAction b z) * pbwLeftAction b (b i)) = _
        rw [mul_smul_comm, smul_mul_assoc]
        change r • (pbwLeftAction b (b i) * pbwLeftAction b z) -
            r • (pbwLeftAction b z * pbwLeftAction b (b i)) =
          r • (pbwLeftAction b (b i) * pbwLeftAction b z -
            pbwLeftAction b z * pbwLeftAction b (b i))
        apply LinearMap.ext
        intro q
        exact (smul_sub r
          ((pbwLeftAction b (b i)) ((pbwLeftAction b z) q) :
            PBWWord ι →₀ k)
          ((pbwLeftAction b z) ((pbwLeftAction b (b i)) q))).symm }
    let righti : L →ₗ[k] Module.End k (PBWWord ι →₀ k) := {
      toFun := fun z => pbwLeftAction b ⁅b i, z⁆
      map_add' := fun z z' => by simp
      map_smul' := fun r z => by simp }
    have hi : lefti = righti := by
      apply b.ext
      intro j
      exact h i j
    exact LinearMap.congr_fun hi y
  exact LinearMap.congr_fun hxy x

/-- For the basis-pair identity it is enough to check the action on the
single ordered-word vectors.  This is the exact word-level Jacobi/Diamond
calculation. -/
theorem pbwLeftAction_isLie_of_single
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (h : ∀ (i j : ι) (word : PBWWord ι),
      ⁅pbwLeftAction b (b i), pbwLeftAction b (b j)⁆
          (Finsupp.single word 1) =
        pbwLeftAction b ⁅b i, b j⁆ (Finsupp.single word 1)) :
    PBWLeftActionIsLie b := by
  apply pbwLeftAction_isLie_of_basis b
  intro i j
  apply Finsupp.basisSingleOne.ext
  intro word
  simpa only [Finsupp.coe_basisSingleOne] using h i j word

/-- The triangular normal-form operators form a Lie representation. -/
theorem pbwLeftAction_isLie
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    PBWLeftActionIsLie b := by
  apply pbwLeftAction_isLie_of_single b
  intro i j word
  exact pbwLeftAction_lie_single_degree b word.1.length word le_rfl i j

/-- Acting on the vacuum and retaining degree one recovers the acting Lie
algebra element. -/
theorem pbwDegreeOneRecover_leftAction_vacuum
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (x : L) :
    pbwDegreeOneRecover b
        (pbwLeftAction b x (Finsupp.single (emptyPBWWord ι) (1 : k))) = x := by
  let lhs : L →ₗ[k] L := (pbwDegreeOneRecover b).comp
    ((LinearMap.applyₗ (R := k)
      (Finsupp.single (emptyPBWWord ι) (1 : k))).comp
      (pbwLeftAction b))
  have hlhs : lhs = LinearMap.id := by
    apply b.ext
    intro i
    change pbwDegreeOneRecover b
        (pbwLeftAction b (b i)
          (Finsupp.single (emptyPBWWord ι) (1 : k))) = b i
    rw [pbwLeftAction_apply_basis, pbwLeftActionBasis,
      Finsupp.linearCombination_single]
    simp only [one_smul]
    change pbwDegreeOneRecover b (pbwNormalForm b [i]) = b i
    rw [pbwNormalForm_of_pairwise]
    exact pbwDegreeOneRecover_singleton b i
  exact LinearMap.congr_fun hlhs x

/-- The triangular PBW action, once its local Jacobi identity is known,
gives a representation separating the degree-one generators. -/
theorem iota_injective_of_pbwLeftAction_isLie
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (hLie : PBWLeftActionIsLie b) :
    Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k) := by
  let ρ : L →ₗ⁅k⁆ Module.End k (PBWWord ι →₀ k) := {
    toLinearMap := pbwLeftAction b
    map_lie' := fun {x y} => (hLie x y).symm }
  let liftρ : UniversalEnvelopingAlgebra k L →ₐ[k]
      Module.End k (PBWWord ι →₀ k) :=
    UniversalEnvelopingAlgebra.lift k ρ
  intro x y hxy
  have hoperators : ρ x = ρ y := by
    have := congrArg liftρ hxy
    simpa [liftρ, ρ] using this
  have hvacuum := DFunLike.congr_fun hoperators
    (Finsupp.single (emptyPBWWord ι) (1 : k))
  have hrecovered := congrArg (pbwDegreeOneRecover b) hvacuum
  change pbwDegreeOneRecover b
      (pbwLeftAction b x (Finsupp.single (emptyPBWWord ι) (1 : k))) =
    pbwDegreeOneRecover b
      (pbwLeftAction b y (Finsupp.single (emptyPBWWord ι) (1 : k))) at hrecovered
  rw [pbwDegreeOneRecover_leftAction_vacuum,
    pbwDegreeOneRecover_leftAction_vacuum] at hrecovered
  exact hrecovered

/-- The canonical Lie map into the universal enveloping algebra is
injective. -/
theorem iota_injective_of_basis
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k) :=
  iota_injective_of_pbwLeftAction_isLie b (pbwLeftAction_isLie b)

/-! ## Coalgebraic coefficient extraction -/

/-- All order-preserving ways of splitting a word into two subwords.  An
occurrence is assigned independently to the left or right subword. -/
def wordSplittings {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
      (wordSplittings xs).map (fun p => (x :: p.1, p.2)) ++
        (wordSplittings xs).map (fun p => (p.1, x :: p.2))

@[simp]
theorem wordSplittings_nil {α : Type*} :
    wordSplittings ([] : List α) = [([], [])] :=
  rfl

@[simp]
theorem wordSplittings_cons {α : Type*} (x : α) (xs : List α) :
    wordSplittings (x :: xs) =
      (wordSplittings xs).map (fun p => (x :: p.1, p.2)) ++
        (wordSplittings xs).map (fun p => (p.1, x :: p.2)) :=
  rfl

/-- The coproduct of a PBW word is the sum over all ways of distributing
its primitive letters between the two tensor factors. -/
theorem comul_pbwMonomial_wordSplittings
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L) (word : List ι) :
    Coalgebra.comul (R := k) (pbwMonomial b word) =
      ((wordSplittings word).map fun p =>
        pbwMonomial b p.1 ⊗ₜ[k] pbwMonomial b p.2).sum := by
  induction word with
  | nil => simp [pbwMonomial_nil, Algebra.TensorProduct.one_def]
  | cons i word ih =>
      rw [pbwMonomial_cons, Bialgebra.comul_mul]
      change Coalgebra.delta (L := L)
          (UniversalEnvelopingAlgebra.ι k (b i)) * _ = _
      rw [Coalgebra.delta_iota, ih]
      simp only [wordSplittings_cons, List.map_append, List.sum_append,
        List.map_map]
      rw [add_mul, ← List.sum_map_mul_left,
        ← List.sum_map_mul_left]
      congr 1
      · simp [Function.comp_def, pbwMonomial_cons]
      · simp [Function.comp_def, pbwMonomial_cons]

/-- Convolution of a finite list of linear functionals on the enveloping
coalgebra. -/
noncomputable def convolutionProduct :
    List (Module.Dual k (UniversalEnvelopingAlgebra k L)) →
      WithConv (Module.Dual k (UniversalEnvelopingAlgebra k L))
  | [] => 1
  | f :: fs => WithConv.toConv f * convolutionProduct fs

@[simp]
theorem convolutionProduct_nil :
    convolutionProduct (k := k) (L := L) [] = 1 :=
  rfl

@[simp]
theorem convolutionProduct_cons
    (f : Module.Dual k (UniversalEnvelopingAlgebra k L)) (fs : List _) :
    convolutionProduct (f :: fs) =
      WithConv.toConv f * convolutionProduct fs :=
  rfl

theorem wordSplittings_length
    {α : Type*} {word : List α} {p : List α × List α}
    (hp : p ∈ wordSplittings word) :
    p.1.length + p.2.length = word.length := by
  induction word generalizing p with
  | nil =>
      simp only [wordSplittings_nil, List.mem_singleton] at hp
      subst p
      simp
  | cons x word ih =>
      simp only [wordSplittings_cons, List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := hp
        have h := ih hq
        simp only [List.length_cons]
        omega
      · obtain ⟨q, hq, rfl⟩ := hp
        have h := ih hq
        simp only [List.length_cons]
        omega

theorem convolutionProduct_cons_apply_pbwMonomial
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (f : Module.Dual k (UniversalEnvelopingAlgebra k L))
    (fs : List (Module.Dual k (UniversalEnvelopingAlgebra k L)))
    (word : List ι) :
    convolutionProduct (f :: fs) (pbwMonomial b word) =
      ((wordSplittings word).map fun p =>
        f (pbwMonomial b p.1) *
          convolutionProduct fs (pbwMonomial b p.2)).sum := by
  rw [convolutionProduct_cons, LinearMap.convMul_apply,
    comul_pbwMonomial_wordSplittings]
  change ((LinearMap.mul' k k).comp
      (TensorProduct.map f (convolutionProduct fs).ofConv))
        ((List.map (fun p =>
          pbwMonomial b p.1 ⊗ₜ[k] pbwMonomial b p.2)
            (wordSplittings word)).sum) = _
  rw [map_list_sum]
  rw [List.map_map]
  congr 1

/-- A convolution of more augmentation-vanishing functionals than there
are primitive letters in a monomial evaluates to zero. -/
theorem convolutionProduct_apply_pbwMonomial_eq_zero_of_lt
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (fs : List (Module.Dual k (UniversalEnvelopingAlgebra k L)))
    (hfs : ∀ f ∈ fs, f 1 = 0) (word : List ι)
    (hlt : word.length < fs.length) :
    convolutionProduct fs (pbwMonomial b word) = 0 := by
  induction fs generalizing word with
  | nil => simp at hlt
  | cons f fs ih =>
      rw [convolutionProduct_cons_apply_pbwMonomial]
      apply List.sum_eq_zero
      intro term hterm
      simp only [List.mem_map] at hterm
      obtain ⟨p, hp, rfl⟩ := hterm
      by_cases hpempty : p.1 = []
      · rw [hpempty, pbwMonomial_nil, hfs f (by simp)]
        simp
      · have hpos : 0 < p.1.length := by
          cases hleft : p.1 with
          | nil => exact (hpempty hleft).elim
          | cons a tail => simp
        have hlength := wordSplittings_length hp
        have hright : p.2.length < fs.length := by
          simp only [List.length_cons] at hlt
          omega
        rw [ih (fun g hg => hfs g (by simp [hg])) p.2 hright]
        simp

/-- The number of occurrence-wise matchings between two words. -/
def wordMatchingCount {α : Type*} [DecidableEq α] :
    List α → List α → ℕ
  | [], word => if word = [] then 1 else 0
  | i :: target, word =>
      ((wordSplittings word).map fun p =>
        if p.1 = [i] then wordMatchingCount target p.2 else 0).sum

@[simp]
theorem wordMatchingCount_nil_nil
    {α : Type*} [DecidableEq α] :
    wordMatchingCount ([] : List α) [] = 1 :=
  rfl

@[simp]
theorem wordMatchingCount_nil_cons
    {α : Type*} [DecidableEq α] (i : α) (word : List α) :
    wordMatchingCount ([] : List α) (i :: word) = 0 := by
  simp [wordMatchingCount]

theorem empty_left_mem_wordSplittings {α : Type*} (word : List α) :
    ([], word) ∈ wordSplittings word := by
  induction word with
  | nil => simp
  | cons i word ih => simp [wordSplittings, ih]

theorem singleton_left_mem_wordSplittings {α : Type*}
    (i : α) (word : List α) :
    ([i], word) ∈ wordSplittings (i :: word) := by
  simp [wordSplittings, empty_left_mem_wordSplittings]

theorem wordMatchingCount_self_pos {α : Type*} [DecidableEq α]
    (word : List α) : 0 < wordMatchingCount word word := by
  induction word with
  | nil => simp
  | cons i word ih =>
      rw [wordMatchingCount]
      have hmem : wordMatchingCount word word ∈
          ((wordSplittings (i :: word)).map fun p =>
            if p.1 = [i] then wordMatchingCount word p.2 else 0) := by
        simp only [List.mem_map]
        exact ⟨([i], word), singleton_left_mem_wordSplittings i word, by simp⟩
      have hle := List.le_sum_of_mem hmem
      omega

theorem wordSplittings_append_perm {α : Type*}
    {word : List α} {p : List α × List α}
    (hp : p ∈ wordSplittings word) : (p.1 ++ p.2).Perm word := by
  induction word generalizing p with
  | nil =>
      simp only [wordSplittings_nil, List.mem_singleton] at hp
      subst p
      simp
  | cons i word ih =>
      simp only [wordSplittings_cons, List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := hp
        simpa using (ih hq).cons i
      · obtain ⟨q, hq, rfl⟩ := hp
        have hmove : (q.1 ++ i :: q.2).Perm (i :: q.1 ++ q.2) := by
          convert List.Perm.append_right q.2
            (List.perm_append_comm (l₁ := q.1) (l₂ := [i])) using 1 <;>
            simp
        exact hmove.trans ((ih hq).cons i)

theorem wordMatchingCount_ne_zero_imp_perm
    {α : Type*} [DecidableEq α] {target word : List α}
    (h : wordMatchingCount target word ≠ 0) : target.Perm word := by
  induction target generalizing word with
  | nil =>
      simp only [wordMatchingCount] at h
      split at h
      · subst word
        simp
      · simp at h
  | cons i target ih =>
      rw [wordMatchingCount] at h
      have hexists : ∃ term ∈
          ((wordSplittings word).map fun p =>
            if p.1 = [i] then wordMatchingCount target p.2 else 0),
          term ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h (List.sum_eq_zero hall)
      obtain ⟨term, hterm, htermne⟩ := hexists
      simp only [List.mem_map] at hterm
      obtain ⟨p, hp, rfl⟩ := hterm
      split at htermne
      next hleft =>
        have htail : target.Perm p.2 := ih htermne
        have hsplit := wordSplittings_append_perm hp
        rw [hleft] at hsplit
        simpa using (htail.cons i).trans hsplit
      next hleft => simp at htermne

theorem wordMatchingCount_eq_zero_of_pairwise_ne
    {α : Type*} [LinearOrder α] {target word : List α}
    (htarget : target.Pairwise (· ≤ ·))
    (hword : word.Pairwise (· ≤ ·)) (hne : target ≠ word) :
    wordMatchingCount target word = 0 := by
  by_contra hzero
  apply hne
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => le_antisymm hab hba)
    htarget hword (wordMatchingCount_ne_zero_imp_perm hzero)

theorem convolutionProduct_coordinates_eq_matchingCount
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (coord : ι → Module.Dual k (UniversalEnvelopingAlgebra k L))
    (hcoord_one : ∀ i, coord i 1 = 0)
    (hcoord_iota : ∀ i j,
      coord i (UniversalEnvelopingAlgebra.ι k (b j)) =
        if j = i then 1 else 0)
    (target word : List ι) (hlength : word.length = target.length) :
    convolutionProduct (target.map coord) (pbwMonomial b word) =
      (wordMatchingCount target word : k) := by
  induction target generalizing word with
  | nil =>
      have hword : word = [] := List.eq_nil_of_length_eq_zero hlength
      subst word
      simp [pbwMonomial_nil, wordMatchingCount]
  | cons i target ih =>
      simp only [List.length_cons] at hlength
      rw [List.map_cons, convolutionProduct_cons_apply_pbwMonomial]
      rw [wordMatchingCount]
      push_cast
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      rcases p with ⟨left, right⟩
      by_cases hpempty : left = []
      · rw [hpempty, pbwMonomial_nil, hcoord_one]
        simp
      · by_cases hpone : left.length = 1
        · obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hpone
          subst left
          simp only [pbwMonomial_cons, pbwMonomial_nil, mul_one]
          rw [hcoord_iota]
          by_cases hji : j = i
          · subst j
            simp only [↓reduceIte, one_mul, Function.comp_apply]
            have hsplit := wordSplittings_length hp
            change [i].length + right.length = word.length at hsplit
            simp only [List.length_cons, List.length_nil] at hsplit
            have hright : right.length = target.length := by omega
            rw [ih right hright]
          · simp [hji]
        · have hpos : 0 < left.length := by
            cases hleft : left with
            | nil => exact (hpempty hleft).elim
            | cons a tail => simp
          have hpge : 2 ≤ left.length := by omega
          have hsplit := wordSplittings_length hp
          change left.length + right.length = word.length at hsplit
          have hright : right.length < target.length := by
            omega
          have hzero :=
            convolutionProduct_apply_pbwMonomial_eq_zero_of_lt b
              (target.map coord) (by
                intro f hf
                simp only [List.mem_map] at hf
                obtain ⟨j, hj, rfl⟩ := hf
                exact hcoord_one j) right (by simpa using hright)
          rw [hzero]
          simp only [mul_zero, Function.comp_apply, Nat.cast_ite,
            Nat.cast_zero, right_eq_ite_iff]
          intro hsingleton
          have := congrArg List.length hsingleton
          simp at this
          omega

theorem convolutionProduct_coordinates_apply_ordered
    {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (coord : ι → Module.Dual k (UniversalEnvelopingAlgebra k L))
    (hcoord_one : ∀ i, coord i 1 = 0)
    (hcoord_iota : ∀ i j,
      coord i (UniversalEnvelopingAlgebra.ι k (b j)) =
        if j = i then 1 else 0)
    (target word : PBWWord ι) (hlength : word.1.length = target.1.length) :
    convolutionProduct (target.1.map coord) (orderedMonomial b word) =
      if target = word then (wordMatchingCount target.1 target.1 : k) else 0 := by
  rw [orderedMonomial,
    convolutionProduct_coordinates_eq_matchingCount b coord hcoord_one
      hcoord_iota target.1 word.1 hlength]
  by_cases htw : target = word
  · subst word
    simp
  · simp only [htw, ↓reduceIte]
    have hcount : wordMatchingCount target.1 word.1 = 0 :=
      wordMatchingCount_eq_zero_of_pairwise_ne target.2 word.2 (by
        intro hwords
        apply htw
        exact Subtype.ext hwords)
    rw [hcount]
    simp

theorem convolutionProduct_coordinates_apply_self_ne_zero
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (coord : ι → Module.Dual k (UniversalEnvelopingAlgebra k L))
    (hcoord_one : ∀ i, coord i 1 = 0)
    (hcoord_iota : ∀ i j,
      coord i (UniversalEnvelopingAlgebra.ι k (b j)) =
        if j = i then 1 else 0)
    (word : PBWWord ι) :
    convolutionProduct (word.1.map coord) (orderedMonomial b word) ≠ 0 := by
  rw [convolutionProduct_coordinates_apply_ordered b coord hcoord_one
    hcoord_iota word word rfl]
  simp only [↓reduceIte]
  exact Nat.cast_ne_zero.mpr (wordMatchingCount_self_pos word.1).ne'

/-- In characteristic zero, coordinate functionals on the primitive
generators suffice to prove linear independence of all ordered monomials. -/
theorem orderedMonomial_linearIndependent_of_coordinates
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (coord : ι → Module.Dual k (UniversalEnvelopingAlgebra k L))
    (hcoord_one : ∀ i, coord i 1 = 0)
    (hcoord_iota : ∀ i j,
      coord i (UniversalEnvelopingAlgebra.ι k (b j)) =
        if j = i then 1 else 0) :
    LinearIndependent k (orderedMonomial b) := by
  rw [linearIndependent_iff]
  intro z hz
  by_contra hz0
  have hsupp : z.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hempty => hz0 (Finsupp.support_eq_empty.mp hempty)
  obtain ⟨target, htarget, hmax⟩ :=
    Finset.exists_max_image z.support (fun word => word.1.length) hsupp
  have hcoeff : z target ≠ 0 := Finsupp.mem_support_iff.mp htarget
  let Φ := convolutionProduct (target.1.map coord)
  have heval : Φ ((Finsupp.linearCombination k (orderedMonomial b)) z) = 0 := by
    rw [hz]
    exact map_zero Φ.ofConv
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at heval
  simp only [map_smul, smul_eq_mul] at heval
  rw [Finset.sum_eq_single target] at heval
  · have hdiag : Φ (orderedMonomial b target) ≠ 0 :=
      convolutionProduct_coordinates_apply_self_ne_zero b coord
        hcoord_one hcoord_iota target
    exact hcoeff (mul_eq_zero.mp heval |>.resolve_right hdiag)
  · intro word hword hne
    have hle := hmax word hword
    by_cases hlen : word.1.length = target.1.length
    · rw [convolutionProduct_coordinates_apply_ordered b coord
          hcoord_one hcoord_iota target word hlen]
      have hnt : target ≠ word := Ne.symm hne
      simp [hnt]
    · have hlt : word.1.length < target.1.length := lt_of_le_of_ne hle hlen
      rw [orderedMonomial,
        convolutionProduct_apply_pbwMonomial_eq_zero_of_lt b
          (target.1.map coord) (by
            intro f hf
            simp only [List.mem_map] at hf
            obtain ⟨i, hi, rfl⟩ := hf
            exact hcoord_one i) word.1 (by simpa using hlt)]
      simp
  · intro hnmem
    exact (hnmem htarget).elim

/-- In characteristic zero, injectivity of the canonical Lie map supplies
the coordinate functionals needed by the convolution proof of PBW. -/
theorem orderedMonomial_linearIndependent_of_iota_injective
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (hι : Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k)) :
    LinearIndependent k (orderedMonomial b) := by
  let U := UniversalEnvelopingAlgebra k L
  let v : Option ι → U := fun o =>
    Option.casesOn' o 1 fun i => UniversalEnvelopingAlgebra.ι k (b i)
  have hvι : LinearIndependent k
      (fun i : ι => UniversalEnvelopingAlgebra.ι k (b i)) :=
    b.linearIndependent.map'
      (UniversalEnvelopingAlgebra.ι k).toLinearMap
      (LinearMap.ker_eq_bot.2 hι)
  have hone : (1 : U) ∉ Submodule.span k
      (Set.range fun i : ι => UniversalEnvelopingAlgebra.ι k (b i)) := by
    intro hone
    have hle : Submodule.span k
        (Set.range fun i : ι => UniversalEnvelopingAlgebra.ι k (b i)) ≤
        LinearMap.ker (Coalgebra.counit (R := k)) := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      exact Coalgebra.eps_iota (k := k) (L := L) (b i)
    have := hle hone
    change Coalgebra.counit (R := k) (1 : U) = 0 at this
    simp at this
  have hv : LinearIndependent k v := by
    exact hvι.option hone
  let V := Submodule.span k (Set.range v)
  let coord (i : ι) : Module.Dual k U :=
    Subspace.dualLift V ((Basis.span hv).coord (some i))
  have hcoord (i : ι) (o : Option ι) :
      coord i (v o) = if o = some i then 1 else 0 := by
    classical
    unfold coord
    let ho : v o ∈ V := Submodule.subset_span (Set.mem_range_self o)
    rw [Subspace.dualLift_of_mem ho]
    have heq : (⟨v o, ho⟩ : V) = Basis.span hv o := by
      apply Subtype.ext
      exact (Basis.coe_span_apply hv o).symm
    change (Basis.span hv).coord (some i) (⟨v o, ho⟩ : V) = _
    rw [heq, Basis.coord_apply, Basis.repr_self]
    simp only [Finsupp.single_apply]
  apply orderedMonomial_linearIndependent_of_coordinates b coord
  · intro i
    simpa [v] using hcoord i none
  · intro i j
    simpa [v, eq_comm] using hcoord i (some j)

/-- The absolute PBW basis, once injectivity of the canonical Lie map is
known. -/
noncomputable def orderedMonomialBasisOfIotaInjective
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (hι : Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k)) :
    Basis (PBWWord ι) k (UniversalEnvelopingAlgebra k L) :=
  orderedMonomialBasisOfLinearIndependent b
    (orderedMonomial_linearIndependent_of_iota_injective b hι)

@[simp]
theorem orderedMonomialBasisOfIotaInjective_apply
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (hι : Function.Injective (UniversalEnvelopingAlgebra.ι (L := L) k))
    (word : PBWWord ι) :
    orderedMonomialBasisOfIotaInjective b hι word =
      orderedMonomial b word :=
  orderedMonomialBasisOfLinearIndependent_apply _ _ _

/-- Relative PBW in characteristic zero, reduced to injectivity of the two
canonical maps into the corresponding enveloping algebras. -/
noncomputable def relativePBWBasisOfIotaInjective
    [CharZero k] {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f)
    (hιL : Function.Injective
      (UniversalEnvelopingAlgebra.ι (L := L) k))
    (hιQ : Function.Injective
      (UniversalEnvelopingAlgebra.ι (L := Q) k)) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    RelativePBWBasis f (PBWWord (RelativeComplementIndex b f hf)) := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  apply relativePBWBasisOfLinearIndependent b f hf
  · exact orderedMonomial_linearIndependent_of_iota_injective b hιL
  · exact orderedMonomial_linearIndependent_of_iota_injective
      (extendMappedBasisLex b f hf) hιQ

/-- The ordered PBW monomials are linearly independent in characteristic
zero. -/
theorem orderedMonomial_linearIndependent
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    LinearIndependent k (orderedMonomial b) :=
  orderedMonomial_linearIndependent_of_iota_injective b
    (iota_injective_of_basis b)

/-- The absolute ordered PBW basis. -/
noncomputable def orderedMonomialBasis
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L) :
    Basis (PBWWord ι) k (UniversalEnvelopingAlgebra k L) :=
  orderedMonomialBasisOfLinearIndependent b
    (orderedMonomial_linearIndependent b)

@[simp]
theorem orderedMonomialBasis_apply
    [CharZero k] {ι : Type w} [LinearOrder ι] (b : Basis ι k L)
    (word : PBWWord ι) :
    orderedMonomialBasis b word = orderedMonomial b word :=
  orderedMonomialBasisOfLinearIndependent_apply _ _ _

/-- Relative PBW: after extending a basis along an injective Lie map, the
complement monomials form a basis over the smaller enveloping algebra. -/
noncomputable def relativePBWBasis
    [CharZero k] {ι : Type*} [LinearOrder ι]
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (b : Basis ι k L) (f : LieHom k L Q) (hf : Function.Injective f) :
    let _ : LinearOrder (RelativeComplementIndex b f hf) :=
      relativeComplementLinearOrder b f hf
    RelativePBWBasis f (PBWWord (RelativeComplementIndex b f hf)) := by
  let _ : LinearOrder (RelativeComplementIndex b f hf) :=
    relativeComplementLinearOrder b f hf
  exact relativePBWBasisOfIotaInjective b f hf
    (iota_injective_of_basis b)
    (iota_injective_of_basis (extendMappedBasisLex b f hf))


end

end UniversalEnvelopingAlgebra
