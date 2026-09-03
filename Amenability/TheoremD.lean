/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremB
import Amenability.LieGeneratorTest
import Amenability.CoalgebraInjective
import Amenability.UniversalEnvelopingPBW
import Amenability.ElementaryLieAlgebra
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Theorem D: permanence properties for amenable Lie algebras

This file formalizes the five closure assertions collected as Theorem D in
the accompanying article.  The public predicate is the manuscript's
finite-Lie-subspace, finite-subcoalgebra condition; the generator test proved
in `LieGeneratorTest` lets the internal permanence arguments use the regular
universal-enveloping module.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

local notation "U" => UniversalEnvelopingAlgebra k L

/-! ## Linear splittings of Lie-ideal quotients -/

/-- The canonical inclusion of a Lie ideal, with the ideal's own bundled
instances kept definitionally visible. -/
def LieIdeal.inclusionLieHom (I : LieIdeal k L) : I →ₗ⁅k⁆ L where
  __ := I.toSubmodule.subtype
  map_lie' := rfl

@[simp]
theorem LieIdeal.inclusionLieHom_apply (I : LieIdeal k L) (x : I) :
    LieIdeal.inclusionLieHom I x = (x : L) :=
  rfl

/-- A fixed linear section of the quotient map by a Lie ideal. -/
noncomputable def LieIdeal.linearSection (I : LieIdeal k L) :
    (L ⧸ I) →ₗ[k] L :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective
    (LieIdeal.quotientMkLieHom I).toLinearMap
    (LinearMap.range_eq_top.2
      (LieIdeal.quotientMkLieHom_surjective I)))

@[simp]
theorem LieIdeal.quotientMk_linearSection (I : LieIdeal k L)
    (q : L ⧸ I) :
    LieIdeal.quotientMkLieHom I (LieIdeal.linearSection I q) = q := by
  have h := Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective
      (LieIdeal.quotientMkLieHom I).toLinearMap
      (LinearMap.range_eq_top.2
        (LieIdeal.quotientMkLieHom_surjective I)))
  exact LinearMap.congr_fun h q

@[simp]
theorem LieIdeal.quotientMk_coe (I : LieIdeal k L) (a : I) :
    LieIdeal.quotientMkLieHom I (a : L) = 0 :=
  LieSubmodule.Quotient.mk_eq_zero'.mpr a.2

/-- The linear splitting `L ≃ (L/I) × I` associated to the fixed section. -/
noncomputable def LieIdeal.quotientProdEquiv (I : LieIdeal k L) :
    ((L ⧸ I) × I) ≃ₗ[k] L := by
  let e : (L ⧸ I) × I →ₗ[k] L :=
    ((LieIdeal.linearSection I).comp (LinearMap.fst k (L ⧸ I) I)) +
      (I.toSubmodule.subtype.comp (LinearMap.snd k (L ⧸ I) I))
  refine LinearEquiv.ofBijective e ?_
  constructor
  · rintro ⟨q, a⟩ ⟨q', a'⟩ h
    have hq : q = q' := by
      have := congrArg (LieIdeal.quotientMkLieHom I) h
      have ha0 : LieIdeal.quotientMkLieHom I (I.toSubmodule.subtype a) = 0 :=
        LieIdeal.quotientMk_coe I a
      have ha0' : LieIdeal.quotientMkLieHom I (I.toSubmodule.subtype a') = 0 :=
        LieIdeal.quotientMk_coe I a'
      simpa only [e, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply,
        map_add, LieIdeal.quotientMk_linearSection,
        ha0, ha0', add_zero] using this
    subst q'
    apply Prod.ext
    · rfl
    apply Subtype.ext
    simpa [e] using h
  · intro x
    let q : L ⧸ I := LieIdeal.quotientMkLieHom I x
    have hmem : x - LieIdeal.linearSection I q ∈ I := by
      apply LieSubmodule.Quotient.mk_eq_zero'.mp
      change LieIdeal.quotientMkLieHom I x -
        LieIdeal.quotientMkLieHom I (LieIdeal.linearSection I q) = 0
      rw [LieIdeal.quotientMk_linearSection]
      exact sub_self _
    refine ⟨(q, ⟨x - LieIdeal.linearSection I q, hmem⟩), ?_⟩
    simp [e, q]

@[simp]
theorem LieIdeal.quotientProdEquiv_apply (I : LieIdeal k L)
    (q : L ⧸ I) (a : I) :
    LieIdeal.quotientProdEquiv I (q, a) =
      LieIdeal.linearSection I q + (a : L) :=
  rfl

/-- A basis of an ideal and a basis of its quotient, with quotient vectors
first, give the split basis of the middle Lie algebra used in the extension
PBW argument. -/
noncomputable def LieIdeal.extensionBasis {α β : Type*}
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) : Basis (β ⊕ α) k L :=
  (bQ.prod bI).map (LieIdeal.quotientProdEquiv I)

@[simp]
theorem LieIdeal.extensionBasis_apply_inl {α β : Type*}
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) (j : β) :
    LieIdeal.extensionBasis I bQ bI (Sum.inl j) =
      LieIdeal.linearSection I (bQ j) := by
  simp [LieIdeal.extensionBasis, LieIdeal.quotientProdEquiv_apply]

@[simp]
theorem LieIdeal.extensionBasis_apply_inr {α β : Type*}
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) (j : α) :
    LieIdeal.extensionBasis I bQ bI (Sum.inr j) = (bI j : L) := by
  simp [LieIdeal.extensionBasis, LieIdeal.quotientProdEquiv_apply]

/-- The split extension basis, ordered with quotient indices before ideal
indices. -/
noncomputable def LieIdeal.extensionBasisLex {α β : Type*}
    [LinearOrder α] [LinearOrder β] (I : LieIdeal k L)
    (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I) :
    Basis (β ⊕ₗ α) k L :=
  (LieIdeal.extensionBasis I bQ bI).reindex toLex

@[simp]
theorem LieIdeal.extensionBasisLex_apply_inl {α β : Type*}
    [LinearOrder α] [LinearOrder β] (I : LieIdeal k L)
    (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I) (j : β) :
    LieIdeal.extensionBasisLex I bQ bI (toLex (Sum.inl j : β ⊕ α)) =
      LieIdeal.linearSection I (bQ j) := by
  rw [LieIdeal.extensionBasisLex, Module.Basis.reindex_apply]
  exact LieIdeal.extensionBasis_apply_inl I bQ bI j

@[simp]
theorem LieIdeal.extensionBasisLex_apply_inr {α β : Type*}
    [LinearOrder α] [LinearOrder β] (I : LieIdeal k L)
    (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I) (j : α) :
    LieIdeal.extensionBasisLex I bQ bI (toLex (Sum.inr j : β ⊕ α)) =
      (bI j : L) := by
  rw [LieIdeal.extensionBasisLex, Module.Basis.reindex_apply]
  exact LieIdeal.extensionBasis_apply_inr I bQ bI j

/-- The ordered product of chosen lifts of a quotient PBW word. -/
noncomputable def LieIdeal.liftedQuotientMonomial {α β : Type*}
    [LinearOrder α] [LinearOrder β] (I : LieIdeal k L)
    (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I)
    (word : UniversalEnvelopingAlgebra.PBWWord β) :
    UniversalEnvelopingAlgebra k L :=
  UniversalEnvelopingAlgebra.pbwMonomial
    (LieIdeal.extensionBasisLex I bQ bI)
    (word.1.map fun j => toLex (Sum.inl j : β ⊕ α))

/-- The PBW linear section `U(L/I) → U(L)` attached to the split basis. -/
noncomputable def LieIdeal.ueaLinearSection
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    UniversalEnvelopingAlgebra k (L ⧸ I) →ₗ[k]
      UniversalEnvelopingAlgebra k L :=
  (UniversalEnvelopingAlgebra.orderedMonomialBasis bQ).constr k
    (LieIdeal.liftedQuotientMonomial I bQ bI)

@[simp]
theorem LieIdeal.ueaLinearSection_orderedMonomial
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (word : UniversalEnvelopingAlgebra.PBWWord β) :
    LieIdeal.ueaLinearSection I bQ bI
        (UniversalEnvelopingAlgebra.orderedMonomial bQ word) =
      LieIdeal.liftedQuotientMonomial I bQ bI word := by
  rw [← UniversalEnvelopingAlgebra.orderedMonomialBasis_apply bQ word]
  exact Module.Basis.constr_basis
    (UniversalEnvelopingAlgebra.orderedMonomialBasis bQ) k
    (LieIdeal.liftedQuotientMonomial I bQ bI) word

@[simp]
theorem LieIdeal.pbwMap_liftedQuotientMonomial
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (word : UniversalEnvelopingAlgebra.PBWWord β) :
    UniversalEnvelopingAlgebra.pbwMap (LieIdeal.quotientMkLieHom I)
        (LieIdeal.liftedQuotientMonomial I bQ bI word) =
      UniversalEnvelopingAlgebra.orderedMonomial bQ word := by
  change UniversalEnvelopingAlgebra.pbwMap (LieIdeal.quotientMkLieHom I)
      (UniversalEnvelopingAlgebra.pbwMonomial
        (LieIdeal.extensionBasisLex I bQ bI)
        (word.1.map fun j => toLex (Sum.inl j : β ⊕ α))) =
    UniversalEnvelopingAlgebra.pbwMonomial bQ word.1
  induction word.1 with
  | nil => simp
  | cons j js ih =>
      rw [List.map_cons, UniversalEnvelopingAlgebra.pbwMonomial_cons,
        map_mul, UniversalEnvelopingAlgebra.pbwMap_iota,
        LieIdeal.extensionBasisLex_apply_inl,
        LieIdeal.quotientMk_linearSection, ih,
        UniversalEnvelopingAlgebra.pbwMonomial_cons]

/-- The enveloping-algebra quotient map is a left inverse of the PBW
linear section. -/
theorem LieIdeal.pbwMap_comp_ueaLinearSection
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (UniversalEnvelopingAlgebra.pbwMap
      (LieIdeal.quotientMkLieHom I)).toLinearMap.comp
        (LieIdeal.ueaLinearSection I bQ bI) = LinearMap.id := by
  apply (UniversalEnvelopingAlgebra.orderedMonomialBasis bQ).ext
  intro word
  rw [LinearMap.comp_apply,
    UniversalEnvelopingAlgebra.orderedMonomialBasis_apply,
    LieIdeal.ueaLinearSection_orderedMonomial,
    LinearMap.id_apply]
  exact LieIdeal.pbwMap_liftedQuotientMonomial I bQ bI word

/-- Multiplication after the PBW quotient section and the enveloping map of
the ideal. -/
noncomputable def LieIdeal.extensionPBWMap
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) →ₗ[k]
        UniversalEnvelopingAlgebra k L :=
  (LinearMap.mul' k (UniversalEnvelopingAlgebra k L)).comp
    (TensorProduct.map (LieIdeal.ueaLinearSection I bQ bI)
      (UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.inclusionLieHom I)).toLinearMap)

@[simp]
theorem LieIdeal.extensionPBWMap_tmul
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (q : UniversalEnvelopingAlgebra k (L ⧸ I))
    (a : UniversalEnvelopingAlgebra k I) :
    LieIdeal.extensionPBWMap I bQ bI (q ⊗ₜ[k] a) =
      LieIdeal.ueaLinearSection I bQ bI q *
        UniversalEnvelopingAlgebra.pbwMap
          (LieIdeal.inclusionLieHom I) a := by
  rfl

theorem LieIdeal.pbwMap_ideal_pbwMonomial
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) (word : List α) :
    UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.inclusionLieHom I)
        (UniversalEnvelopingAlgebra.pbwMonomial bI word) =
      UniversalEnvelopingAlgebra.pbwMonomial
        (LieIdeal.extensionBasisLex I bQ bI)
        (word.map fun j => toLex (Sum.inr j : β ⊕ α)) := by
  induction word with
  | nil => simp
  | cons j js ih =>
      rw [UniversalEnvelopingAlgebra.pbwMonomial_cons, map_mul,
        UniversalEnvelopingAlgebra.pbwMap_iota, ih, List.map_cons,
        UniversalEnvelopingAlgebra.pbwMonomial_cons,
        LieIdeal.extensionBasisLex_apply_inr,
        LieIdeal.inclusionLieHom_apply]

/-- On PBW basis tensors, extension multiplication is the corresponding
ordered monomial in the split basis. -/
theorem LieIdeal.extensionPBWMap_basis_tmul
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (qword : UniversalEnvelopingAlgebra.PBWWord β)
    (iword : UniversalEnvelopingAlgebra.PBWWord α) :
    LieIdeal.extensionPBWMap I bQ bI
        (UniversalEnvelopingAlgebra.orderedMonomial bQ qword ⊗ₜ[k]
          UniversalEnvelopingAlgebra.orderedMonomial bI iword) =
      UniversalEnvelopingAlgebra.orderedMonomial
        (LieIdeal.extensionBasisLex I bQ bI)
        (UniversalEnvelopingAlgebra.combinePBWWords (qword, iword)) := by
  rw [LieIdeal.extensionPBWMap_tmul,
    LieIdeal.ueaLinearSection_orderedMonomial]
  change LieIdeal.liftedQuotientMonomial I bQ bI qword *
      UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.inclusionLieHom I)
        (UniversalEnvelopingAlgebra.pbwMonomial bI iword.1) = _
  rw [LieIdeal.pbwMap_ideal_pbwMonomial
    (α := α) (β := β) I bQ bI]
  exact (UniversalEnvelopingAlgebra.pbwMonomial_append
    (LieIdeal.extensionBasisLex I bQ bI)
    (qword.1.map fun j => toLex (Sum.inl j : β ⊕ α))
    (iword.1.map fun j => toLex (Sum.inr j : β ⊕ α))).symm

/-- PBW multiplication gives the vector-space tensor decomposition
`U(L/I) ⊗ U(I) ≃ U(L)`. -/
noncomputable def LieIdeal.extensionPBWEquiv
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) ≃ₗ[k]
        UniversalEnvelopingAlgebra k L := by
  let qBasis := UniversalEnvelopingAlgebra.orderedMonomialBasis bQ
  let iBasis := UniversalEnvelopingAlgebra.orderedMonomialBasis bI
  let tensorBasis := qBasis.tensorProduct iBasis
  let lBasis0 := UniversalEnvelopingAlgebra.orderedMonomialBasis
    (LieIdeal.extensionBasisLex I bQ bI)
  let lBasis := lBasis0.reindex
    UniversalEnvelopingAlgebra.pbwWordSumLexEquiv
  let e := tensorBasis.equiv lBasis (Equiv.refl _)
  apply LinearEquiv.ofBijective (LieIdeal.extensionPBWMap I bQ bI)
  have heq : LieIdeal.extensionPBWMap I bQ bI = e.toLinearMap := by
    apply tensorBasis.ext
    rintro ⟨qword, iword⟩
    change LieIdeal.extensionPBWMap I bQ bI
        (tensorBasis (qword, iword)) = e (tensorBasis (qword, iword))
    rw [Module.Basis.equiv_apply]
    dsimp only [tensorBasis, qBasis, iBasis, lBasis, lBasis0]
    rw [Module.Basis.tensorProduct_apply, Module.Basis.reindex_apply,
      UniversalEnvelopingAlgebra.orderedMonomialBasis_apply,
      UniversalEnvelopingAlgebra.orderedMonomialBasis_apply,
      UniversalEnvelopingAlgebra.orderedMonomialBasis_apply]
    exact LieIdeal.extensionPBWMap_basis_tmul I bQ bI qword iword
  rw [heq]
  exact e.bijective

@[simp]
theorem LieIdeal.extensionPBWEquiv_apply
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (x : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) :
    LieIdeal.extensionPBWEquiv I bQ bI x =
      LieIdeal.extensionPBWMap I bQ bI x :=
  rfl

theorem UniversalEnvelopingAlgebra.wordSplittings_sublist
    {γ : Type*} {word : List γ} {p : List γ × List γ}
    (hp : p ∈ UniversalEnvelopingAlgebra.wordSplittings word) :
    p.1.Sublist word ∧ p.2.Sublist word := by
  induction word generalizing p with
  | nil =>
      simp only [UniversalEnvelopingAlgebra.wordSplittings_nil,
        List.mem_singleton] at hp
      subst p
      exact ⟨List.Sublist.slnil, List.Sublist.slnil⟩
  | cons x xs ih =>
      simp only [UniversalEnvelopingAlgebra.wordSplittings_cons,
        List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · obtain ⟨hql, hqr⟩ := ih hq
        exact ⟨hql.cons_cons x, hqr.cons x⟩
      · obtain ⟨hql, hqr⟩ := ih hq
        exact ⟨hql.cons x, hqr.cons_cons x⟩

theorem UniversalEnvelopingAlgebra.wordSplittings_map
    {γ δ : Type*} (f : γ → δ) (word : List γ) :
    UniversalEnvelopingAlgebra.wordSplittings (word.map f) =
      (UniversalEnvelopingAlgebra.wordSplittings word).map fun p =>
        (p.1.map f, p.2.map f) := by
  induction word with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,
        UniversalEnvelopingAlgebra.wordSplittings_cons, ih,
        List.map_append, List.map_map]
      rfl

/-- Every subword appearing in the PBW coproduct of an ordered word is
ordered. -/
theorem UniversalEnvelopingAlgebra.wordSplittings_pairwise
    {γ : Type*} [LinearOrder γ]
    {word : List γ} (hword : word.Pairwise (· ≤ ·))
    {p : List γ × List γ}
    (hp : p ∈ UniversalEnvelopingAlgebra.wordSplittings word) :
    p.1.Pairwise (· ≤ ·) ∧ p.2.Pairwise (· ≤ ·) := by
  obtain ⟨hl, hr⟩ :=
    UniversalEnvelopingAlgebra.wordSplittings_sublist hp
  exact ⟨hword.sublist hl, hword.sublist hr⟩

/-- The PBW quotient section respects comultiplication. -/
theorem LieIdeal.comul_ueaLinearSection
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (Coalgebra.comul (R := k)).comp
        (LieIdeal.ueaLinearSection I bQ bI) =
      (TensorProduct.map (LieIdeal.ueaLinearSection I bQ bI)
        (LieIdeal.ueaLinearSection I bQ bI)).comp
          (Coalgebra.comul (R := k)) := by
  apply (UniversalEnvelopingAlgebra.orderedMonomialBasis bQ).ext
  intro word
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    UniversalEnvelopingAlgebra.orderedMonomialBasis_apply,
    LieIdeal.ueaLinearSection_orderedMonomial]
  change Coalgebra.comul (R := k)
      (UniversalEnvelopingAlgebra.pbwMonomial
        (LieIdeal.extensionBasisLex I bQ bI)
        (word.1.map fun j => toLex (Sum.inl j : β ⊕ α))) = _
  rw [UniversalEnvelopingAlgebra.comul_pbwMonomial_wordSplittings,
    UniversalEnvelopingAlgebra.wordSplittings_map]
  change _ = (TensorProduct.map (LieIdeal.ueaLinearSection I bQ bI)
    (LieIdeal.ueaLinearSection I bQ bI))
      (Coalgebra.comul (R := k)
        (UniversalEnvelopingAlgebra.pbwMonomial bQ word.1))
  rw [UniversalEnvelopingAlgebra.comul_pbwMonomial_wordSplittings,
    map_list_sum]
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨hpl, hpr⟩ :=
    UniversalEnvelopingAlgebra.wordSplittings_pairwise word.2 hp
  change _ = (TensorProduct.map (LieIdeal.ueaLinearSection I bQ bI)
    (LieIdeal.ueaLinearSection I bQ bI))
      (UniversalEnvelopingAlgebra.pbwMonomial bQ p.1 ⊗ₜ[k]
        UniversalEnvelopingAlgebra.pbwMonomial bQ p.2)
  rw [TensorProduct.map_tmul]
  rw [show LieIdeal.ueaLinearSection I bQ bI
        (UniversalEnvelopingAlgebra.pbwMonomial bQ p.1) =
      LieIdeal.liftedQuotientMonomial I bQ bI ⟨p.1, hpl⟩ by
        exact LieIdeal.ueaLinearSection_orderedMonomial
          I bQ bI ⟨p.1, hpl⟩]
  rw [show LieIdeal.ueaLinearSection I bQ bI
        (UniversalEnvelopingAlgebra.pbwMonomial bQ p.2) =
      LieIdeal.liftedQuotientMonomial I bQ bI ⟨p.2, hpr⟩ by
        exact LieIdeal.ueaLinearSection_orderedMonomial
          I bQ bI ⟨p.2, hpr⟩]
  rfl

/-- The PBW quotient section also preserves the counit. -/
theorem LieIdeal.counit_ueaLinearSection
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (Coalgebra.counit (R := k)).comp
        (LieIdeal.ueaLinearSection I bQ bI) =
      Coalgebra.counit (R := k) := by
  apply (UniversalEnvelopingAlgebra.orderedMonomialBasis bQ).ext
  intro word
  rw [LinearMap.comp_apply,
    UniversalEnvelopingAlgebra.orderedMonomialBasis_apply,
    LieIdeal.ueaLinearSection_orderedMonomial]
  change Coalgebra.eps
      (UniversalEnvelopingAlgebra.pbwMonomial
        (LieIdeal.extensionBasisLex I bQ bI)
        (word.1.map fun j => toLex (Sum.inl j : β ⊕ α))) =
    Coalgebra.eps
      (UniversalEnvelopingAlgebra.pbwMonomial bQ word.1)
  induction word.1 with
  | nil => simp
  | cons j js ih =>
      rw [List.map_cons,
        UniversalEnvelopingAlgebra.pbwMonomial_cons,
        UniversalEnvelopingAlgebra.pbwMonomial_cons,
        map_mul, map_mul, Coalgebra.eps_iota, Coalgebra.eps_iota,
        zero_mul, zero_mul]

/-- The PBW quotient section as a coalgebra morphism. -/
noncomputable def LieIdeal.ueaLinearSectionCoalgHom
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    UniversalEnvelopingAlgebra k (L ⧸ I) →ₗc[k]
      UniversalEnvelopingAlgebra k L where
  toLinearMap := LieIdeal.ueaLinearSection I bQ bI
  counit_comp := LieIdeal.counit_ueaLinearSection I bQ bI
  map_comp_comul := (LieIdeal.comul_ueaLinearSection I bQ bI).symm

@[simp]
theorem LieIdeal.ueaLinearSectionCoalgHom_apply
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (q : UniversalEnvelopingAlgebra k (L ⧸ I)) :
    LieIdeal.ueaLinearSectionCoalgHom I bQ bI q =
      LieIdeal.ueaLinearSection I bQ bI q :=
  rfl

/-- A Lie homomorphism induces a coalgebra morphism between enveloping
coalgebras.  This PBW-independent version is available to the extension
construction before the amenability-specific `ueaMap` abbreviation. -/
noncomputable def UniversalEnvelopingAlgebra.pbwMapCoalgHom
    {Q : Type w} [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q) :
    UniversalEnvelopingAlgebra k L →ₗc[k]
      UniversalEnvelopingAlgebra k Q where
  toLinearMap := (UniversalEnvelopingAlgebra.pbwMap f).toLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro a
    have heq : (Coalgebra.eps (L := Q)).comp
        (UniversalEnvelopingAlgebra.pbwMap f) =
        Coalgebra.eps (L := L) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext _ _
      intro x
      change Coalgebra.eps
          (UniversalEnvelopingAlgebra.pbwMap f
            (UniversalEnvelopingAlgebra.ι k x)) =
        Coalgebra.eps (UniversalEnvelopingAlgebra.ι k x)
      rw [UniversalEnvelopingAlgebra.pbwMap_iota,
        Coalgebra.eps_iota, Coalgebra.eps_iota]
    exact DFunLike.congr_fun heq a
  map_comp_comul := by
    apply LinearMap.ext
    intro a
    have heq :
        (Algebra.TensorProduct.map
          (UniversalEnvelopingAlgebra.pbwMap f)
          (UniversalEnvelopingAlgebra.pbwMap f)).comp
            (Coalgebra.delta (L := L)) =
          (Coalgebra.delta (L := Q)).comp
            (UniversalEnvelopingAlgebra.pbwMap f) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext _ _
      intro x
      change Algebra.TensorProduct.map
          (UniversalEnvelopingAlgebra.pbwMap f)
          (UniversalEnvelopingAlgebra.pbwMap f)
          (Coalgebra.delta (UniversalEnvelopingAlgebra.ι k x)) =
        Coalgebra.delta
          (UniversalEnvelopingAlgebra.pbwMap f
            (UniversalEnvelopingAlgebra.ι k x))
      rw [Coalgebra.delta_iota]
      simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
      rw [UniversalEnvelopingAlgebra.pbwMap_iota,
        Coalgebra.delta_iota]
    exact DFunLike.congr_fun heq a

@[simp]
theorem UniversalEnvelopingAlgebra.pbwMapCoalgHom_apply
    {Q : Type w} [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q)
    (a : UniversalEnvelopingAlgebra k L) :
    UniversalEnvelopingAlgebra.pbwMapCoalgHom f a =
      UniversalEnvelopingAlgebra.pbwMap f a :=
  rfl

/-- The finite-dimensional image of a finite subcoalgebra under an
arbitrary coalgebra morphism. -/
noncomputable def FiniteSubcoalgebra.image
    {A : Type*} {B : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [Coalgebra k A] [Coalgebra k B]
    (C : FiniteSubcoalgebra k A) (f : A →ₗc[k] B) :
    FiniteSubcoalgebra k B where
  carrier := C.carrier.map f.toLinearMap
  isSubcoalgebra := C.isSubcoalgebra.map_coalgHom f
  finiteDimensional := by infer_instance

@[simp]
theorem FiniteSubcoalgebra.image_carrier
    {A : Type*} {B : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [Coalgebra k A] [Coalgebra k B]
    (C : FiniteSubcoalgebra k A) (f : A →ₗc[k] B) :
    (C.image f).carrier = C.carrier.map f.toLinearMap :=
  rfl

/-- The PBW tensor decomposition as a coalgebra map. -/
noncomputable def LieIdeal.extensionPBWCoalgHom
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) →ₗc[k]
        UniversalEnvelopingAlgebra k L :=
  (Bialgebra.mulCoalgHom k (UniversalEnvelopingAlgebra k L)).comp
    (CoalgHom.tensorMapStruct
      (LieIdeal.ueaLinearSectionCoalgHom I bQ bI)
      (UniversalEnvelopingAlgebra.pbwMapCoalgHom
        (LieIdeal.inclusionLieHom I)))

@[simp]
theorem LieIdeal.extensionPBWCoalgHom_apply
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (x : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) :
    LieIdeal.extensionPBWCoalgHom I bQ bI x =
      LieIdeal.extensionPBWMap I bQ bI x := by
  rfl

/-- The PBW tensor decomposition as a coalgebra equivalence. -/
noncomputable def LieIdeal.extensionPBWCoalgEquiv
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) ≃ₗc[k]
        UniversalEnvelopingAlgebra k L :=
  CoalgEquiv.ofBijective
    (f := LieIdeal.extensionPBWCoalgHom I bQ bI) (by
    change Function.Bijective (LieIdeal.extensionPBWMap I bQ bI)
    exact (LieIdeal.extensionPBWEquiv I bQ bI).bijective)

@[simp]
theorem LieIdeal.extensionPBWCoalgEquiv_apply
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (x : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) :
    LieIdeal.extensionPBWCoalgEquiv I bQ bI x =
      LieIdeal.extensionPBWMap I bQ bI x :=
  rfl

/-- The quotient map sends the ideal enveloping algebra to scalars through
the counit. -/
theorem LieIdeal.pbwMap_quotient_comp_ideal
    (I : LieIdeal k L) :
    (UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.quotientMkLieHom I)).comp
      (UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.inclusionLieHom I)) =
    (Algebra.ofId k (UniversalEnvelopingAlgebra k (L ⧸ I))).comp
      (Coalgebra.eps (L := I)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply DFunLike.ext _ _
  intro x
  change UniversalEnvelopingAlgebra.pbwMap
      (LieIdeal.quotientMkLieHom I)
      (UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.inclusionLieHom I)
        (UniversalEnvelopingAlgebra.ι k x)) = _
  rw [UniversalEnvelopingAlgebra.pbwMap_iota,
    UniversalEnvelopingAlgebra.pbwMap_iota,
    LieIdeal.inclusionLieHom_apply,
    LieIdeal.quotientMk_coe]
  change UniversalEnvelopingAlgebra.ι k 0 =
    algebraMap k (UniversalEnvelopingAlgebra k (L ⧸ I))
      (Coalgebra.eps (UniversalEnvelopingAlgebra.ι k x))
  have heps : Coalgebra.eps (UniversalEnvelopingAlgebra.ι k x) = 0 :=
    Coalgebra.eps_iota x
  rw [heps]
  simp

/-- Applying the quotient map to the PBW tensor decomposition multiplies
the quotient factor by the counit of the ideal factor. -/
theorem LieIdeal.pbwMap_extensionPBW_tmul
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (q : UniversalEnvelopingAlgebra k (L ⧸ I))
    (a : UniversalEnvelopingAlgebra k I) :
    UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.quotientMkLieHom I)
        (LieIdeal.extensionPBWMap I bQ bI (q ⊗ₜ[k] a)) =
      q * algebraMap k (UniversalEnvelopingAlgebra k (L ⧸ I))
        (Coalgebra.counit (R := k) a) := by
  rw [LieIdeal.extensionPBWMap_tmul, map_mul]
  have hsection := LinearMap.congr_fun
    (LieIdeal.pbwMap_comp_ueaLinearSection I bQ bI) q
  change UniversalEnvelopingAlgebra.pbwMap
      (LieIdeal.quotientMkLieHom I)
      (LieIdeal.ueaLinearSection I bQ bI q) = q at hsection
  rw [hsection]
  have hideal := DFunLike.congr_fun
    (LieIdeal.pbwMap_quotient_comp_ideal I) a
  exact congrArg (fun z => q * z) hideal

@[simp]
theorem LieIdeal.pbwMap_ueaLinearSection
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (q : UniversalEnvelopingAlgebra k (L ⧸ I)) :
    UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.quotientMkLieHom I)
        (LieIdeal.ueaLinearSection I bQ bI q) = q := by
  exact LinearMap.congr_fun
    (LieIdeal.pbwMap_comp_ueaLinearSection I bQ bI) q

@[simp]
theorem LieIdeal.pbwMap_quotient_ideal
    (I : LieIdeal k L) (a : UniversalEnvelopingAlgebra k I) :
    UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.quotientMkLieHom I)
        (UniversalEnvelopingAlgebra.pbwMap
          (LieIdeal.inclusionLieHom I) a) =
      algebraMap k (UniversalEnvelopingAlgebra k (L ⧸ I))
        (Coalgebra.counit (R := k) a) := by
  exact DFunLike.congr_fun (LieIdeal.pbwMap_quotient_comp_ideal I) a

@[simp]
theorem LieIdeal.extensionPBWCoalgEquiv_symm_mul
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (q : UniversalEnvelopingAlgebra k (L ⧸ I))
    (a : UniversalEnvelopingAlgebra k I) :
    (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
        (LieIdeal.ueaLinearSection I bQ bI q *
          UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.inclusionLieHom I) a) = q ⊗ₜ[k] a := by
  rw [← LieIdeal.extensionPBWMap_tmul]
  exact (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm_apply_apply _

/-- Contract the middle quotient factor in
`U(L/I) ⊗ (U(L/I) ⊗ U(I))`. -/
noncomputable def LieIdeal.middleCounitContraction (I : LieIdeal k L) :
    (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
        UniversalEnvelopingAlgebra k I)) →ₗ[k]
      (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
        UniversalEnvelopingAlgebra k I) :=
  (LinearMap.lTensor (UniversalEnvelopingAlgebra k (L ⧸ I))
    ((TensorProduct.lid k (UniversalEnvelopingAlgebra k I)).toLinearMap.comp
      ((Coalgebra.counit (R := k) :
        UniversalEnvelopingAlgebra k (L ⧸ I) →ₗ[k] k).rTensor
          (UniversalEnvelopingAlgebra k I))))

@[simp]
theorem LieIdeal.middleCounitContraction_tmul (I : LieIdeal k L)
    (q r : UniversalEnvelopingAlgebra k (L ⧸ I))
    (a : UniversalEnvelopingAlgebra k I) :
    LieIdeal.middleCounitContraction I (q ⊗ₜ[k] (r ⊗ₜ[k] a)) =
      q ⊗ₜ[k] (Coalgebra.counit (R := k) r • a) := by
  simp [LieIdeal.middleCounitContraction, smul_tmul']

/-- The coaction obtained from the quotient map, transported back through
the PBW tensor decomposition and contracted in the middle quotient factor. -/
noncomputable def LieIdeal.extensionCoactionRetraction
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    UniversalEnvelopingAlgebra k L →ₗ[k]
      (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
        UniversalEnvelopingAlgebra k I) :=
  (LieIdeal.middleCounitContraction I).comp
    ((TensorProduct.map
      (UniversalEnvelopingAlgebra.pbwMap
        (LieIdeal.quotientMkLieHom I)).toLinearMap
      (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap).comp
        (Coalgebra.comul (R := k)))

/-- Contracting the transported quotient coaction is the inverse PBW
decomposition. -/
theorem LieIdeal.extensionCoactionRetraction_apply_extension
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (y : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I) :
    LieIdeal.extensionCoactionRetraction I bQ bI
        (LieIdeal.extensionPBWCoalgEquiv I bQ bI y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q a =>
      change LieIdeal.middleCounitContraction I
          (TensorProduct.map
            (UniversalEnvelopingAlgebra.pbwMap
              (LieIdeal.quotientMkLieHom I)).toLinearMap
            (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap
            (Coalgebra.comul (R := k)
              (LieIdeal.extensionPBWCoalgEquiv I bQ bI
                (q ⊗ₜ[k] a)))) = q ⊗ₜ[k] a
      rw [← CoalgHomClass.map_comp_comul_apply
        (LieIdeal.extensionPBWCoalgEquiv I bQ bI)]
      rw [TensorProduct.comul_tmul]
      let rq := Coalgebra.Repr.arbitrary k q
      let ra := Coalgebra.Repr.arbitrary k a
      rw [← rq.eq, ← ra.eq]
      simp only [tmul_sum, sum_tmul, map_sum]
      simp only [CoalgEquiv.toCoalgHom_eq_coe,
        CoalgHom.toLinearMap_eq_coe, CoalgEquiv.symm_toCoalgHom,
        LinearEquiv.symm_mk, CoalgEquiv.invFun_eq_symm,
        LinearMap.coe_coe, CoalgHom.coe_coe,
        AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.map_tmul, LieIdeal.extensionPBWCoalgEquiv_apply,
        LieIdeal.extensionPBWMap_tmul, AlgHom.toLinearMap_apply, map_mul,
        LieIdeal.pbwMap_ueaLinearSection,
        LieIdeal.pbwMap_quotient_ideal, LinearMap.coe_mk, AddHom.coe_mk,
        LieIdeal.extensionPBWCoalgEquiv_symm_mul,
        LieIdeal.middleCounitContraction_tmul, tmul_smul]
      have hq : ∑ x ∈ rq.index,
          Coalgebra.counit (R := k) (rq.right x) • rq.left x = q := by
        have h := Coalgebra.sum_tmul_counit_eq rq
        apply_fun TensorProduct.rid k
          (UniversalEnvelopingAlgebra k (L ⧸ I)) at h
        simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h
      have ha : ∑ x ∈ ra.index,
          Coalgebra.counit (R := k) (ra.left x) • ra.right x = a :=
        Coalgebra.sum_counit_smul ra
      calc
        _ = (∑ x ∈ rq.index,
              Coalgebra.counit (R := k) (rq.right x) • rq.left x) ⊗ₜ[k]
            (∑ x ∈ ra.index,
              Coalgebra.counit (R := k) (ra.left x) • ra.right x) := by
          rw [Finset.sum_comm]
          rw [sum_tmul]
          simp_rw [tmul_sum]
          apply Finset.sum_congr rfl
          intro iq hiq
          apply Finset.sum_congr rfl
          intro ia hia
          change Coalgebra.counit (R := k) (rq.right iq) •
              ((rq.left iq * algebraMap k
                (UniversalEnvelopingAlgebra k (L ⧸ I))
                  (Coalgebra.counit (R := k) (ra.left ia))) ⊗ₜ[k]
                ra.right ia) =
            (Coalgebra.counit (R := k) (rq.right iq) • rq.left iq) ⊗ₜ[k]
              (Coalgebra.counit (R := k) (ra.left ia) • ra.right ia)
          rw [← Algebra.commutes
            (Coalgebra.counit (R := k) (ra.left ia)) (rq.left iq),
            ← Algebra.smul_def]
          rw [TensorProduct.tmul_smul]
          simp only [smul_tmul', smul_smul]
          rw [mul_comm]
        _ = q ⊗ₜ[k] a := by rw [hq, ha]

/-! ## Tensor subspaces and the quotient coaction -/

/-- The subspace generated by pure tensors from two subspaces. -/
def tensorProductSubspace {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (P : Submodule k M) (Q : Submodule k N) :
    Submodule k (M ⊗[k] N) :=
  Submodule.map₂ (TensorProduct.mk k M N) P Q

/-- The left coaction along the enveloping-algebra quotient. -/
noncomputable def LieIdeal.leftQuotientCoaction (I : LieIdeal k L) :
    UniversalEnvelopingAlgebra k L →ₗ[k]
      (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
        UniversalEnvelopingAlgebra k L) :=
  (TensorProduct.map
    (UniversalEnvelopingAlgebra.pbwMap
      (LieIdeal.quotientMkLieHom I)).toLinearMap LinearMap.id).comp
        (Coalgebra.comul (R := k))

/-- The contracted coaction retraction is exactly the inverse PBW
equivalence. -/
theorem LieIdeal.extensionCoactionRetraction_eq_symm
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I) :
    LieIdeal.extensionCoactionRetraction I bQ bI =
      (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    (LieIdeal.extensionPBWCoalgEquiv I bQ bI).surjective x
  calc
    LieIdeal.extensionCoactionRetraction I bQ bI
        (LieIdeal.extensionPBWCoalgEquiv I bQ bI y) = y :=
      LieIdeal.extensionCoactionRetraction_apply_extension I bQ bI y
    _ = (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap
        (LieIdeal.extensionPBWCoalgEquiv I bQ bI y) :=
      ((LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm_apply_apply y).symm

/-- If the quotient coaction of a subspace has first tensor factor in
`P`, then its inverse-PBW image lies in `P ⊗ U(I)`. -/
theorem LieIdeal.extensionPBWEquiv_symm_mem_of_coaction_mem
 {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (P : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)))
    (x : UniversalEnvelopingAlgebra k L)
    (hx : LieIdeal.leftQuotientCoaction I x ∈
      tensorProductSubspace P ⊤) :
    (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm x ∈
      tensorProductSubspace P ⊤ := by
  let θinv := (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap
  let transported : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k L →ₗ[k]
      UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
        (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
          UniversalEnvelopingAlgebra k I) :=
    TensorProduct.map LinearMap.id θinv
  have htransported : transported (LieIdeal.leftQuotientCoaction I x) ∈
      tensorProductSubspace P ⊤ := by
    apply (show tensorProductSubspace P ⊤ ≤
      (tensorProductSubspace P ⊤).comap transported by
        apply Submodule.map₂_le.2
        intro q hq y hy
        change transported (q ⊗ₜ[k] y) ∈ tensorProductSubspace P ⊤
        rw [TensorProduct.map_tmul]
        exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P ⊤ hq trivial)
    exact hx
  have hcontracted : LieIdeal.middleCounitContraction I
      (transported (LieIdeal.leftQuotientCoaction I x)) ∈
        tensorProductSubspace P ⊤ := by
    let Good : Submodule k
        (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
          (UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
            UniversalEnvelopingAlgebra k I)) :=
      (tensorProductSubspace P ⊤).comap
        (LieIdeal.middleCounitContraction I)
    apply (show tensorProductSubspace P ⊤ ≤ Good by
      apply Submodule.map₂_le.2
      intro q hq z hz
      change LieIdeal.middleCounitContraction I (q ⊗ₜ[k] z) ∈
        tensorProductSubspace P ⊤
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [tmul_add, map_add] using
          (tensorProductSubspace P ⊤).add_mem hz hz'
      | tmul r a =>
          rw [LieIdeal.middleCounitContraction_tmul]
          exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P ⊤ hq trivial)
      htransported
  change θinv x ∈ _
  have heq : LieIdeal.extensionCoactionRetraction I bQ bI x = θinv x :=
    LinearMap.congr_fun
      (LieIdeal.extensionCoactionRetraction_eq_symm I bQ bI) x
  rw [← heq]
  have hR : LieIdeal.extensionCoactionRetraction I bQ bI x =
      LieIdeal.middleCounitContraction I
        (transported (LieIdeal.leftQuotientCoaction I x)) := by
    change LieIdeal.middleCounitContraction I
        (TensorProduct.map
          (UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.quotientMkLieHom I)).toLinearMap θinv
          (Coalgebra.comul (R := k) x)) = _
    apply congrArg (LieIdeal.middleCounitContraction I)
    change TensorProduct.map
        (UniversalEnvelopingAlgebra.pbwMap
          (LieIdeal.quotientMkLieHom I)).toLinearMap θinv
          (Coalgebra.comul (R := k) x) =
      TensorProduct.map LinearMap.id θinv
        (TensorProduct.map
          (UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.quotientMkLieHom I)).toLinearMap LinearMap.id
          (Coalgebra.comul (R := k) x))
    have hmaps := LinearMap.congr_fun
      (TensorProduct.map_comp LinearMap.id θinv
        (UniversalEnvelopingAlgebra.pbwMap
          (LieIdeal.quotientMkLieHom I)).toLinearMap LinearMap.id)
      (Coalgebra.comul (R := k) x)
    simpa only [LinearMap.id_comp, LinearMap.comp_id,
      LinearMap.comp_apply] using hmaps
  rw [hR]
  exact hcontracted

/-- The quotient coaction of a product `a σ(c)` has first tensor factor in
the product of the quotient image of the coefficient coalgebra with `C`. -/
theorem LieIdeal.leftQuotientCoaction_mul_section_mem
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (A : FiniteSubcoalgebra k (UniversalEnvelopingAlgebra k L))
    (C : FiniteSubcoalgebra k
      (UniversalEnvelopingAlgebra k (L ⧸ I)))
    (a : UniversalEnvelopingAlgebra k L) (ha : a ∈ A.carrier)
    (c : UniversalEnvelopingAlgebra k (L ⧸ I)) (hc : c ∈ C.carrier) :
    LieIdeal.leftQuotientCoaction I
        (a * LieIdeal.ueaLinearSection I bQ bI c) ∈
      tensorProductSubspace
        (actionSubspace
          (A.carrier.map
            (UniversalEnvelopingAlgebra.pbwMap
              (LieIdeal.quotientMkLieHom I)).toLinearMap)
          C.carrier) ⊤ := by
  let π := UniversalEnvelopingAlgebra.pbwMapCoalgHom
    (LieIdeal.quotientMkLieHom I)
  let σ := LieIdeal.ueaLinearSectionCoalgHom I bQ bI
  obtain ⟨za, hza⟩ := A.isSubcoalgebra ha
  obtain ⟨zc, hzc⟩ := C.isSubcoalgebra hc
  change TensorProduct.map π.toLinearMap LinearMap.id
      (Coalgebra.comul (R := k)
        (a * LieIdeal.ueaLinearSection I bQ bI c)) ∈ _
  rw [Bialgebra.comul_mul]
  rw [show Coalgebra.comul (R := k)
      (LieIdeal.ueaLinearSection I bQ bI c) =
        TensorProduct.map σ.toLinearMap σ.toLinearMap
          (Coalgebra.comul (R := k) c) from
    (CoalgHomClass.map_comp_comul_apply σ c).symm]
  rw [← hza, ← hzc]
  clear hza hzc ha hc a c
  induction za using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, add_mul]
      exact (tensorProductSubspace _ _).add_mem hx hy
  | tmul a₁ a₂ =>
      induction zc using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simp only [map_add, mul_add]
          exact (tensorProductSubspace _ _).add_mem hx hy
      | tmul c₁ c₂ =>
          simp only [TensorProduct.map_tmul,
            Algebra.TensorProduct.tmul_mul_tmul]
          change (UniversalEnvelopingAlgebra.pbwMap
              (LieIdeal.quotientMkLieHom I)
              ((a₁ : UniversalEnvelopingAlgebra k L) *
                LieIdeal.ueaLinearSection I bQ bI c₁)) ⊗ₜ[k]
              ((a₂ : UniversalEnvelopingAlgebra k L) *
                LieIdeal.ueaLinearSection I bQ bI c₂) ∈ _
          rw [map_mul, LieIdeal.pbwMap_ueaLinearSection I bQ bI]
          apply Submodule.mem_map₂ (TensorProduct.mk k _ _)
          · rw [actionSubspace_eq_map₂]
            exact Submodule.mem_map₂
              (Algebra.lsmul k k
                (UniversalEnvelopingAlgebra k (L ⧸ I))).toLinearMap
              (A.carrier.map
                (UniversalEnvelopingAlgebra.pbwMap
                  (LieIdeal.quotientMkLieHom I)).toLinearMap) C.carrier
              ⟨a₁, a₁.2, rfl⟩ c₁.2
          · trivial

/-! ## Finite support in one tensor factor -/

/-- A finite-dimensional subspace contained in `P ⊗ N` uses only a
finite-dimensional subspace of the second tensor factor. -/
theorem exists_finite_right_tensor_support
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (P : Submodule k M) (X : Submodule k (M ⊗[k] N))
    [FiniteDimensional k X]
    (hX : X ≤ tensorProductSubspace P ⊤) :
    ∃ D : Submodule k N, FiniteDimensional k D ∧
      X ≤ tensorProductSubspace P D := by
  classical
  obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P
  let proj : M →ₗ[k] P := P.projectionOnto Q hPQ
  let r : M →ₗ[k] M := P.subtype.comp proj
  have hr (x : M) (hx : x ∈ P) : r x = x := by
    let xp : P := ⟨x, hx⟩
    change ((P.subtype.comp proj) x) = x
    change (proj x : M) = x
    rw [show x = (xp : M) from rfl,
      Submodule.projectionOnto_apply_left]
  let T : (M ⊗[k] N) →ₗ[k] (M ⊗[k] N) :=
    TensorProduct.map r LinearMap.id
  have hfixed : ∀ x ∈ tensorProductSubspace P ⊤, T x = x := by
    intro x hx
    let Fix : Submodule k (M ⊗[k] N) := LinearMap.ker
      (T - (LinearMap.id : (M ⊗[k] N) →ₗ[k] (M ⊗[k] N)))
    have hle : tensorProductSubspace P ⊤ ≤ Fix := by
      apply Submodule.map₂_le.2
      intro m hm n hn
      change (T - (LinearMap.id :
        (M ⊗[k] N) →ₗ[k] (M ⊗[k] N))) (m ⊗ₜ[k] n) = 0
      simp [T, hr m hm]
    have := hle hx
    change (T - (LinearMap.id :
      (M ⊗[k] N) →ₗ[k] (M ⊗[k] N))) x = 0 at this
    exact sub_eq_zero.mp (by simpa using this)
  let e := Module.finBasis k X
  let pieces : ∀ i, Finset (M × N) := fun i =>
    Classical.choose (TensorProduct.exists_finset (e i : M ⊗[k] N))
  have hpieces (i) : (e i : M ⊗[k] N) =
      ∑ p ∈ pieces i, p.1 ⊗ₜ[k] p.2 :=
    Classical.choose_spec
      (TensorProduct.exists_finset (e i : M ⊗[k] N))
  let rights : Finset N := Finset.univ.biUnion fun i =>
    (pieces i).image Prod.snd
  let D : Submodule k N := Submodule.span k (rights : Set N)
  have hDfd : FiniteDimensional k D := by
    dsimp [D]
    infer_instance
  refine ⟨D, hDfd, ?_⟩
  intro x hx
  let xX : X := ⟨x, hx⟩
  have hxsum : ∑ i, (e.repr xX i) • (e i : M ⊗[k] N) = x := by
    have h := congrArg X.subtype (e.sum_repr xX)
    rw [map_sum] at h
    simp only [LinearMap.map_smul_of_tower] at h
    exact h
  rw [← hxsum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have heiFixed : T (e i : M ⊗[k] N) = (e i : M ⊗[k] N) :=
    hfixed _ (hX (e i).2)
  rw [← heiFixed, hpieces, map_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [TensorProduct.map_tmul]
  apply Submodule.mem_map₂ (TensorProduct.mk k M N) P D
  · exact (proj p.1).2
  · apply Submodule.subset_span
    change p.2 ∈ rights
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem tensorProductSubspace_eq_range_mapIncl
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (P : Submodule k M) (Q : Submodule k N) :
    tensorProductSubspace P Q = LinearMap.range (TensorProduct.mapIncl P Q) := by
  apply le_antisymm
  · apply Submodule.map₂_le.2
    intro p hp q hq
    exact ⟨(⟨p, hp⟩ : P) ⊗ₜ[k] (⟨q, hq⟩ : Q), rfl⟩
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using
        (tensorProductSubspace P Q).add_mem hx hy
    | tmul p q =>
        exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P Q p.2 q.2

theorem tensorProductSubspace_mono
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    {P P' : Submodule k M} {Q Q' : Submodule k N}
    (hP : P ≤ P') (hQ : Q ≤ Q') :
    tensorProductSubspace P Q ≤ tensorProductSubspace P' Q' := by
  apply Submodule.map₂_le.2
  intro p hp q hq
  exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P' Q'
    (hP hp) (hQ hq)

theorem finiteDimensional_tensorProductSubspace
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (P : Submodule k M) (Q : Submodule k N)
    [FiniteDimensional k P] [FiniteDimensional k Q] :
    FiniteDimensional k (tensorProductSubspace P Q) := by
  let f : (P ⊗[k] Q) →ₗ[k] tensorProductSubspace P Q :=
    (TensorProduct.mapIncl P Q).codRestrict _ (fun z => by
      rw [tensorProductSubspace_eq_range_mapIncl]
      exact ⟨z, rfl⟩)
  exact FiniteDimensional.of_surjective f (by
    rintro ⟨x, hx⟩
    rw [tensorProductSubspace_eq_range_mapIncl] at hx
    obtain ⟨z, rfl⟩ := hx
    exact ⟨z, rfl⟩)

theorem sfinrank_tensorProductSubspace
    {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (P : Submodule k M) (Q : Submodule k N) :
    sfinrank k (tensorProductSubspace P Q) =
      sfinrank k P * sfinrank k Q := by
  rw [tensorProductSubspace_eq_range_mapIncl]
  have h := (LinearEquiv.ofInjective (TensorProduct.mapIncl P Q)
    (Module.Flat.tensorProduct_mapIncl_injective_of_right P Q)).finrank_eq
  change Module.finrank k (P ⊗[k] Q) =
    Module.finrank k (LinearMap.range (TensorProduct.mapIncl P Q)) at h
  simp only [sfinrank]
  rw [← h, Module.finrank_tensorProduct]

/-- Finite PBW defect: multiplying a finite quotient coalgebra section by a
finite coefficient coalgebra introduces only finitely many ideal
coefficients, while the quotient coordinate stays in the expected product
space. -/
theorem LieIdeal.exists_finite_extension_defect
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (A : FiniteSubcoalgebra k (UniversalEnvelopingAlgebra k L))
    (C : FiniteSubcoalgebra k
      (UniversalEnvelopingAlgebra k (L ⧸ I))) :
    ∃ D : Submodule k (UniversalEnvelopingAlgebra k I),
      FiniteDimensional k D ∧
      (actionSubspace A.carrier
          (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI))).map
            (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap ≤
        tensorProductSubspace
          (actionSubspace
            (A.carrier.map
              (UniversalEnvelopingAlgebra.pbwMap
                (LieIdeal.quotientMkLieHom I)).toLinearMap)
            C.carrier) D := by
  let X : Submodule k (UniversalEnvelopingAlgebra k L) :=
    actionSubspace A.carrier
      (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI))
  let θinv := (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm.toLinearMap
  let X' := X.map θinv
  let P : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    actionSubspace
      (A.carrier.map
        (UniversalEnvelopingAlgebra.pbwMap
          (LieIdeal.quotientMkLieHom I)).toLinearMap)
      C.carrier
  let _ : FiniteDimensional k X := by
    dsimp [X]
    exact finiteDimensional_actionSubspace _ _
  let _ : FiniteDimensional k X' := by
    dsimp [X']
    infer_instance
  have hX' : X' ≤ tensorProductSubspace P ⊤ := by
    rintro _ ⟨x, hx, rfl⟩
    apply LieIdeal.extensionPBWEquiv_symm_mem_of_coaction_mem I bQ bI P
    change x ∈ actionSubspace A.carrier
      (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI)) at hx
    rw [actionSubspace_eq_map₂] at hx
    let Good : Submodule k (UniversalEnvelopingAlgebra k L) :=
      (tensorProductSubspace P ⊤).comap
        (LieIdeal.leftQuotientCoaction I)
    apply (show Submodule.map₂
        (Algebra.lsmul k k (UniversalEnvelopingAlgebra k L)).toLinearMap
        A.carrier
        (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI)) ≤ Good by
      apply Submodule.map₂_le.2
      intro a ha y hy
      rcases hy with ⟨c, hc, rfl⟩
      exact LieIdeal.leftQuotientCoaction_mul_section_mem
        I bQ bI A C a ha c hc) hx
  obtain ⟨D, hDfd, hD⟩ :=
    exists_finite_right_tensor_support P X' hX'
  exact ⟨D, hDfd, hD⟩

/-- Right multiplication by an ideal coefficient acts only on the ideal
factor of the PBW tensor decomposition. -/
theorem LieIdeal.extensionPBWEquiv_symm_mul_ideal_mem
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I))
    (bI : Basis α k I)
    (P : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)))
    (D E : Submodule k (UniversalEnvelopingAlgebra k I))
    (z : UniversalEnvelopingAlgebra k (L ⧸ I) ⊗[k]
      UniversalEnvelopingAlgebra k I)
    (hz : z ∈ tensorProductSubspace P D)
    (e : UniversalEnvelopingAlgebra k I) (he : e ∈ E) :
    (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
        (LieIdeal.extensionPBWCoalgEquiv I bQ bI z *
          UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.inclusionLieHom I) e) ∈
      tensorProductSubspace P (actionSubspace D E) := by
  rw [tensorProductSubspace_eq_range_mapIncl] at hz
  obtain ⟨zDE, rfl⟩ := hz
  induction zDE using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, add_mul]
      exact (tensorProductSubspace P (actionSubspace D E)).add_mem hx hy
  | tmul q d =>
      change (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
          ((LieIdeal.ueaLinearSection I bQ bI q *
              UniversalEnvelopingAlgebra.pbwMap
                (LieIdeal.inclusionLieHom I) d) *
            UniversalEnvelopingAlgebra.pbwMap
              (LieIdeal.inclusionLieHom I) e) ∈ _
      rw [mul_assoc, ← map_mul]
      rw [LieIdeal.extensionPBWCoalgEquiv_symm_mul]
      apply Submodule.mem_map₂ (TensorProduct.mk k _ _)
      · exact q.2
      · rw [actionSubspace_eq_map₂]
        exact Submodule.mem_map₂
          (Algebra.lsmul k k (UniversalEnvelopingAlgebra k I)).toLinearMap
          D E d.2 he

section AlgebraicAmenability

variable {A : Type*} {Q : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- The algebraic expansion `E + F E`, stated without any coalgebraic
assumptions on the acting algebra. -/
def algebraModuleExpansion (F : Submodule k A) (E : Submodule k Q) :
    Submodule k Q :=
  E ⊔ Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E

/-- Elek amenability for a module over an arbitrary associative algebra. -/
def IsAlgebraicallyAmenableModule : Prop :=
  ∀ (F : Submodule k A), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k Q,
        E ≠ ⊥ ∧ FiniteDimensional k E ∧
          (sfinrank k (algebraModuleExpansion F E) : ℚ) ≤
            (1 + ε) * sfinrank k E

end AlgebraicAmenability

section FreeModuleSupport

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- A finite-dimensional subspace of a free `A`-module uses only finitely
many coordinates of any chosen `A`-basis. -/
theorem Basis.exists_finset_support
    (b : Basis ι A Q) (E : Submodule k Q) [FiniteDimensional k E] :
    ∃ s : Finset ι, ∀ x ∈ E, (b.repr x).support ⊆ s := by
  classical
  let e := Module.finBasis k E
  let s : Finset ι := Finset.univ.biUnion fun i =>
    (b.repr (e i : Q)).support
  refine ⟨s, ?_⟩
  intro x hx
  let xE : E := ⟨x, hx⟩
  have hxsum : ∑ i, (e.repr xE i) • (e i : Q) = x := by
    have h := congrArg E.subtype (e.sum_repr xE)
    rw [map_sum] at h
    simp only [LinearMap.map_smul_of_tower] at h
    exact h
  rw [← hxsum, map_sum]
  refine Finsupp.support_finsetSum.trans ?_
  apply Finset.biUnion_subset.2
  intro i hi
  have heq := (b.repr : Q →ₗ[A] ι →₀ A).map_smul_of_tower
    (e.repr xE i) (e i : Q)
  change (((b.repr : Q →ₗ[A] ι →₀ A)
    ((e.repr xE i) • (e i : Q))).support) ⊆ s
  rw [heq]
  exact Finsupp.support_smul.trans
    (Finset.subset_biUnion_of_mem
      (fun j => (b.repr (e j : Q)).support) (Finset.mem_univ i))

end FreeModuleSupport

section FreeModuleLayers

variable {A : Type*} {Q : Type*} {ι : Type*} [Fintype ι]
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

omit [Module A Q] [IsScalarTower k A Q] in
/-- The finite weighted-average step in the standard proof that amenability
of a free `A`-module implies amenability of `A`.  The geometric construction
of the layers is kept separate from this numerical lemma. -/
theorem exists_layer_ratio_le
    (F : Submodule k A) [FiniteDimensional k F]
    (E Eplus : Submodule k Q) [FiniteDimensional k E]
    [FiniteDimensional k Eplus] (hE : E ≠ ⊥)
    (V Vplus : ι → Submodule k A)
    (hVfd : ∀ i, FiniteDimensional k (V i))
    (hVplusfd : ∀ i, FiniteDimensional k (Vplus i))
    (hsource : ∑ i, sfinrank k (V i) = sfinrank k E)
    (htarget : ∑ i, sfinrank k (Vplus i) = sfinrank k Eplus)
    (haction : ∀ i, algebraModuleExpansion F (V i) ≤ Vplus i) :
    ∃ i, V i ≠ ⊥ ∧
      (sfinrank k (algebraModuleExpansion F (V i)) : ℚ) /
          sfinrank k (V i) ≤
        (sfinrank k Eplus : ℚ) / sfinrank k E := by
  classical
  let _ (i : ι) : FiniteDimensional k (V i) := hVfd i
  let _ (i : ι) : FiniteDimensional k (Vplus i) := hVplusfd i
  have hplus (i : ι) : FiniteDimensional k
      (algebraModuleExpansion F (V i)) := by
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k A).toLinearMap F (V i)) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k A).toLinearMap F (V i)) := hmap
    rw [algebraModuleExpansion]
    infer_instance
  let _ (i : ι) : FiniteDimensional k
      (algebraModuleExpansion F (V i)) := hplus i
  have hmono (i : ι) :
      sfinrank k (algebraModuleExpansion F (V i)) ≤
        sfinrank k (Vplus i) :=
    Submodule.finrank_mono (haction i)
  let cert : RoundingCertificate ι := {
    w := fun _ => 1
    cDim := fun i => sfinrank k (V i)
    fcDim := fun i => sfinrank k (algebraModuleExpansion F (V i))
    dimE := sfinrank k E
    dimFE := sfinrank k Eplus
    w_nonneg := fun _ => by norm_num
    cDim_nonneg := fun _ => by positivity
    fcDim_nonneg := fun _ => by positivity
    dimE_pos := by
      let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
      exact_mod_cast Module.finrank_pos (R := k) (M := E)
    mass := by
      simp only [one_mul]
      exact_mod_cast hsource
    plus_mass := by
      have hsum : ∑ i, sfinrank k (algebraModuleExpansion F (V i)) ≤
          ∑ i, sfinrank k (Vplus i) :=
        Finset.sum_le_sum fun i _ => hmono i
      simp only [one_mul]
      exact_mod_cast hsum.trans_eq htarget }
  obtain ⟨i, _, hi, hratio⟩ := cert.exists_ratio_le
  refine ⟨i, ?_, hratio⟩
  intro hbot
  change 0 < (sfinrank k (V i) : ℚ) at hi
  rw [hbot] at hi
  simp [sfinrank] at hi

end FreeModuleLayers

section PiFlag

variable {A : Type*} [Ring A] [Algebra k A]

/-- The first `j` coordinates in the finite free module `Fin n → A`. -/
def piPrefix (n j : ℕ) : Submodule k (Fin n → A) where
  carrier := {x | ∀ i : Fin n, j ≤ i.1 → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro r x hx i hi
    simp [hx i hi]

theorem piPrefix_mono {n i j : ℕ} (hij : i ≤ j) :
    piPrefix (k := k) (A := A) n i ≤ piPrefix n j := by
  intro x hx a ha
  exact hx a (hij.trans ha)

@[simp]
theorem piPrefix_zero (n : ℕ) :
    piPrefix (k := k) (A := A) n 0 = ⊥ := by
  ext x
  simp [piPrefix, funext_iff]

@[simp]
theorem piPrefix_top (n : ℕ) :
    piPrefix (k := k) (A := A) n n = ⊤ := by
  ext x
  simp [piPrefix]

/-- Projection onto one coordinate, as a `k`-linear map. -/
def piCoordinate (n : ℕ) (i : Fin n) : (Fin n → A) →ₗ[k] A :=
  LinearMap.proj i

@[simp]
theorem piCoordinate_apply (n : ℕ) (i : Fin n) (x : Fin n → A) :
    piCoordinate (k := k) n i x = x i :=
  rfl

/-- The `i`th successive coordinate layer of a subspace of a finite free
module. -/
def piLayer {n : ℕ} (E : Submodule k (Fin n → A)) (i : Fin n) :
    Submodule k A :=
  (E ⊓ piPrefix n (i.1 + 1)).map (piCoordinate n i)

theorem mem_piPrefix_succ_and_coordinate_zero_iff
    {n : ℕ} (i : Fin n) (x : Fin n → A) :
    x ∈ piPrefix (k := k) (A := A) n (i.1 + 1) ∧ x i = 0 ↔
      x ∈ piPrefix (k := k) (A := A) n i.1 := by
  constructor
  · rintro ⟨hx, hxi⟩ a ha
    rcases ha.eq_or_lt with heq | hlt
    · have hai : a = i := Fin.ext heq.symm
      simpa [hai] using hxi
    · exact hx a (Nat.succ_le_iff.2 hlt)
  · intro hx
    exact ⟨piPrefix_mono (k := k) (A := A) (Nat.le_succ i.1) hx,
      hx i le_rfl⟩

theorem piLayer_finrank_add {n : ℕ}
    (E : Submodule k (Fin n → A)) [FiniteDimensional k E] (i : Fin n) :
    sfinrank k (E ⊓ piPrefix n i.1) + sfinrank k (piLayer E i) =
      sfinrank k (E ⊓ piPrefix n (i.1 + 1)) := by
  let S : Submodule k (Fin n → A) := E ⊓ piPrefix n i.1
  let Ssucc : Submodule k (Fin n → A) :=
    E ⊓ piPrefix n (i.1 + 1)
  have hle : S ≤ Ssucc := inf_le_inf_left E
    (piPrefix_mono (k := k) (A := A) (Nat.le_succ i.1))
  let f : Ssucc →ₗ[k] A := (piCoordinate n i).domRestrict Ssucc
  have hker : LinearMap.ker f = S.comap Ssucc.subtype := by
    ext x
    change (x : Fin n → A) i = 0 ↔ (x : Fin n → A) ∈ S
    rw [show (x : Fin n → A) ∈ S ↔
        (x : Fin n → A) ∈ piPrefix n i.1 by
      simp only [S, Submodule.mem_inf]
      exact and_iff_right x.2.1]
    constructor
    · intro hxzero
      exact (mem_piPrefix_succ_and_coordinate_zero_iff
        (k := k) (A := A) i (x : Fin n → A)).mp ⟨x.2.2, hxzero⟩
    · intro hxprefix
      exact ((mem_piPrefix_succ_and_coordinate_zero_iff
        (k := k) (A := A) i (x : Fin n → A)).mpr hxprefix).2
  have hrange : LinearMap.range f = piLayer E i := by
    change LinearMap.range ((piCoordinate n i).domRestrict Ssucc) = _
    rw [LinearMap.range_domRestrict]
    rfl
  have hkerDim : finrank k (LinearMap.ker f) = finrank k S := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hkerDim] at hrank
  change finrank k S + finrank k (piLayer E i) = finrank k Ssucc
  simpa [add_comm] using hrank

theorem sum_piLayer_finrank {n : ℕ}
    (E : Submodule k (Fin n → A)) [FiniteDimensional k E] :
    ∑ i : Fin n, sfinrank k (piLayer E i) = sfinrank k E := by
  classical
  let d : ℕ → ℕ := fun j => sfinrank k (E ⊓ piPrefix n j)
  let layer : ℕ → ℕ := fun j =>
    if hj : j < n then sfinrank k (piLayer E ⟨j, hj⟩) else 0
  have hd : Monotone d := by
    intro i j hij
    exact Submodule.finrank_mono
      (inf_le_inf_left E (piPrefix_mono (k := k) (A := A) hij))
  have hlayer {j : ℕ} (hj : j < n) :
      d (j + 1) - d j = layer j := by
    have hrec := piLayer_finrank_add E ⟨j, hj⟩
    apply (Nat.sub_eq_iff_eq_add' (hd (Nat.le_succ j))).2
    dsimp only [d, layer]
    rw [dite_eq_left hj]
    exact hrec.symm
  calc
    ∑ i : Fin n, sfinrank k (piLayer E i) =
        ∑ j ∈ Finset.range n, layer j := by
      simpa [layer] using
        (Fin.sum_univ_eq_sum_range layer n)
    _ = ∑ j ∈ Finset.range n, (d (j + 1) - d j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hlayer (Finset.mem_range.1 hj)).symm
    _ = d n - d 0 := Finset.sum_range_tsub hd n
    _ = sfinrank k E := by
      dsimp only [d]
      rw [piPrefix_top (k := k) (A := A), inf_top_eq,
        piPrefix_zero (k := k) (A := A), inf_bot_eq]
      simp [sfinrank]

theorem algebraModuleExpansion_piLayer_le {n : ℕ}
    (F : Submodule k A) (E : Submodule k (Fin n → A)) (i : Fin n) :
    algebraModuleExpansion F (piLayer E i) ≤
      piLayer (algebraModuleExpansion F E) i := by
  rw [algebraModuleExpansion, sup_le_iff]
  constructor
  · rintro v ⟨x, hx, rfl⟩
    exact ⟨x, ⟨(le_sup_left : E ≤ algebraModuleExpansion F E) hx.1,
      hx.2⟩, rfl⟩
  · apply Submodule.map₂_le.2
    intro a ha v hv
    rcases hv with ⟨x, hx, rfl⟩
    let y : Fin n → A := a • (x : Fin n → A)
    have hyE : y ∈ algebraModuleExpansion F E := by
      rw [algebraModuleExpansion]
      apply (le_sup_right :
        Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E ≤ _)
      exact Submodule.mem_map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap
        F E ha hx.1
    have hyPrefix : y ∈ piPrefix (k := k) (A := A) n (i.1 + 1) := by
      intro j hj
      simp [y, hx.2 j hj]
    refine ⟨y, ⟨hyE, hyPrefix⟩, ?_⟩
    rfl

/-- Amenability descends from a nonzero finite free module to its coefficient
algebra.  This is the finite-support core of the free-module observation in
the proof of the subalgebra clause of Theorem D. -/
theorem IsAlgebraicallyAmenableModule.coefficient_of_pi (n : ℕ)
    (h : IsAlgebraicallyAmenableModule
      (k := k) (A := A) (Q := Fin n → A)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  intro F hF ε hε
  let _ : FiniteDimensional k F := hF
  obtain ⟨E, hE, hEfd, hEplus⟩ := h F inferInstance ε hε
  let _ : FiniteDimensional k E := hEfd
  let Eplus : Submodule k (Fin n → A) := algebraModuleExpansion F E
  have hEplusfd : FiniteDimensional k Eplus := by
    dsimp [Eplus, algebraModuleExpansion]
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E) := hmap
    exact Submodule.finiteDimensional_sup E
      (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E)
  let _ : FiniteDimensional k Eplus := hEplusfd
  have hlayerfd (i : Fin n) : FiniteDimensional k (piLayer E i) := by
    rw [piLayer]
    infer_instance
  have hlayerplusfd (i : Fin n) : FiniteDimensional k (piLayer Eplus i) := by
    rw [piLayer]
    infer_instance
  obtain ⟨i, hVi, hratio⟩ := exists_layer_ratio_le
    F E Eplus hE (piLayer E) (piLayer Eplus)
    hlayerfd hlayerplusfd (sum_piLayer_finrank E)
    (sum_piLayer_finrank Eplus) (algebraModuleExpansion_piLayer_le F E)
  let _ : FiniteDimensional k (piLayer E i) := hlayerfd i
  let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let _ : Nontrivial (piLayer E i) :=
    Submodule.nontrivial_iff_ne_bot.mpr hVi
  have hEpos : (0 : ℚ) < sfinrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hVpos : (0 : ℚ) < sfinrank k (piLayer E i) := by
    exact_mod_cast Module.finrank_pos (R := k) (M := piLayer E i)
  have hsource : (sfinrank k Eplus : ℚ) / sfinrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).2 hEplus
  refine ⟨piLayer E i, hVi, hlayerfd i, ?_⟩
  exact (div_le_iff₀ hVpos).1 (hratio.trans hsource)

end PiFlag

section FiniteCoordinates

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- Restrict the coordinates of an `A`-basis to a finite set and enumerate
that set by `Fin`. -/
noncomputable def Basis.finiteCoordinates
    (b : Basis ι A Q) (s : Finset ι) :
    Q →ₗ[k] (Fin s.card → A) where
  toFun x i := b.repr x (s.equivFin.symm i)
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    change b.repr (r • x) (s.equivFin.symm i) =
      r • b.repr x (s.equivFin.symm i)
    exact congrArg (fun z : ι →₀ A => z (s.equivFin.symm i))
      ((b.repr : Q →ₗ[A] ι →₀ A).map_smul_of_tower r x)

theorem Basis.finiteCoordinates_smul
    (b : Basis ι A Q) (s : Finset ι) (a : A) (x : Q) :
    Basis.finiteCoordinates (k := k) b s (a • x) =
      a • Basis.finiteCoordinates (k := k) b s x := by
  ext i
  exact congrArg (fun z : ι →₀ A => z (s.equivFin.symm i))
    (b.repr.map_smul a x)

theorem Basis.finiteCoordinates_injectiveOn
    (b : Basis ι A Q) (s : Finset ι) {x y : Q}
    (hx : (b.repr x).support ⊆ s) (hy : (b.repr y).support ⊆ s)
    (hxy : Basis.finiteCoordinates (k := k) b s x =
      Basis.finiteCoordinates (k := k) b s y) :
    x = y := by
  apply b.repr.injective
  ext j
  by_cases hj : j ∈ s
  · let js : s := ⟨j, hj⟩
    have h := congrFun hxy (s.equivFin js)
    simpa [Basis.finiteCoordinates, js] using h
  · have hxzero : b.repr x j = 0 := by
      rw [← Finsupp.notMem_support_iff]
      exact fun hmem => hj (hx hmem)
    have hyzero : b.repr y j = 0 := by
      rw [← Finsupp.notMem_support_iff]
      exact fun hmem => hj (hy hmem)
    rw [hxzero, hyzero]

end FiniteCoordinates

section FreeModuleDescent

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- The one-shot free-module coefficient extraction used in the proof that
an amenable free module has an amenable coefficient algebra. -/
theorem exists_coefficient_ratio_le_of_basis
    (b : Basis ι A Q) (F : Submodule k A) [FiniteDimensional k F]
    (E : Submodule k Q) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ V : Submodule k A, V ≠ ⊥ ∧ FiniteDimensional k V ∧
      (sfinrank k (algebraModuleExpansion F V) : ℚ) / sfinrank k V ≤
        (sfinrank k (algebraModuleExpansion F E) : ℚ) / sfinrank k E := by
  classical
  let Eplus : Submodule k Q := algebraModuleExpansion F E
  have hEplusfd : FiniteDimensional k Eplus := by
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E) := hmap
    dsimp [Eplus, algebraModuleExpansion]
    exact Submodule.finiteDimensional_sup E
      (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E)
  let _ : FiniteDimensional k Eplus := hEplusfd
  obtain ⟨s, hs⟩ := Basis.exists_finset_support (k := k) b Eplus
  let T : Q →ₗ[k] (Fin s.card → A) :=
    Basis.finiteCoordinates (k := k) b s
  have hEle : E ≤ Eplus := le_sup_left
  have hTinjEplus : Function.Injective (T.domRestrict Eplus) := by
    intro x y hxy
    apply Subtype.ext
    exact Basis.finiteCoordinates_injectiveOn (k := k) b s
      (hs x x.2) (hs y y.2) hxy
  have hTinjE : Function.Injective (T.domRestrict E) := by
    intro x y hxy
    apply Subtype.ext
    exact Basis.finiteCoordinates_injectiveOn (k := k) b s
      (hs x (hEle x.2)) (hs y (hEle y.2)) hxy
  let E' : Submodule k (Fin s.card → A) := E.map T
  let Eplus' : Submodule k (Fin s.card → A) := Eplus.map T
  have hdimE : sfinrank k E' = sfinrank k E := by
    have h := (LinearEquiv.ofInjective (T.domRestrict E) hTinjE).finrank_eq
    change finrank k E = finrank k (LinearMap.range (T.domRestrict E)) at h
    rw [LinearMap.range_domRestrict] at h
    exact h.symm
  have hdimEplus : sfinrank k Eplus' = sfinrank k Eplus := by
    have h :=
      (LinearEquiv.ofInjective (T.domRestrict Eplus) hTinjEplus).finrank_eq
    change finrank k Eplus =
      finrank k (LinearMap.range (T.domRestrict Eplus)) at h
    rw [LinearMap.range_domRestrict] at h
    exact h.symm
  have hE'fd : FiniteDimensional k E' := by
    dsimp [E']
    infer_instance
  let _ : FiniteDimensional k E' := hE'fd
  have hE' : E' ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdimE
    have hzero : sfinrank k E = 0 := by simpa [sfinrank] using hdimE.symm
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    exact (Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E))) hzero
  let Target : Submodule k (Fin s.card → A) :=
    algebraModuleExpansion F E'
  have hTargetfd : FiniteDimensional k Target := by
    dsimp [Target, algebraModuleExpansion]
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin s.card → A)).toLinearMap
          F E') := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin s.card → A)).toLinearMap
          F E') := hmap
    exact Submodule.finiteDimensional_sup E' _
  let _ : FiniteDimensional k Target := hTargetfd
  have hTarget : Target ≤ Eplus' := by
    change algebraModuleExpansion F E' ≤ Eplus'
    rw [algebraModuleExpansion, sup_le_iff]
    constructor
    · exact Submodule.map_mono hEle
    · apply Submodule.map₂_le.2
      intro a ha y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hax : a • x ∈ Eplus := by
        change a • x ∈ algebraModuleExpansion F E
        rw [algebraModuleExpansion]
        apply (le_sup_right :
          Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E ≤ _)
        exact Submodule.mem_map₂ (Algebra.lsmul k k Q).toLinearMap F E ha hx
      refine ⟨a • x, hax, ?_⟩
      exact Basis.finiteCoordinates_smul (k := k) b s a x
  have hlayerfd (i : Fin s.card) : FiniteDimensional k (piLayer E' i) := by
    rw [piLayer]
    infer_instance
  have hlayerTargetfd (i : Fin s.card) :
      FiniteDimensional k (piLayer Target i) := by
    rw [piLayer]
    infer_instance
  obtain ⟨i, hVi, hratio⟩ := exists_layer_ratio_le
    F E' Target hE' (piLayer E') (piLayer Target)
    hlayerfd hlayerTargetfd (sum_piLayer_finrank E')
    (sum_piLayer_finrank Target) (algebraModuleExpansion_piLayer_le F E')
  have htargetDim : sfinrank k Target ≤ sfinrank k Eplus' :=
    Submodule.finrank_mono hTarget
  have htargetRatio :
      (sfinrank k Target : ℚ) / sfinrank k E' ≤
        (sfinrank k Eplus : ℚ) / sfinrank k E := by
    rw [hdimE, ← hdimEplus]
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    have hEpos : (0 : ℚ) < sfinrank k E := by
      exact_mod_cast Module.finrank_pos (R := k) (M := E)
    exact (div_le_div_iff_of_pos_right hEpos).2 (by exact_mod_cast htargetDim)
  exact ⟨piLayer E' i, hVi, hlayerfd i, hratio.trans htargetRatio⟩

/-- Standard free-module observation from the proof of Theorem D: if a
nonzero free left `A`-module is algebraically amenable, then `A` is
algebraically amenable. -/
theorem IsAlgebraicallyAmenableModule.coefficient_of_basis
    (b : Basis ι A Q)
    (hQ : IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := Q)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  intro F hF ε hε
  let _ : FiniteDimensional k F := hF
  obtain ⟨E, hE, hEfd, hEfolner⟩ := hQ F inferInstance ε hε
  let _ : FiniteDimensional k E := hEfd
  obtain ⟨V, hV, hVfd, hratio⟩ :=
    exists_coefficient_ratio_le_of_basis b F E hE
  let _ : FiniteDimensional k V := hVfd
  let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let _ : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hEpos : (0 : ℚ) < sfinrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hVpos : (0 : ℚ) < sfinrank k V := by
    exact_mod_cast Module.finrank_pos (R := k) (M := V)
  have hsource :
      (sfinrank k (algebraModuleExpansion F E) : ℚ) / sfinrank k E ≤
        1 + ε :=
    (div_le_iff₀ hEpos).2 hEfolner
  exact ⟨V, hV, hVfd, (div_le_iff₀ hVpos).1 (hratio.trans hsource)⟩

end FreeModuleDescent

section ProjectiveModuleDescent

variable {A : Type*} {Q : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- Algebraic amenability descends from an amenable projective module to its
coefficient algebra. This is the projective-module Følner argument, separate
from the Takeuchi--Wigner projectivity input. -/
theorem algebraicallyAmenable_of_projective
    [Module.Projective A Q]
    (hQ : IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := Q)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A Q)
  have hsInjective : Function.Injective s := hs.injective
  let sk : Q →ₗ[k] Q →₀ A := s.restrictScalars k
  have hfree : IsAlgebraicallyAmenableModule
      (k := k) (A := A) (Q := Q →₀ A) := by
    intro F hF ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := hQ F hF ε hε
    let E' : Submodule k (Q →₀ A) := E.map sk
    have hE' : E' ≠ ⊥ := by
      intro hbot
      apply hE
      apply le_antisymm
      · intro x hx
        have hx' : sk x ∈ E' := Submodule.mem_map_of_mem hx
        rw [hbot, Submodule.mem_bot] at hx'
        exact hsInjective (by simpa [sk] using hx')
      · exact bot_le
    have hmap : (algebraModuleExpansion F E).map sk =
        algebraModuleExpansion F E' := by
      rw [algebraModuleExpansion, algebraModuleExpansion, Submodule.map_sup]
      congr 1
      apply le_antisymm
      · apply Submodule.map_le_iff_le_comap.mpr
        apply Submodule.map₂_le.2
        intro a ha e he
        change sk (a • e) ∈
          Submodule.map₂ (Algebra.lsmul k k (Q →₀ A)).toLinearMap F E'
        rw [show sk (a • e) = a • sk e by simp [sk]]
        exact Submodule.mem_map₂ _ _ _ ha (Submodule.mem_map_of_mem he)
      · apply Submodule.map₂_le.2
        intro a ha y hy
        rcases hy with ⟨e, he, rfl⟩
        refine ⟨a • e, Submodule.mem_map₂ _ _ _ ha he, ?_⟩
        simp [sk]
    let _ : FiniteDimensional k E' := by
      dsimp [E']
      infer_instance
    have hdimE : finrank k E' = finrank k E := by
      have h := (LinearEquiv.ofInjective (sk.domRestrict E)
        (fun x y hxy => Subtype.ext (hsInjective hxy))).finrank_eq.symm
      rw [LinearMap.range_domRestrict] at h
      exact h
    have hdimExpansion :
        finrank k ((algebraModuleExpansion F E).map sk) =
          finrank k (algebraModuleExpansion F E) := by
      have h := (LinearEquiv.ofInjective
        (sk.domRestrict (algebraModuleExpansion F E))
        (fun x y hxy => Subtype.ext (hsInjective hxy))).finrank_eq.symm
      rw [LinearMap.range_domRestrict] at h
      exact h
    refine ⟨E', hE', inferInstance, ?_⟩
    rw [← hmap, sfinrank, sfinrank, hdimE, hdimExpansion]
    exact hratio
  exact hfree.coefficient_of_basis (Finsupp.basisSingleOne (R := A))

end ProjectiveModuleDescent

section HopfSubalgebraDescent

universe x y

variable {H : Type x} {K : Type y}
variable [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]

/-- Algebraic amenability descends along a cocommutative Hopf-subalgebra
embedding. The only external input is projectivity; the Følner descent is
`algebraicallyAmenable_of_projective` above. -/
theorem algebraicAmenability_of_hopfSubalgebra
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hH : IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H)) :
    IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := K) := by
  let _ : Module K H := hopfSubalgebraRestrictionModule i
  let _ : IsScalarTower k K H :=
    IsScalarTower.of_algebraMap_smul fun r h => by
      change i.toAlgHom (algebraMap k K r) * h = r • h
      rw [i.toAlgHom.commutes, Algebra.smul_def]
  have hrestricted : IsAlgebraicallyAmenableModule
      (k := k) (A := K) (Q := H) := by
    intro F hF ε hε
    let F' : Submodule k H := F.map i.toAlgHom.toLinearMap
    let _ : FiniteDimensional k F' := by
      dsimp [F']
      infer_instance
    obtain ⟨E, hE, hEfd, hratio⟩ := hH F' inferInstance ε hε
    refine ⟨E, hE, hEfd, ?_⟩
    have hexpansion :
        algebraModuleExpansion (k := k) F E = actionExpansion F' E := by
      rw [algebraModuleExpansion, actionExpansion, actionSubspace_eq_map₂]
      congr 1
      apply le_antisymm
      · apply Submodule.map₂_le.2
        intro a ha e he
        exact Submodule.mem_map₂
          (Algebra.lsmul k k H).toLinearMap F' E
          (show i.toAlgHom a ∈ F' from ⟨a, ha, rfl⟩) he
      · apply Submodule.map₂_le.2
        intro a ha e he
        rcases ha with ⟨a, ha, rfl⟩
        exact Submodule.mem_map₂ _ _ _ ha he
    rwa [hexpansion]
  let _ : Module.Projective K H :=
    takeuchiWigner_projective_left (inferInstance : Coalgebra.IsCocomm k H) i
  have hK := algebraicallyAmenable_of_projective hrestricted
  intro F hF ε hε
  obtain ⟨E, hE, hEfd, hratio⟩ := hK F hF ε hε
  exact ⟨E, hE, hEfd, by
    simpa only [algebraModuleExpansion, actionExpansion,
      actionSubspace_eq_map₂] using hratio⟩

/-- **Theorem D.** Every Hopf subalgebra of an amenable cocommutative Hopf
algebra is amenable. -/
theorem isAmenableHopfAlgebra_of_hopfSubalgebra
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfAlgebra (k := k) (H := K) := by
  apply isAmenableHopfAlgebra_iff_algebraicallyAmenable.mpr
  exact algebraicAmenability_of_hopfSubalgebra i
    (isAmenableHopfAlgebra_iff_algebraicallyAmenable.mp hH)

end HopfSubalgebraDescent

section AssociativeLieInstance

attribute [local instance 100] LieRing.ofAssociativeRing

theorem algebraModuleExpansion_eq_actionExpansion
    (F E : Submodule k U) :
    algebraModuleExpansion F E = actionExpansion F E := by
  rw [algebraModuleExpansion, actionExpansion, actionSubspace_eq_map₂]

/-- The manuscript definition of Lie amenability is equivalent, by the
generator test, to Elek's associative-module condition on `U(L)`. -/
theorem isAmenableLieAlgebra_iff_algebraicallyAmenableModule :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAlgebraicallyAmenableModule (k := k) (A := U) (Q := U) := by
  constructor
  · intro h F hF ε hε
    have hregular := isAmenableLieAlgebra_iff_regularActionFolner.mp h
    obtain ⟨E, hE, hEfd, hratio⟩ := hregular F hF ε hε
    exact ⟨E, hE, hEfd, by
      rwa [algebraModuleExpansion_eq_actionExpansion]⟩
  · intro h
    apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
    intro F hF ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := h F hF ε hε
    exact ⟨E, hE, hEfd, by
      rwa [algebraModuleExpansion_eq_actionExpansion] at hratio⟩

/-- The algebra map on universal enveloping algebras induced by a Lie
homomorphism. -/
noncomputable def ueaMap {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) :
    UniversalEnvelopingAlgebra k L →ₐ[k]
      UniversalEnvelopingAlgebra k Q :=
  UniversalEnvelopingAlgebra.lift k
    ((UniversalEnvelopingAlgebra.ι k).comp f)

@[simp]
theorem ueaMap_iota {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (x : L) :
    ueaMap f (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.ι k (f x) := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply k _ x

theorem ueaMap_id :
    ueaMap (LieHom.id : L →ₗ⁅k⁆ L) = AlgHom.id k U := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply DFunLike.ext _ _
  intro x
  change ueaMap (LieHom.id : L →ₗ⁅k⁆ L)
      (UniversalEnvelopingAlgebra.ι k x) =
    (AlgHom.id k U) (UniversalEnvelopingAlgebra.ι k x)
  rw [ueaMap_iota]
  rfl

theorem ueaMap_comp {Q : Type w} {N : Type*}
    [LieRing Q] [LieAlgebra k Q] [LieRing N] [LieAlgebra k N]
    (g : Q →ₗ⁅k⁆ N) (f : L →ₗ⁅k⁆ Q) :
    ueaMap (g.comp f) = (ueaMap g).comp (ueaMap f) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply DFunLike.ext _ _
  intro x
  change ueaMap (g.comp f) (UniversalEnvelopingAlgebra.ι k x) =
    ueaMap g (ueaMap f (UniversalEnvelopingAlgebra.ι k x))
  rw [ueaMap_iota, ueaMap_iota, ueaMap_iota]
  rfl

/-- A surjective Lie homomorphism induces a surjective map of universal
enveloping algebras. -/
theorem ueaMap_surjective {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Surjective f) :
    Function.Surjective (ueaMap f) := by
  let A : Subalgebra k (UniversalEnvelopingAlgebra k Q) :=
    (ueaMap f).range
  have hi : Set.range (UniversalEnvelopingAlgebra.ι (L := Q) k) ⊆ A := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := hf q
    exact ⟨UniversalEnvelopingAlgebra.ι k x, ueaMap_iota f x⟩
  let iA : Q →ₗ⁅k⁆ A := {
    toLinearMap :=
      (UniversalEnvelopingAlgebra.ι (L := Q) k).toLinearMap.codRestrict
        A.toSubmodule
        (fun q => hi ⟨q, rfl⟩)
    map_lie' := fun {x y} => by
      apply Subtype.ext
      exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι k) x y }
  let liftA : UniversalEnvelopingAlgebra k Q →ₐ[k] A :=
    UniversalEnvelopingAlgebra.lift k iA
  have hval : A.val.comp liftA = AlgHom.id k _ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply DFunLike.ext _ _
    intro q
    change A.val (liftA (UniversalEnvelopingAlgebra.ι k q)) =
      UniversalEnvelopingAlgebra.ι k q
    rw [show liftA (UniversalEnvelopingAlgebra.ι k q) = iA q from
      UniversalEnvelopingAlgebra.lift_ι_apply k iA q]
    rfl
  intro q
  let aq : A := liftA q
  rcases aq.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  calc
    ueaMap f x = (aq : UniversalEnvelopingAlgebra k Q) := hx
    _ = q := DFunLike.congr_fun hval q

/-- The map induced on enveloping algebras is a counital coalgebra
morphism. -/
noncomputable def ueaMapCoalgHom {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q) :
    UniversalEnvelopingAlgebra k L →ₗc[k]
      UniversalEnvelopingAlgebra k Q where
  toLinearMap := (ueaMap f).toLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro a
    have heq : (Coalgebra.eps (L := Q)).comp (ueaMap f) =
        Coalgebra.eps (L := L) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext _ _
      intro x
      change Coalgebra.eps (ueaMap f (UniversalEnvelopingAlgebra.ι k x)) =
        Coalgebra.eps (UniversalEnvelopingAlgebra.ι k x)
      rw [ueaMap_iota, Coalgebra.eps_iota, Coalgebra.eps_iota]
    exact DFunLike.congr_fun heq a
  map_comp_comul := by
    apply LinearMap.ext
    intro a
    have heq :
        (Algebra.TensorProduct.map (ueaMap f) (ueaMap f)).comp
            (Coalgebra.delta (L := L)) =
          (Coalgebra.delta (L := Q)).comp (ueaMap f) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext _ _
      intro x
      change Algebra.TensorProduct.map (ueaMap f) (ueaMap f)
          (Coalgebra.delta (UniversalEnvelopingAlgebra.ι k x)) =
        Coalgebra.delta (ueaMap f (UniversalEnvelopingAlgebra.ι k x))
      rw [Coalgebra.delta_iota]
      simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
      rw [show ueaMap f (UniversalEnvelopingAlgebra.ι k x) =
        UniversalEnvelopingAlgebra.ι k (f x) from ueaMap_iota f x,
        Coalgebra.delta_iota]
    exact DFunLike.congr_fun heq a

@[simp]
theorem ueaMapCoalgHom_apply {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q)
    (a : UniversalEnvelopingAlgebra k L) :
    ueaMapCoalgHom f a = ueaMap f a :=
  rfl

/-- Restriction of the regular `U(Q)`-module along `U(f)`. -/
@[instance_reducible]
noncomputable def ueaRestrictionModule {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q) :
    Module (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) :=
  Module.compHom _ (ueaMap f).toRingHom

/-- The subalgebra argument of Theorem D, with the exact relative-freeness
conclusion of PBW made explicit. -/
theorem isAmenableLieAlgebra_of_map_basis
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) {ι : Type*}
    (b : UniversalEnvelopingAlgebra.RelativePBWBasis f ι)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₐ[k] UQ := ueaMap f
  let _ : Module UL UQ := ueaRestrictionModule f
  let _ : IsScalarTower k UL UQ :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change φ (algebraMap k UL r) * x = r • x
      rw [φ.commutes, Algebra.smul_def])
  change Basis ι UL UQ at b
  have hQalg : IsAlgebraicallyAmenableModule
      (k := k) (A := UQ) (Q := UQ) :=
    isAmenableLieAlgebra_iff_algebraicallyAmenableModule.mp hQ
  have hrestricted : IsAlgebraicallyAmenableModule
      (k := k) (A := UL) (Q := UQ) := by
    intro F hF ε hε
    let _ : FiniteDimensional k F := hF
    let F' : Submodule k UQ := F.map φ.toLinearMap
    let _ : FiniteDimensional k F' := by
      dsimp [F']
      infer_instance
    obtain ⟨E, hE, hEfd, hratio⟩ := hQalg F' inferInstance ε hε
    have hexpansion :
        algebraModuleExpansion (k := k) F E =
          algebraModuleExpansion (k := k) F' E := by
      rw [algebraModuleExpansion, algebraModuleExpansion]
      congr 1
      apply le_antisymm
      · apply Submodule.map₂_le.2
        intro a ha x hx
        exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap F' E
          ⟨a, ha, rfl⟩ hx
      · apply Submodule.map₂_le.2
        intro a ha x hx
        rcases ha with ⟨a, ha, rfl⟩
        exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap F E ha hx
    exact ⟨E, hE, hEfd, by rwa [hexpansion]⟩
  have hULalg :=
    IsAlgebraicallyAmenableModule.coefficient_of_basis b hrestricted
  exact isAmenableLieAlgebra_iff_algebraicallyAmenableModule.mpr hULalg

/-- Subalgebra descent for an injective Lie map, with relative PBW built
from injectivity of the canonical maps into the two enveloping algebras. -/
theorem isAmenableLieAlgebra_of_injective_of_iota_injective
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (_hιL : Function.Injective
      (UniversalEnvelopingAlgebra.ι (L := L) k))
    (_hιQ : Function.Injective
      (UniversalEnvelopingAlgebra.ι (L := Q) k))
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let ι := Module.Basis.ofVectorSpaceIndex k L
  let b : Basis ι k L := Module.Basis.ofVectorSpace k L
  let _ : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder
      (UniversalEnvelopingAlgebra.RelativeComplementIndex b f hf) :=
    UniversalEnvelopingAlgebra.relativeComplementLinearOrder b f hf
  exact isAmenableLieAlgebra_of_map_basis f
    (UniversalEnvelopingAlgebra.relativePBWBasis b f hf) hQ

/-- Subalgebra closure in Theorem D. -/
theorem isAmenableLieAlgebra_of_injective_pbw
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let ι := Module.Basis.ofVectorSpaceIndex k L
  let b : Basis ι k L := Module.Basis.ofVectorSpace k L
  let _ : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder
      (UniversalEnvelopingAlgebra.RelativeComplementIndex b f hf) :=
    UniversalEnvelopingAlgebra.relativeComplementLinearOrder b f hf
  exact isAmenableLieAlgebra_of_map_basis f
    (UniversalEnvelopingAlgebra.relativePBWBasis b f hf) hQ

/-- PBW makes the enveloping-algebra map induced by an injective Lie map
injective. -/
theorem ueaMap_injective
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f) :
    Function.Injective (ueaMap f) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let _ : Module UL UQ := ueaRestrictionModule f
  let ι := Module.Basis.ofVectorSpaceIndex k L
  let b : Basis ι k L := Module.Basis.ofVectorSpace k L
  let _ : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder
      (UniversalEnvelopingAlgebra.RelativeComplementIndex b f hf) :=
    UniversalEnvelopingAlgebra.relativeComplementLinearOrder b f hf
  let rb := UniversalEnvelopingAlgebra.relativePBWBasis b f hf
  let _ : Module.Free UL UQ := Module.Free.of_basis rb
  let _ : Nontrivial UQ := ⟨⟨0, 1, fun h => by
    have := congrArg (Coalgebra.counit (R := k)) h
    simp at this⟩⟩
  let _ : FaithfulSMul UL UQ :=
    Module.Free.instFaithfulSMulOfNontrivial UL UQ
  intro a c hac
  apply smul_left_injective' (M := UL) (α := UQ)
  funext x
  change ueaMap f a * x = ueaMap f c * x
  rw [hac]

/-- Amenability of a Lie algebra is equivalent to amenability of its
universal enveloping Hopf algebra. -/
theorem isAmenableLieAlgebra_iff_isAmenableHopfAlgebra :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableHopfAlgebra
        (k := k) (H := UniversalEnvelopingAlgebra k L) := by
  exact isAmenableLieAlgebra_iff_regularActionFolner.trans
    (isAmenableHopfAlgebra_iff_algebraicallyAmenable
      (k := k) (H := UniversalEnvelopingAlgebra k L)).symm

/-- Subalgebra closure in Theorem D, obtained from Hopf-subalgebra
permanence through the injective map of universal enveloping algebras. -/
theorem isAmenableLieAlgebra_of_injective
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let i : HopfSubalgebraEmbedding
      (k := k) (H := UniversalEnvelopingAlgebra k Q)
      (UniversalEnvelopingAlgebra k L) :=
    { toAlgHom := ueaMap f
      map_counit := (ueaMapCoalgHom f).counit_comp
      map_comul := (ueaMapCoalgHom f).map_comp_comul
      injective := ueaMap_injective f hf }
  apply isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mpr
  exact isAmenableHopfAlgebra_of_hopfSubalgebra i
    (isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hQ)

/-- Amenability transfers through an injective enveloping-algebra map for
coefficient spaces contained in its range.  This is the local step used for
directed unions. -/
theorem exists_folner_of_le_ueaMap_range
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L))
    (P : Submodule k (UniversalEnvelopingAlgebra k Q))
    (hP : P ≤ LinearMap.range (ueaMap f).toLinearMap)
    (hPfd : FiniteDimensional k P) (ε : ℚ) (hε : 0 < ε) :
    ∃ E : Submodule k (UniversalEnvelopingAlgebra k Q),
      E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k (actionExpansion P E) : ℚ) ≤
      (1 + ε) * sfinrank k E := by
  have hL := isAmenableLieAlgebra_iff_regularActionFolner.mp hL
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₗ[k] UQ := (ueaMap f).toLinearMap
  have hφ : Function.Injective φ := ueaMap_injective f hf
  let F : Submodule k UL := P.comap φ
  have hmap : F.map φ = P := by
    apply le_antisymm
    · exact Submodule.map_comap_le φ P
    · intro x hx
      obtain ⟨y, hy⟩ := hP hx
      refine ⟨y, ?_, hy⟩
      change φ y ∈ P
      rw [hy]
      exact hx
  let eFP : F ≃ₗ[k] P := LinearEquiv.ofBijective
    ((φ.domRestrict F).codRestrict P fun x => by
      rw [← hmap]
      exact Submodule.mem_map_of_mem x.2)
    ⟨fun x y hxy => Subtype.ext (hφ (congrArg Subtype.val hxy)), by
      intro x
      obtain ⟨y, hy, hxy⟩ := hmap.ge x.2
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩⟩
  let _ : FiniteDimensional k F :=
    FiniteDimensional.of_injective eFP.toLinearMap eFP.injective
  obtain ⟨E, hE, hEfd, hratio⟩ := hL F inferInstance ε hε
  let E' : Submodule k UQ := E.map φ
  have hE' : E' ≠ ⊥ := by
    intro hbot
    apply hE
    apply le_antisymm
    · intro x hx
      have : φ x ∈ E' := Submodule.mem_map_of_mem hx
      rw [hbot, Submodule.mem_bot] at this
      apply hφ
      simpa using this
    · exact bot_le
  let _ : FiniteDimensional k E' := by dsimp [E']; infer_instance
  have hexp : (actionExpansion F E).map φ = actionExpansion P E' := by
    rw [actionExpansion, actionExpansion, Submodule.map_sup]
    change E.map φ ⊔ (actionSubspace F E).map φ =
      E.map φ ⊔ actionSubspace P (E.map φ)
    congr 1
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    rw [← hmap]
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.map₂_le.2
      intro a ha x hx
      change φ (a * x) ∈ Submodule.map₂
        (Algebra.lsmul k k UQ).toLinearMap (F.map φ) (E.map φ)
      rw [show φ (a * x) = φ a * φ x from map_mul (ueaMap f) a x]
      exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap
        (F.map φ) (E.map φ) (Submodule.mem_map_of_mem ha)
        (Submodule.mem_map_of_mem hx)
    · apply Submodule.map₂_le.2
      intro a ha x hx
      rcases ha with ⟨a, ha, rfl⟩
      rcases hx with ⟨x, hx, rfl⟩
      exact ⟨a * x, Submodule.mem_map₂
        (Algebra.lsmul k k UL).toLinearMap F E ha hx, map_mul (ueaMap f) a x⟩
  refine ⟨E', hE', inferInstance, ?_⟩
  rw [← hexp]
  have hdimE := (LinearEquiv.ofInjective (φ.domRestrict E)
    (fun x y hxy => Subtype.ext (hφ hxy))).finrank_eq
  have hdimExp := (LinearEquiv.ofInjective
    (φ.domRestrict (actionExpansion F E))
    (fun x y hxy => Subtype.ext (hφ hxy))).finrank_eq
  rw [LinearMap.range_domRestrict] at hdimE hdimExp
  change (sfinrank k ((actionExpansion F E).map φ) : ℚ) ≤
    (1 + ε) * sfinrank k (E.map φ)
  simp only [sfinrank]
  rw [show Module.finrank k ((actionExpansion F E).map φ) =
      Module.finrank k (actionExpansion F E) by
        exact hdimExp.symm]
  rw [show Module.finrank k (E.map φ) = Module.finrank k E by
        exact hdimE.symm]
  exact hratio

/-- Directed-union closure in Theorem D. -/
theorem isAmenableLieAlgebra_directedUnion
 {ι : Type w} [Nonempty ι]
    (S : ι → LieSubalgebra k L) (hdir : Directed (· ≤ ·) S)
    (hsup : iSup S = ⊤)
    (hS : ∀ i, IsAmenableLieAlgebra (k := k) (L := S i)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hPfd ε hε
  let β := Module.Basis.ofVectorSpaceIndex k L
  let b : Basis β k L := Module.Basis.ofVectorSpace k L
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  let B := UniversalEnvelopingAlgebra.orderedMonomialBasis b
  let _ : FiniteDimensional k P := hPfd
  obtain ⟨t, ht⟩ := Basis.exists_finset_support (k := k) B P
  let letters : Finset β := t.biUnion fun word => word.1.toFinset
  have hletter (j : β) (hj : j ∈ letters) : ∃ i, b j ∈ S i := by
    apply (LieSubalgebra.mem_iSup_of_directed (k := k) S hdir).mp
    rw [hsup]
    trivial
  obtain ⟨i, hi⟩ := exists_directed_member_containing_finset
    (k := k) (L := L) S hdir (letters.image b) (by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      exact hletter j hj)
  let f : S i →ₗ⁅k⁆ L := LieSubalgebra.incl (S i)
  have hf : Function.Injective f := fun x y hxy => Subtype.ext hxy
  let φ := (ueaMap f).toLinearMap
  have hword (word : UniversalEnvelopingAlgebra.PBWWord β)
      (hw : word ∈ t) : B word ∈ LinearMap.range φ := by
    have hall : ∀ j ∈ word.1, b j ∈ S i := by
      intro j hj
      apply hi (b j)
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨word, hw, List.mem_toFinset.mpr hj⟩
    have hlist : ∀ (l : List β), (∀ j ∈ l, b j ∈ S i) →
        UniversalEnvelopingAlgebra.pbwMonomial b l ∈
          LinearMap.range φ := by
      intro l hl
      induction l with
      | nil =>
          exact ⟨1, by
            change ueaMap f 1 = 1
            exact map_one (ueaMap f)⟩
      | cons j js ih =>
          have hj : b j ∈ S i := hl j List.mem_cons_self
          have hjs : ∀ l ∈ js, b l ∈ S i := fun l hmem =>
            hl l (List.mem_cons_of_mem j hmem)
          obtain ⟨a, ha⟩ := ih hjs
          refine ⟨UniversalEnvelopingAlgebra.ι k ⟨b j, hj⟩ * a, ?_⟩
          change ueaMap f
              (UniversalEnvelopingAlgebra.ι k ⟨b j, hj⟩ * a) = _
          change ueaMap f a = _ at ha
          rw [map_mul, ueaMap_iota, ha]
          rfl
    rw [show B word = UniversalEnvelopingAlgebra.orderedMonomial b word from
      UniversalEnvelopingAlgebra.orderedMonomialBasis_apply b word]
    exact hlist word.1 hall
  have hPrange : P ≤ LinearMap.range φ := by
    intro x hx
    have hsum := B.linearCombination_repr x
    rw [Finsupp.linearCombination_apply] at hsum
    rw [← hsum]
    change ∑ word ∈ (B.repr x).support,
      (B.repr x word) • B word ∈ LinearMap.range φ
    apply Submodule.sum_mem
    intro word hwordSupport
    exact Submodule.smul_mem _ _
      (hword word (ht x hx hwordSupport))
  exact exists_folner_of_le_ueaMap_range f hf (hS i) P hPrange hPfd ε hε

/-- Restricting scalars along `U(f)` makes `U(Q)` a module coalgebra over
`U(L)`. -/
theorem ueaRestrictionIsHopfModuleCoalgebra {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q) : by
    letI : Module (UniversalEnvelopingAlgebra k L)
        (UniversalEnvelopingAlgebra k Q) := ueaRestrictionModule f
    letI : IsScalarTower k (UniversalEnvelopingAlgebra k L)
        (UniversalEnvelopingAlgebra k Q) :=
      IsScalarTower.of_algebraMap_smul (fun r q => by
        change ueaMap f (algebraMap k (UniversalEnvelopingAlgebra k L) r) * q =
          r • q
        rw [(ueaMap f).commutes, Algebra.smul_def])
    exact IsHopfModuleCoalgebra k (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) := by
  let : Module (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) := ueaRestrictionModule f
  let : IsScalarTower k (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) :=
    IsScalarTower.of_algebraMap_smul (fun r q => by
      change ueaMap f (algebraMap k (UniversalEnvelopingAlgebra k L) r) * q =
        r • q
      rw [(ueaMap f).commutes, Algebra.smul_def])
  let act :
      ((UniversalEnvelopingAlgebra k L) ⊗[k]
          (UniversalEnvelopingAlgebra k Q)) →ₗc[k]
        (UniversalEnvelopingAlgebra k Q) :=
    (Bialgebra.mulCoalgHom k (UniversalEnvelopingAlgebra k Q)).comp
      (CoalgHom.tensorMapStruct (ueaMapCoalgHom f) (CoalgHom.id k _))
  have hact : hopfModuleAction (k := k)
      (H := UniversalEnvelopingAlgebra k L)
      (M := UniversalEnvelopingAlgebra k Q) = act.toLinearMap := by
    ext a q
    change ueaMap f a * q = act (a ⊗ₜ[k] q)
    simp [act]
  refine {
    counit_action := ?_
    comul_action := ?_ }
  · rw [hact]
    exact act.counit_comp
  · rw [hact]
    exact act.map_comp_comul.symm

/-- Quotient closure in Theorem D. -/
theorem IsAmenableLieAlgebra.of_surjective
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Surjective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := Q) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₐ[k] UQ := ueaMap f
  let q : UL →ₗc[k] UQ := ueaMapCoalgHom f
  let : Module UL UQ := ueaRestrictionModule f
  let : IsScalarTower k UL UQ :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change φ (algebraMap k UL r) * x = r • x
      rw [φ.commutes, Algebra.smul_def])
  let : IsHopfModuleCoalgebra k UL UQ :=
    ueaRestrictionIsHopfModuleCoalgebra f
  have hq : IsHopfModuleMap (H := UL) q.toLinearMap := by
    intro a b
    change φ (a * b) = φ a * φ b
    exact map_mul φ a b
  have hULcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UL) (M := UL) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
      (isAmenableLieAlgebra_iff_regularActionFolner.mp hL)
  have hUQcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UL) (M := UQ) :=
    IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom q hq
      (by
        intro y
        obtain ⟨x, hx⟩ := ueaMap_surjective f hf y
        exact ⟨x, hx⟩) hULcoal
  have hrestricted : HasActionFolnerSubspaces
      (k := k) (H := UL) (M := UQ) :=
    hUQcoal.hasActionFolnerSubspaces
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let : FiniteDimensional k P := hP
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    φ.toLinearMap (LinearMap.range_eq_top.2 (ueaMap_surjective f hf))
  let F : Submodule k UL := P.map s
  let : FiniteDimensional k F := by
    dsimp [F]
    infer_instance
  obtain ⟨E, hE, hEfd, hEfolner⟩ :=
    hrestricted F inferInstance ε hε
  have hs_apply (p : UQ) : φ (s p) = p := by
    have h := LinearMap.congr_fun hs p
    exact h
  have haction : actionSubspace F E = actionSubspace P E := by
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    apply le_antisymm
    · apply Submodule.map₂_le.2
      rintro _ ⟨p, hp, rfl⟩ e he
      change φ (s p) * e ∈ _
      rw [hs_apply]
      exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap P E hp he
    · apply Submodule.map₂_le.2
      intro p hp e he
      have hsp : s p ∈ F := ⟨p, hp, rfl⟩
      have hmem := Submodule.mem_map₂
        (Algebra.lsmul k k UQ).toLinearMap F E hsp he
      change φ (s p) * e ∈ _ at hmem
      rwa [hs_apply] at hmem
  refine ⟨E, hE, hEfd, ?_⟩
  change (sfinrank k (E ⊔ actionSubspace P E) : ℚ) ≤
    (1 + ε) * sfinrank k E
  change (sfinrank k (E ⊔ actionSubspace F E) : ℚ) ≤
    (1 + ε) * sfinrank k E at hEfolner
  rw [haction] at hEfolner
  exact hEfolner

/-- The quotient-algebra clause of Theorem D. -/
theorem isAmenableLieAlgebra_quotient
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Surjective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := Q) :=
  hL.of_surjective f hf

/-- The easy implication in the extension clause: amenability passes from
the middle algebra to its ideal and quotient. -/
theorem IsAmenableLieAlgebra.extension_components
 (I : LieIdeal k L)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := I) ∧
      IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact isAmenableLieAlgebra_of_injective
      (LieSubalgebra.incl (I : LieSubalgebra k L))
      (fun x y hxy => Subtype.ext hxy) hL
  · exact hL.of_surjective (LieIdeal.quotientMkLieHom I)
      (LieIdeal.quotientMkLieHom_surjective I)

/-- Extension closure in Theorem D. -/
theorem isAmenableLieAlgebra_extension_direct
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  have hI := isAmenableLieAlgebra_iff_regularActionFolner.mp hI
  have hQ := isAmenableLieAlgebra_iff_regularActionFolner.mp hQ
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro F hF ε hε
  let δ : ℚ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδeps : 3 * δ ≤ ε := by
    have := min_le_left (ε / 3) (1 : ℚ)
    dsimp [δ]
    linarith
  have hsq : (1 + δ) ^ 2 ≤ 1 + ε := by
    nlinarith [sq_nonneg δ]
  let _ : FiniteDimensional k F := hF
  let F1 : Submodule k (UniversalEnvelopingAlgebra k L) :=
    F ⊔ Submodule.span k {1}
  let _ : FiniteDimensional k F1 := by dsimp [F1]; infer_instance
  obtain ⟨A, hF1A⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule F1
  have hFA : F ≤ A.carrier := le_sup_left.trans hF1A
  have h1A : (1 : UniversalEnvelopingAlgebra k L) ∈ A.carrier := by
    apply hF1A
    exact (le_sup_right : Submodule.span k {1} ≤ F1)
      (Submodule.subset_span (Set.mem_singleton 1))
  let π := UniversalEnvelopingAlgebra.pbwMap
    (LieIdeal.quotientMkLieHom I)
  let G : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    A.carrier.map π.toLinearMap
  let _ : FiniteDimensional k G := by dsimp [G]; infer_instance
  have h1G : (1 : UniversalEnvelopingAlgebra k (L ⧸ I)) ∈ G := by
    exact ⟨1, h1A, map_one π⟩
  have hQcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UniversalEnvelopingAlgebra k (L ⧸ I))
      (M := UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra hQ
  obtain ⟨C, hC, hCratio0⟩ := hQcoal G inferInstance δ hδ
  have hCratio :
      (sfinrank k (actionSubspace G C.carrier) : ℚ) ≤
        (1 + δ) * sfinrank k C.carrier := by
    rw [actionExpansion_eq_actionSubspace_of_one_mem h1G] at hCratio0
    exact hCratio0
  let α := Module.Basis.ofVectorSpaceIndex k I
  let β := Module.Basis.ofVectorSpaceIndex k (L ⧸ I)
  let bI : Basis α k I := Module.Basis.ofVectorSpace k I
  let bQ : Basis β k (L ⧸ I) := Module.Basis.ofVectorSpace k (L ⧸ I)
  let _ : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨D, hDfd, hdefect⟩ :=
    LieIdeal.exists_finite_extension_defect I bQ bI A C
  let _ : FiniteDimensional k D := hDfd
  obtain ⟨K, hK, hKfd, hKratio⟩ := hI D inferInstance δ hδ
  let _ : FiniteDimensional k K := hKfd
  let CP : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    actionSubspace G C.carrier
  let KP : Submodule k (UniversalEnvelopingAlgebra k I) :=
    actionExpansion D K
  let _ : FiniteDimensional k CP := by
    dsimp [CP]
    exact finiteDimensional_actionSubspace _ _
  let _ : FiniteDimensional k KP := by
    dsimp [KP]
    exact finiteDimensional_actionExpansion _ _
  let E0 := tensorProductSubspace C.carrier K
  let θ := (LieIdeal.extensionPBWCoalgEquiv I bQ bI).toLinearEquiv
  let E : Submodule k (UniversalEnvelopingAlgebra k L) := E0.map θ.toLinearMap
  let Target0 := tensorProductSubspace CP KP
  let Target : Submodule k (UniversalEnvelopingAlgebra k L) :=
    Target0.map θ.toLinearMap
  let _ : FiniteDimensional k E0 := by
    dsimp [E0]
    exact finiteDimensional_tensorProductSubspace C.carrier K
  let _ : FiniteDimensional k E := by dsimp [E]; infer_instance
  let _ : FiniteDimensional k Target0 := by
    dsimp [Target0]
    exact finiteDimensional_tensorProductSubspace CP KP
  let _ : FiniteDimensional k Target := by
    dsimp [Target]
    infer_instance
  have hC_CP : C.carrier ≤ CP := by
    intro c hc
    change c ∈ actionSubspace G C.carrier
    rw [actionSubspace_eq_map₂]
    simpa using Submodule.mem_map₂
      (Algebra.lsmul k k (UniversalEnvelopingAlgebra k (L ⧸ I))).toLinearMap
      G C.carrier h1G hc
  have hK_KP : K ≤ KP := by
    exact le_sup_left
  have hETarget : E ≤ Target := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    apply (show E0 ≤ Target0 by
      exact tensorProductSubspace_mono hC_CP hK_KP)
    exact hz
  have haction : actionSubspace F E ≤ Target := by
    rw [actionSubspace_eq_map₂]
    apply Submodule.map₂_le.2
    intro f hf x hx
    rcases hx with ⟨z, hz, rfl⟩
    change z ∈ tensorProductSubspace C.carrier K at hz
    rw [tensorProductSubspace_eq_range_mapIncl] at hz
    obtain ⟨zCK, rfl⟩ := hz
    induction zCK using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simp only [map_add]
        exact Target.add_mem hz hz'
    | tmul c e =>
        have hprod : f * LieIdeal.ueaLinearSection I bQ bI c ∈
            actionSubspace A.carrier
              (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI)) := by
          rw [actionSubspace_eq_map₂]
          exact Submodule.mem_map₂
            (Algebra.lsmul k k (UniversalEnvelopingAlgebra k L)).toLinearMap
            A.carrier
            (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI))
            (hFA hf) ⟨c, c.2, rfl⟩
        have hzD := hdefect
          (Submodule.mem_map_of_mem hprod)
        have hmul := LieIdeal.extensionPBWEquiv_symm_mul_ideal_mem
          I bQ bI CP D K
          ((LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            (f * LieIdeal.ueaLinearSection I bQ bI c)) hzD e e.2
        have hmul0 : (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            ((f * LieIdeal.ueaLinearSection I bQ bI c) *
              UniversalEnvelopingAlgebra.pbwMap
                (LieIdeal.inclusionLieHom I) e) ∈
            tensorProductSubspace CP (actionSubspace D K) := by
          simpa using hmul
        have hmul' : (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            (f * LieIdeal.extensionPBWCoalgEquiv I bQ bI
              (c ⊗ₜ[k] e)) ∈ Target0 := by
          change (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
              (f * LieIdeal.extensionPBWMap I bQ bI (c ⊗ₜ[k] e)) ∈ Target0
          rw [LieIdeal.extensionPBWMap_tmul]
          rw [← mul_assoc]
          change (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
              ((f * LieIdeal.ueaLinearSection I bQ bI c) *
                UniversalEnvelopingAlgebra.pbwMap
                  (LieIdeal.inclusionLieHom I) e) ∈
            tensorProductSubspace CP KP
          exact tensorProductSubspace_mono le_rfl
            (le_sup_right : actionSubspace D K ≤ KP) hmul0
        exact ⟨_, hmul', (LieIdeal.extensionPBWCoalgEquiv I bQ bI).apply_symm_apply _⟩
  have hexpansion : actionExpansion F E ≤ Target := by
    exact sup_le hETarget haction
  have hdimE : sfinrank k E = sfinrank k C.carrier * sfinrank k K := by
    rw [show sfinrank k E = sfinrank k E0 by
      exact θ.finrank_map_eq E0]
    exact sfinrank_tensorProductSubspace C.carrier K
  have hdimTarget : sfinrank k Target = sfinrank k CP * sfinrank k KP := by
    rw [show sfinrank k Target = sfinrank k Target0 by
      exact θ.finrank_map_eq Target0]
    exact sfinrank_tensorProductSubspace CP KP
  have hdimExpansion : sfinrank k (actionExpansion F E) ≤
      sfinrank k Target := Submodule.finrank_mono hexpansion
  have hnonzero : E ≠ ⊥ := by
    intro hbot
    have hzero : sfinrank k E = 0 := by simp [hbot, sfinrank]
    rw [hdimE] at hzero
    have hCpos : 0 < sfinrank k C.carrier := by
      let _ : Nontrivial C.carrier := Submodule.nontrivial_iff_ne_bot.mpr hC
      exact Module.finrank_pos
    have hKpos : 0 < sfinrank k K := by
      let _ : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
      exact Module.finrank_pos
    have hprod : sfinrank k C.carrier * sfinrank k K ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hCpos) (Nat.ne_of_gt hKpos)
    exact hprod (hdimE ▸ hzero)
  refine ⟨E, hnonzero, inferInstance, ?_⟩
  calc
    (sfinrank k (actionExpansion F E) : ℚ) ≤ sfinrank k Target := by
      exact_mod_cast hdimExpansion
    _ = (sfinrank k CP : ℚ) * sfinrank k KP := by rw [hdimTarget]; norm_num
    _ ≤ ((1 + δ) * sfinrank k C.carrier) *
        ((1 + δ) * sfinrank k K) := by
      apply mul_le_mul hCratio hKratio
      · positivity
      · positivity
    _ = (1 + δ) ^ 2 *
        ((sfinrank k C.carrier : ℚ) * sfinrank k K) := by ring
    _ ≤ (1 + ε) *
        ((sfinrank k C.carrier : ℚ) * sfinrank k K) := by
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (1 + ε) * sfinrank k E := by rw [hdimE]; norm_num

/-- The extension clause of Theorem D in iff form. -/
theorem isAmenableLieAlgebra_extension_direct_iff
    (I : LieIdeal k L) :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableLieAlgebra (k := k) (L := I) ∧
        IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact IsAmenableLieAlgebra.extension_components I
  · rintro ⟨hI, hQ⟩
    exact isAmenableLieAlgebra_extension_direct I hI hQ

end AssociativeLieInstance

/-- The ball generated by a finite-dimensional subspace of an associative
algebra.  The zeroth ball consists of the scalars and each successor is
obtained by one further multiplication by the generating subspace. -/
noncomputable def algebraBall (P : Submodule k U) : ℕ → Submodule k U
  | 0 => k ∙ (1 : U)
  | n + 1 => actionExpansion P (algebraBall P n)

theorem algebraBall_zero (P : Submodule k U) :
    algebraBall P 0 = k ∙ (1 : U) :=
  rfl

theorem algebraBall_succ (P : Submodule k U) (n : ℕ) :
    algebraBall P (n + 1) = actionExpansion P (algebraBall P n) :=
  rfl

theorem finiteDimensional_algebraBall
    (P : Submodule k U) [FiniteDimensional k P] (n : ℕ) :
    FiniteDimensional k (algebraBall P n) := by
  induction n with
  | zero =>
      rw [algebraBall_zero]
      infer_instance
  | succ n ih =>
      rw [algebraBall_succ]
      exact finiteDimensional_actionExpansion P (algebraBall P n)

theorem algebraBall_ne_bot (P : Submodule k U) (n : ℕ) :
    algebraBall P n ≠ ⊥ := by
  have hmono : algebraBall P 0 ≤ algebraBall P n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        exact ih.trans (le_sup_left : algebraBall P n ≤
          actionExpansion P (algebraBall P n))
  intro hbot
  have hOne : (1 : U) ∈ (⊥ : Submodule k U) := by
    rw [← hbot]
    apply hmono
    rw [algebraBall_zero]
    exact Submodule.mem_span_singleton_self 1
  have hone : (1 : U) ≠ 0 := by
    intro h
    have := congrArg (Coalgebra.eps (L := L)) h
    simp at this
  simp only [Submodule.mem_bot] at hOne
  exact hone hOne

set_option linter.unusedVariables false in
/-- The legacy unit-coefficient bound on UEA balls.  This auxiliary
condition is retained only for the ratio lemma below; it is deliberately not
called subexponential growth. -/
def HasUnitCoefficientUEAGrowth : Prop :=
  ∀ (P : Submodule k U), FiniteDimensional k P →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : ℚ, ∀ n : ℕ,
        (sfinrank k (algebraBall P n) : ℚ) ≤ (1 + ε) ^ n

/-- The elementary ratio test used to pass from a subexponential bound to
a Følner radius. -/
theorem exists_succ_le_mul_of_exponential_bound
    (a : ℕ → ℚ) (ha0 : 0 < a 0) (ε : ℚ) (hε : 0 < ε)
    (C : ℚ)
    (hbound : ∀ n : ℕ, a n ≤ C * (1 + ε / 2) ^ n) :
    ∃ n : ℕ, a (n + 1) ≤ (1 + ε) * a n := by
  by_contra h
  push Not at h
  have hr : 0 < 1 + ε := by linarith
  have hs : 0 < 1 + ε / 2 := by linarith
  have hrs : 1 < (1 + ε) / (1 + ε / 2) := by
    rw [one_lt_div hs]
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / a 0) hrs
  have hgrowth : ∀ m : ℕ, (1 + ε) ^ m * a 0 ≤ a m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        have hstep : (1 + ε) ^ m * (1 + ε) * a 0 < a (m + 1) := by
          calc
          (1 + ε) ^ m * (1 + ε) * a 0 =
              (1 + ε) * ((1 + ε) ^ m * a 0) := by ring
            _ ≤ (1 + ε) * a m := mul_le_mul_of_nonneg_left ih hr.le
            _ < a (m + 1) := h m
        exact hstep.le
  have hpow : C * (1 + ε / 2) ^ n < (1 + ε) ^ n * a 0 := by
    rw [div_pow] at hn
    exact (div_lt_div_iff₀ ha0 (pow_pos hs n)).mp hn
  have han : a n < (1 + ε) ^ n * a 0 :=
    lt_of_le_of_lt (hbound n) hpow
  exact (not_lt_of_ge (hgrowth n)) han

/-- The locally-subexponential-growth clause of Theorem D. -/
theorem HasUnitCoefficientUEAGrowth.isAmenableLieAlgebra
    (hL : HasUnitCoefficientUEAGrowth (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let : FiniteDimensional k P := hP
  obtain ⟨_, hbound⟩ := hL P inferInstance (ε / 2) (by linarith)
  obtain ⟨n, hn⟩ := exists_succ_le_mul_of_exponential_bound
    (fun m => (sfinrank k (algebraBall P m) : ℚ))
    (by
      rw [algebraBall_zero]
      have hone : (1 : U) ≠ 0 := by
        intro h
        have := congrArg (Coalgebra.eps (L := L)) h
        simp at this
      rw [sfinrank, finrank_span_singleton hone]
      norm_num) ε hε 1 (by
        intro m
        simpa [div_div] using hbound m)
  let E : Submodule k U := algebraBall P n
  let : FiniteDimensional k E := finiteDimensional_algebraBall P n
  have hE : E ≠ ⊥ := algebraBall_ne_bot P n
  refine ⟨E, hE, inferInstance, ?_⟩
  change (sfinrank k (algebraBall P (n + 1)) : ℚ) ≤
    (1 + ε) * sfinrank k (algebraBall P n)
  exact hn

/-- Public statement of the locally-subexponential-growth clause of
Theorem D. -/
theorem isAmenableLieAlgebra_of_unitCoefficientUEAGrowth
    (hL : HasUnitCoefficientUEAGrowth (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  hL.isAmenableLieAlgebra

end

end HopfAmenability
