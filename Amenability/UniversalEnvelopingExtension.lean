/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.LieGeneratorTest
import Amenability.CoalgebraInjective
import Amenability.UniversalEnvelopingPBW
import Amenability.ElementaryLieAlgebra
import Amenability.HopfExactSequence
import Amenability.CleftNormalBasis
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Basis.Prod

/-! # PBW structure of universal-enveloping extensions -/

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


attribute [local instance 100] LieRing.ofAssociativeRing

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


/-- The universal-enveloping sequence of a Lie ideal, packaged as the
intrinsic cleft exact sequence required by Theorem E. -/
noncomputable def LieIdeal.ueaCleftExactSequence
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I) :
    CleftExactSequence (k := k)
      (UniversalEnvelopingAlgebra k I)
      (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k (L ⧸ I)) where
  inclusion :=
    { toAlgHom := ueaMap (LieIdeal.inclusionLieHom I)
      map_counit := (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)).counit_comp
      map_comul := (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)).map_comp_comul }
  projection :=
    { toAlgHom := ueaMap (LieIdeal.quotientMkLieHom I)
      map_counit := (ueaMapCoalgHom (LieIdeal.quotientMkLieHom I)).counit_comp
      map_comul := (ueaMapCoalgHom (LieIdeal.quotientMkLieHom I)).map_comp_comul }
  inclusion_injective := ueaMap_injective (LieIdeal.inclusionLieHom I)
    (fun x y h => Subtype.ext h)
  projection_surjective := ueaMap_surjective (LieIdeal.quotientMkLieHom I)
    (LieIdeal.quotientMkLieHom_surjective I)
  projection_inclusion := fun a => DFunLike.congr_fun
    (LieIdeal.pbwMap_quotient_comp_ideal I) a
  coalgebraSection := LieIdeal.ueaLinearSectionCoalgHom I bQ bI
  projection_section := LieIdeal.pbwMap_comp_ueaLinearSection I bQ bI
  section_one := by
    let word : UniversalEnvelopingAlgebra.PBWWord β := ⟨[], by simp⟩
    change LieIdeal.ueaLinearSection I bQ bI
      (UniversalEnvelopingAlgebra.orderedMonomial bQ word) = 1
    rw [LieIdeal.ueaLinearSection_orderedMonomial]
    simp [LieIdeal.liftedQuotientMonomial, word]
  coinvariants := by
    let inc := ueaMap (LieIdeal.inclusionLieHom I)
    let proj := ueaMap (LieIdeal.quotientMkLieHom I)
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      change (((TensorProduct.map LinearMap.id proj.toLinearMap).comp
          (Coalgebra.comul (R := k)
            (A := UniversalEnvelopingAlgebra k L))) -
        (TensorProduct.mk k (UniversalEnvelopingAlgebra k L)
          (UniversalEnvelopingAlgebra k (L ⧸ I))).flip 1) (inc a) = 0
      rw [LinearMap.sub_apply, sub_eq_zero]
      rw [LinearMap.comp_apply]
      rw [show Coalgebra.comul (R := k) (inc a) =
          TensorProduct.map inc.toLinearMap inc.toLinearMap
            (Coalgebra.comul (R := k) a) from
        (CoalgHomClass.map_comp_comul_apply
          (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)) a).symm]
      have hcounit (y : UniversalEnvelopingAlgebra k I) :
          proj (inc y) = algebraMap k _ (Coalgebra.counit (R := k) y) :=
        DFunLike.congr_fun (LieIdeal.pbwMap_quotient_comp_ideal I) y
      have hmap (z : UniversalEnvelopingAlgebra k I ⊗[k]
          UniversalEnvelopingAlgebra k I) :
          TensorProduct.map LinearMap.id proj.toLinearMap
              (TensorProduct.map inc.toLinearMap inc.toLinearMap z) =
            TensorProduct.map inc.toLinearMap
              (Algebra.linearMap k
                (UniversalEnvelopingAlgebra k (L ⧸ I)))
                (Coalgebra.counit (R := k).lTensor _ z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            simpa only [map_add] using congrArg₂ (fun p q => p + q) hx hy
        | tmul x y =>
            simp only [TensorProduct.map_tmul, LinearMap.id_apply,
              LinearMap.lTensor_tmul]
            rw [show proj.toLinearMap (inc.toLinearMap y) =
                algebraMap k (UniversalEnvelopingAlgebra k (L ⧸ I))
                  (Coalgebra.counit (R := k) y) from
              hcounit y]
            simp
      rw [hmap]
      rw [Coalgebra.lTensor_counit_comul]
      simp
    · intro b hb
      let p : HopfAlgebraHom (k := k)
          (H := UniversalEnvelopingAlgebra k L)
          (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
        { toAlgHom := proj
          map_counit := (ueaMapCoalgHom
            (LieIdeal.quotientMkLieHom I)).counit_comp
          map_comul := (ueaMapCoalgHom
            (LieIdeal.quotientMkLieHom I)).map_comp_comul }
      change b ∈ rightCoinvariants p at hb
      have hleft := leftCoaction_eq_of_mem_rightCoinvariants p b hb
      let θ := LieIdeal.extensionPBWCoalgEquiv I bQ bI
      let θinv := θ.symm.toLinearMap
      let a : UniversalEnvelopingAlgebra k I :=
        (TensorProduct.lid k (UniversalEnvelopingAlgebra k I))
          (Coalgebra.counit (R := k).rTensor _ (θinv b))
      have htransport :
          TensorProduct.map proj.toLinearMap θinv
              (Coalgebra.comul (R := k) b) =
            TensorProduct.map LinearMap.id θinv
              (TensorProduct.map proj.toLinearMap LinearMap.id
                (Coalgebra.comul (R := k) b)) := by
        have hmaps := LinearMap.congr_fun
          (TensorProduct.map_comp LinearMap.id θinv
            proj.toLinearMap LinearMap.id)
          (Coalgebra.comul (R := k) b)
        simpa only [LinearMap.id_comp, LinearMap.comp_id,
          LinearMap.comp_apply] using hmaps
      have hR := LinearMap.congr_fun
        (LieIdeal.extensionCoactionRetraction_eq_symm I bQ bI) b
      change LieIdeal.middleCounitContraction I
          (TensorProduct.map proj.toLinearMap θinv
            (Coalgebra.comul (R := k) b)) = θinv b at hR
      rw [htransport, hleft] at hR
      have hmiddle : LieIdeal.middleCounitContraction I
          (1 ⊗ₜ[k] θinv b) = 1 ⊗ₜ[k] a := by
        change LinearMap.lTensor _
            ((TensorProduct.lid k _).toLinearMap.comp
              (Coalgebra.counit (R := k).rTensor _))
              (1 ⊗ₜ[k] θinv b) = _
        rw [LinearMap.lTensor_tmul, LinearMap.comp_apply]
        rfl
      have hz : θinv b = 1 ⊗ₜ[k] a := by
        rw [TensorProduct.map_tmul, LinearMap.id_apply] at hR
        exact hR.symm.trans hmiddle
      refine ⟨a, ?_⟩
      change inc a = b
      have hinc : inc =
          UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.inclusionLieHom I) := by
        apply UniversalEnvelopingAlgebra.hom_ext
        apply DFunLike.ext _ _
        intro x
        change ueaMap (LieIdeal.inclusionLieHom I)
            (UniversalEnvelopingAlgebra.ι k x) =
          UniversalEnvelopingAlgebra.pbwMap (LieIdeal.inclusionLieHom I)
            (UniversalEnvelopingAlgebra.ι k x)
        rw [ueaMap_iota, UniversalEnvelopingAlgebra.pbwMap_iota]
      calc
        inc a = θ (1 ⊗ₜ[k] a) := by
          rw [hinc]
          rw [LieIdeal.extensionPBWCoalgEquiv_apply,
            LieIdeal.extensionPBWMap_tmul]
          have hsone : LieIdeal.ueaLinearSection I bQ bI 1 = 1 := by
            let word : UniversalEnvelopingAlgebra.PBWWord β := ⟨[], by simp⟩
            change LieIdeal.ueaLinearSection I bQ bI
              (UniversalEnvelopingAlgebra.orderedMonomial bQ word) = 1
            rw [LieIdeal.ueaLinearSection_orderedMonomial]
            simp [LieIdeal.liftedQuotientMonomial, word]
          rw [hsone, one_mul]
        _ = θ (θinv b) := by rw [hz]
        _ = b := θ.apply_symm_apply b



end
end HopfAmenability


