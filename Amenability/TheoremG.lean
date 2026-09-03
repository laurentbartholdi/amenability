/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremD
import Amenability.TheoremE
import Amenability.LieAmenabilityPermanence

/-! # Theorem G: permanence properties for amenable Lie algebras -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

/-- The backward extension implication for Lie algebras, factored through
the cleft Hopf-extension theorem. -/
theorem isAmenableLieAlgebra_extension_of_components
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  let α := Module.Basis.ofVectorSpaceIndex k I
  let β := Module.Basis.ofVectorSpaceIndex k (L ⧸ I)
  let bI : Basis α k I := Module.Basis.ofVectorSpace k I
  let bQ : Basis β k (L ⧸ I) := Module.Basis.ofVectorSpace k (L ⧸ I)
  let _ : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  let e := LieIdeal.ueaCleftExactSequence I bQ bI
  rw [isAmenableLieAlgebra_iff_isAmenableHopfAlgebra]
  apply isAmenableHopfAlgebra_cleftExtension_of_components e
  · exact isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hI
  · exact isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hQ

/-- Public backward extension clause of Theorem G. -/
theorem isAmenableLieAlgebra_extension
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  isAmenableLieAlgebra_extension_of_components I hI hQ

/-- The Lie-extension clause of Theorem G in iff form, obtained from the
Hopf cleft-extension equivalence. -/
theorem isAmenableLieAlgebra_extension_iff (I : LieIdeal k L) :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableLieAlgebra (k := k) (L := I) ∧
        IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact IsAmenableLieAlgebra.extension_components I
  · rintro ⟨hI, hQ⟩
    exact isAmenableLieAlgebra_extension_of_components I hI hQ



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

/-- Subalgebra closure in Theorem G. -/
theorem isAmenableLieAlgebra_of_injective
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  isAmenableLieAlgebra_of_injective_aux f hf hQ


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


/-- The quotient-algebra clause of Theorem D. -/
theorem isAmenableLieAlgebra_quotient
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Surjective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := Q) :=
  hL.of_surjective f hf


/-- Subexponential growth of all finite coefficient filtrations of the
universal enveloping algebra implies Lie amenability. -/
theorem isAmenableLieAlgebra_of_subexponentialUEAGrowth
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (hU : HasSubexponentialAlgebraGrowth
      (k := k) (A := UniversalEnvelopingAlgebra k L)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let _ : FiniteDimensional k P := hP
  have hsub := hU P inferInstance
  obtain ⟨n, hn⟩ := exists_succ_ratio_le_of_subexponential
    (fun m ↦ sfinrank k (associativeGrowthBall k P m))
    (by
      change 0 < sfinrank k (k ∙ (1 : UniversalEnvelopingAlgebra k L))
      rw [sfinrank, finrank_span_singleton]
      · norm_num
      · intro hone
        have := congrArg (Coalgebra.counit (R := k)) hone
        simp at this)
    hsub ε hε
  let E := algebraBall P n
  let _ : FiniteDimensional k E := finiteDimensional_algebraBall P n
  have hE : E ≠ ⊥ := algebraBall_ne_bot P n
  refine ⟨E, hE, inferInstance, ?_⟩
  change (sfinrank k (algebraBall P (n + 1)) : ℚ) ≤
    (1 + ε) * sfinrank k (algebraBall P n)
  simpa only [associativeGrowthBall_eq_algebraBall] using hn



/-- A finite-dimensional Lie algebra is amenable.  Finite PBW filtration
steps provide the Følner subspaces. -/
theorem isAmenableLieAlgebra_of_finiteDimensional
    {L : Type v} [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let : FiniteDimensional k P := hP
  let b := Module.finBasis k L
  let r := Module.finrank k L
  obtain ⟨d, hPd⟩ :=
    UniversalEnvelopingAlgebra.exists_le_monomialFiltration_of_finite b P
  obtain ⟨n, hn⟩ :=
    UniversalEnvelopingAlgebra.exists_choose_shift_le r d ε hε
  let E := UniversalEnvelopingAlgebra.monomialFiltration b n
  let : FiniteDimensional k E :=
    UniversalEnvelopingAlgebra.finiteDimensional_monomialFiltration b n
  have hE : E ≠ ⊥ := by
    intro hbot
    have hone : (1 : UniversalEnvelopingAlgebra k L) ∈ E := by
      rw [← UniversalEnvelopingAlgebra.pbwMonomial_nil b]
      exact UniversalEnvelopingAlgebra.pbwMonomial_mem_filtration b [] (by simp)
    rw [hbot, Submodule.mem_bot] at hone
    have hne : (1 : UniversalEnvelopingAlgebra k L) ≠ 0 := by
      intro h
      have := congrArg (Coalgebra.counit (R := k)) h
      simp at this
    exact hne hone
  have hexp : actionExpansion P E ≤
      UniversalEnvelopingAlgebra.monomialFiltration b (d + n) := by
    rw [actionExpansion, sup_le_iff]
    constructor
    · exact UniversalEnvelopingAlgebra.monomialFiltration_mono b
        (Nat.le_add_left n d)
    · rw [actionSubspace_eq_map₂]
      apply Submodule.map₂_le.2
      intro x hx y hy
      exact UniversalEnvelopingAlgebra.mul_mem_monomialFiltration b
        (hPd hx) hy
  refine ⟨E, hE, inferInstance, ?_⟩
  let : FiniteDimensional k
      (UniversalEnvelopingAlgebra.monomialFiltration b (d + n)) :=
    UniversalEnvelopingAlgebra.finiteDimensional_monomialFiltration b (d + n)
  have hdim := Submodule.finrank_mono hexp
  rw [sfinrank, sfinrank]
  calc
    (Module.finrank k (actionExpansion P E) : ℚ) ≤
        (Module.finrank k
          (UniversalEnvelopingAlgebra.monomialFiltration b (d + n)) : ℚ) :=
      by exact_mod_cast hdim
    _ = (((d + n + r).choose r : ℕ) : ℚ) := by
      rw [UniversalEnvelopingAlgebra.finrank_monomialFiltration]
      simp only [Fintype.card_fin, r]
    _ ≤ (1 + ε) * (((n + r).choose r : ℕ) : ℚ) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
    _ = (1 + ε) * Module.finrank k E := by
      rw [show Module.finrank k E = (n + r).choose r by
        change Module.finrank k
          (UniversalEnvelopingAlgebra.monomialFiltration b n) = _
        rw [UniversalEnvelopingAlgebra.finrank_monomialFiltration]
        simp only [Fintype.card_fin, r]]


/-- Every finitely generated Lie algebra of genuine subexponential growth
is amenable; this is the PBW/Smith clause of Theorem G. -/
theorem isAmenableLieAlgebra_of_hasSubexponentialLieGrowth
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (hL : HasSubexponentialLieGrowth k L) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  obtain ⟨F, hF, hspan, hsub⟩ := hL
  let _ : FiniteDimensional k F := hF
  let β := LieGrowthBasisIndex k F
  let b := lieGrowthBasis k F hspan
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  cases isEmpty_or_nonempty β with
  | inl hempty =>
      let _ : IsEmpty β := hempty
      let _ : Fintype β := Fintype.ofFinite β
      let _ : Module.Finite k L := Module.Finite.of_basis b
      exact isAmenableLieAlgebra_of_finiteDimensional (k := k)
  | inr hnonempty =>
      let _ : Nonempty β := hnonempty
      apply isAmenableLieAlgebra_of_subexponentialUEAGrowth
      exact hasSubexponentialAlgebraGrowth_uea_of_generatingSubspace
        k F hspan hsub



/-- The locally subexponential-growth clause of Theorem G. -/
theorem isAmenableLieAlgebra_of_locallySubexponentialGrowth
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (hL : HasLocallySubexponentialGrowth k L) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  let S : Finset L → LieSubalgebra k L := fun s =>
    LieSubalgebra.lieSpan k L (s : Set L)
  apply isAmenableLieAlgebra_directedUnion S
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact LieSubalgebra.lieSpan_mono Finset.subset_union_left
    · exact LieSubalgebra.lieSpan_mono Finset.subset_union_right
  · apply top_unique
    intro x _hx
    exact (le_iSup S {x})
      (LieSubalgebra.subset_lieSpan (by simp))
  · intro s
    apply isAmenableLieAlgebra_of_hasSubexponentialLieGrowth
    exact hL (S s) (by
      dsimp [S]
      exact isFinitelyGeneratedLieAlgebra_lieSpan_finset k s)


/-- In particular, every Abelian Lie algebra is amenable. -/
theorem isAmenableLieAlgebra_of_isLieAbelian
    {L : Type v} [LieRing L] [LieAlgebra k L] (hL : IsLieAbelian L) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  isAmenableLieAlgebra_of_locallySubexponentialGrowth (k := k)
    (hasLocallySubexponentialGrowth_of_isLieAbelian k hL)


/-- A locally finite-dimensional Lie algebra is a directed union of its
finite-dimensional Lie subalgebras, hence is amenable. -/
theorem IsLocallyFiniteDimensionalLieAlgebra.isAmenableLieAlgebra
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (hL : IsLocallyFiniteDimensionalLieAlgebra k L) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let ι := {S : LieSubalgebra k L // Module.Finite k S}
  let S : ι → LieSubalgebra k L := fun i => i.1
  let _ : Nonempty ι := ⟨⟨⊥, Module.Finite.bot k L⟩⟩
  have hdir : Directed (· ≤ ·) S := by
    intro A B
    let : Module.Finite k A.1 := A.2
    let : Module.Finite k B.1 := B.2
    let P : Submodule k L := A.1.toSubmodule ⊔ B.1.toSubmodule
    let : FiniteDimensional k P :=
      Submodule.finite_sup A.1.toSubmodule B.1.toSubmodule
    obtain ⟨T, hPT, hT⟩ := hL P inferInstance
    exact ⟨⟨T, hT⟩,
      fun x hx => hPT ((le_sup_left : A.1.toSubmodule ≤ P) hx),
      fun x hx => hPT ((le_sup_right : B.1.toSubmodule ≤ P) hx)⟩
  have hsup : iSup S = ⊤ := by
    apply top_unique
    intro x _hx
    let P : Submodule k L := k ∙ x
    let : FiniteDimensional k P := by dsimp [P]; infer_instance
    obtain ⟨T, hPT, hT⟩ := hL P inferInstance
    exact le_iSup S ⟨T, hT⟩
      (hPT (Submodule.mem_span_singleton_self x))
  apply isAmenableLieAlgebra_directedUnion S hdir hsup
  intro i
  let : FiniteDimensional k i.1 := i.2
  exact isAmenableLieAlgebra_of_finiteDimensional (k := k)




end

end HopfAmenability
