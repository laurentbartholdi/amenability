/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.GroupPermanence
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The cleft Hopf sequence attached to a normal subgroup -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

section NormalSubgroup

variable (N : Subgroup G) [N.Normal]

local instance : DecidableEq (G ⧸ N) := Classical.decEq _

/-- A normalized choice of representative of every coset. -/
noncomputable def normalizedQuotientSection (q : G ⧸ N) : G :=
  if q = 1 then 1 else Classical.choose (Quotient.exists_rep q)

@[simp]
theorem normalizedQuotientSection_one :
    normalizedQuotientSection N (1 : G ⧸ N) = 1 := by
  simp [normalizedQuotientSection]

@[simp]
theorem quotientMk_normalizedQuotientSection (q : G ⧸ N) :
    QuotientGroup.mk' N (normalizedQuotientSection N q) = q := by
  by_cases hq : q = 1
  · subst q
    simp
  · simp only [normalizedQuotientSection, hq, ite_false]
    exact Classical.choose_spec (Quotient.exists_rep q)

/-- Linearization of the normalized representative choice. -/
noncomputable def normalizedQuotientCoalgebraSection :
    MonoidAlgebra k (G ⧸ N) →ₗc[k] MonoidAlgebra k G :=
  pointMapCoalgHom (k := k) (normalizedQuotientSection N)

@[simp]
theorem normalizedQuotientCoalgebraSection_one :
    normalizedQuotientCoalgebraSection (k := k) N 1 = 1 := by
  classical
  simp [normalizedQuotientCoalgebraSection, MonoidAlgebra.one_def]

theorem groupAlgebraProjection_section :
    (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap.comp
        (normalizedQuotientCoalgebraSection (k := k) N).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of q =>
      simp only [normalizedQuotientCoalgebraSection,
        groupAlgebraHopfHom, pointMapCoalgHom, LinearMap.coe_comp,
        Function.comp_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.mapDomainLinearMap_single, LinearMap.id_apply]
      change MonoidAlgebra.mapDomain (QuotientGroup.mk' N)
        (MonoidAlgebra.single (normalizedQuotientSection N q) 1) = _
      rw [MonoidAlgebra.mapDomain_single]
      rw [quotientMk_normalizedQuotientSection]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx => simp only [map_smul, hx]

/-- A right coinvariant has zero coefficient away from the kernel of the
quotient map. -/
theorem coeff_eq_zero_of_mem_rightCoinvariants
    (b : MonoidAlgebra k G)
    (hb : b ∈ rightCoinvariants
      (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)))
    (g : G) (hg : QuotientGroup.mk' N g ≠ 1) : b.coeff g = 0 := by
  classical
  change ((TensorProduct.map LinearMap.id
      (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := MonoidAlgebra k G)) -
      (TensorProduct.mk k (MonoidAlgebra k G) (MonoidAlgebra k (G ⧸ N))).flip 1) b = 0 at hb
  rw [LinearMap.sub_apply, sub_eq_zero] at hb
  let coord : MonoidAlgebra k G ⊗[k] MonoidAlgebra k (G ⧸ N) →ₗ[k] k :=
    (pointCoordinate (k := k) (QuotientGroup.mk' N g)).comp
      (TensorProduct.leftContract (pointCoordinate (k := k) g))
  have hcoord := congrArg coord hb
  have hneq : QuotientGroup.mk' N g ≠ (1 : G ⧸ N) := hg
  have hleft : coord
      (TensorProduct.map LinearMap.id
        (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap
          (Coalgebra.comul (R := k) (A := MonoidAlgebra k G) b)) = b.coeff g := by
    clear hb hcoord
    induction b using MonoidAlgebra.induction_on with
    | of x =>
        by_cases hx : x = g
        · subst x
          simp [coord, groupAlgebraHopfHom, pointCoordinate]
        · simp [coord, groupAlgebraHopfHom, pointCoordinate, hx]
    | add x y hx hy =>
        simpa using congrArg₂ (fun a b => a + b) hx hy
    | smul r x hx => simpa using congrArg (fun a => r • a) hx
  have hright : coord
      ((TensorProduct.mk k (MonoidAlgebra k G)
        (MonoidAlgebra k (G ⧸ N))).flip 1 b) = 0 := by
    have hcoe : (g : G ⧸ N) ≠ 1 := hneq
    simp [coord, pointCoordinate, MonoidAlgebra.one_def, hcoe]
  change coord
      (TensorProduct.map LinearMap.id
        (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap
          (Coalgebra.comul (R := k) (A := MonoidAlgebra k G) b)) =
    coord ((TensorProduct.mk k (MonoidAlgebra k G)
      (MonoidAlgebra k (G ⧸ N))).flip 1 b) at hcoord
  rw [hleft, hright] at hcoord
  exact hcoord

-- The finite-support induction deliberately normalizes the current equality
-- before the following tensor calculation.
set_option linter.flexible false in
/-- Conversely, an element supported on the kernel of the quotient map is a
right coinvariant. -/
theorem mem_rightCoinvariants_of_coeff_eq_zero
    (b : MonoidAlgebra k G)
    (hb : ∀ g : G, QuotientGroup.mk' N g ≠ 1 → b.coeff g = 0) :
    b ∈ rightCoinvariants
      (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)) := by
  classical
  change ((TensorProduct.map LinearMap.id
      (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := MonoidAlgebra k G)) -
      (TensorProduct.mk k (MonoidAlgebra k G) (MonoidAlgebra k (G ⧸ N))).flip 1) b = 0
  rw [LinearMap.sub_apply, sub_eq_zero]
  let leftMap := (TensorProduct.map LinearMap.id
    (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)).toAlgHom.toLinearMap).comp
      (Coalgebra.comul (R := k) (A := MonoidAlgebra k G))
  let rightMap :=
    (TensorProduct.mk k (MonoidAlgebra k G) (MonoidAlgebra k (G ⧸ N))).flip 1
  have aux : ∀ f : G →₀ k,
      (∀ g : G, QuotientGroup.mk' N g ≠ 1 → f g = 0) →
      leftMap (MonoidAlgebra.ofCoeff f) = rightMap (MonoidAlgebra.ofCoeff f) := by
    intro f hf
    induction f using Finsupp.induction with
    | zero => simp [leftMap, rightMap]
    | single_add g a f hgf ha ih =>
        have hg : QuotientGroup.mk' N g = 1 := by
          by_contra hne
          have hz := hf g hne
          have hfg : f g = 0 := by
            simpa [Finsupp.mem_support_iff] using hgf
          have ha0 : a = 0 := by
            calc
              a = (Finsupp.single g a + f) g := by simp [hfg]
              _ = 0 := hz
          exact ha ha0
        have hff : ∀ x : G, QuotientGroup.mk' N x ≠ 1 → f x = 0 := by
          intro x hx
          by_cases hxg : x = g
          · subst x
            simpa [Finsupp.mem_support_iff] using hgf
          · simpa [hxg] using hf x hx
        rw [MonoidAlgebra.ofCoeff_add, map_add, map_add, ih hff]
        have hcoe : (g : G ⧸ N) = 1 := hg
        simp [leftMap, rightMap, groupAlgebraHopfHom, hcoe,
          MonoidAlgebra.one_def, MonoidAlgebra.mapDomain_single]
        calc
          MonoidAlgebra.single g (1 : k) ⊗ₜ[k]
                MonoidAlgebra.single (1 : G ⧸ N) a =
              MonoidAlgebra.single g (1 : k) ⊗ₜ[k]
                (a • MonoidAlgebra.single (1 : G ⧸ N) (1 : k)) := by
            simp [MonoidAlgebra.smul_single]
          _ = (a • MonoidAlgebra.single g (1 : k)) ⊗ₜ[k]
                MonoidAlgebra.single (1 : G ⧸ N) (1 : k) := by
            exact TensorProduct.tmul_smul _ _ _
          _ = MonoidAlgebra.single g a ⊗ₜ[k]
                MonoidAlgebra.single (1 : G ⧸ N) (1 : k) := by
            simp [MonoidAlgebra.smul_single]
  exact aux b.coeff hb

theorem mem_range_subgroupGroupAlgebra_iff_coeff
    (b : MonoidAlgebra k G) :
    b ∈ LinearMap.range
        (subgroupGroupAlgebraEmbedding (k := k) N).toAlgHom.toLinearMap ↔
      ∀ g : G, QuotientGroup.mk' N g ≠ 1 → b.coeff g = 0 := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ g hg
    change (MonoidAlgebra.mapDomain (fun n : N => (n : G)) a).coeff g = 0
    change Finsupp.mapDomain (fun n : N => (n : G)) a.coeff g = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨n, rfl⟩
    exact hg ((QuotientGroup.eq_one_iff (n : G)).2 n.property)
  · intro hb
    have hrange : b.coeff ∈ Set.range
        (Finsupp.mapDomain (fun n : N => (n : G))) := by
      rw [Finsupp.mem_range_mapDomain_iff _ Subtype.val_injective]
      intro g hg
      apply hb g
      intro hq
      have hgN : g ∈ N := (QuotientGroup.eq_one_iff g).1 hq
      exact hg ⟨⟨g, hgN⟩, rfl⟩
    obtain ⟨f, hf⟩ := hrange
    refine ⟨MonoidAlgebra.ofCoeff f, ?_⟩
    apply MonoidAlgebra.coeff_injective
    simpa [subgroupGroupAlgebraEmbedding, groupAlgebraHopfHom,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain] using hf

/-- The right coinvariants of `k[G] → k[G/N]` are exactly `k[N]`. -/
theorem groupAlgebra_rightCoinvariants :
    LinearMap.range
        (subgroupGroupAlgebraEmbedding (k := k) N).toAlgHom.toLinearMap =
      rightCoinvariants
        (groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)) := by
  ext b
  rw [mem_range_subgroupGroupAlgebra_iff_coeff]
  constructor
  · exact mem_rightCoinvariants_of_coeff_eq_zero N b
  · intro hb
    exact fun g hg => coeff_eq_zero_of_mem_rightCoinvariants N b hb g hg

/-- The intrinsic cleft exact sequence of group Hopf algebras associated to
a normal subgroup.  Its normal basis is derived by Theorem E. -/
noncomputable def normalSubgroupCleftExactSequence :
    CleftExactSequence (k := k) (MonoidAlgebra k N)
      (MonoidAlgebra k G) (MonoidAlgebra k (G ⧸ N)) where
  inclusion := (subgroupGroupAlgebraEmbedding (k := k) N).toHopfAlgebraHom
  projection := groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)
  inclusion_injective :=
    (subgroupGroupAlgebraEmbedding (k := k) N).injective
  projection_surjective := by
    intro q
    change ∃ x, MonoidAlgebra.mapDomain (QuotientGroup.mk' N) x = q
    obtain ⟨f, hf⟩ :=
      Finsupp.mapDomain_surjective (QuotientGroup.mk'_surjective N) q.coeff
    refine ⟨MonoidAlgebra.ofCoeff f, ?_⟩
    apply MonoidAlgebra.coeff_injective
    exact hf
  projection_inclusion := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of n =>
        have hn : ((n : G) : G ⧸ N) = 1 :=
          (QuotientGroup.eq_one_iff (n : G)).2 n.property
        simp [subgroupGroupAlgebraEmbedding, groupAlgebraHopfHom, hn]
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul r x hx =>
        rw [map_smul, map_smul, hx]
        simp [Algebra.smul_def]
  coalgebraSection := normalizedQuotientCoalgebraSection (k := k) N
  projection_section := groupAlgebraProjection_section (k := k) N
  section_one := normalizedQuotientCoalgebraSection_one (k := k) N
  coinvariants := groupAlgebra_rightCoinvariants (k := k) N

/-- Group amenability is stable under, and detected by, extensions.  The
proof is the application of Theorem E to the intrinsic group-algebra cleft
sequence above. -/
theorem isAmenableGroup_normalExtension_iff (k : Type u) [Field k] :
    IsAmenableGroup (G := G) ↔
      IsAmenableGroup (G := N) ∧ IsAmenableGroup (G := G ⧸ N) := by
  rw [isAmenableGroup_iff_groupAlgebra (k := k) (G := G),
    isAmenableGroup_iff_groupAlgebra (k := k) (G := N),
    isAmenableGroup_iff_groupAlgebra (k := k) (G := G ⧸ N)]
  exact isAmenableHopfAlgebra_cleftExtension_iff
    (normalSubgroupCleftExactSequence (k := k) N)

theorem isAmenableGroup_normalExtension
    (k : Type u) [Field k]
    (hN : IsAmenableGroup (G := N))
    (hQ : IsAmenableGroup (G := G ⧸ N)) : IsAmenableGroup (G := G) :=
  (isAmenableGroup_normalExtension_iff (k := k) N).2 ⟨hN, hQ⟩

/-- The ideal of `k[G]` generated by the augmentation differences `n - 1`
for `n ∈ N`.  This is the explicit product `k[G] k[N]⁺`. -/
def normalSubgroupAugmentationIdeal : Ideal (MonoidAlgebra k G) :=
  Ideal.span {x | ∃ n : N,
    x = MonoidAlgebra.single (n : G) 1 - 1}

theorem normalSubgroupAugmentationIdeal_le_projection_ker :
    normalSubgroupAugmentationIdeal (k := k) N ≤
      RingHom.ker
        (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' N)) := by
  apply Ideal.span_le.2
  rintro x ⟨n, rfl⟩
  change (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' N))
      (MonoidAlgebra.single (n : G) 1 - 1) = 0
  have hn : ((n : G) : G ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff (n : G)).2 n.property
  rw [map_sub, map_one]
  change MonoidAlgebra.mapDomain (QuotientGroup.mk' N)
      (MonoidAlgebra.single (n : G) 1) - 1 = 0
  simp [MonoidAlgebra.mapDomain_single, hn, MonoidAlgebra.one_def]

theorem sub_section_projection_mem_normalSubgroupAugmentationIdeal
    (b : MonoidAlgebra k G) :
    b - normalizedQuotientCoalgebraSection (k := k) N
        ((groupAlgebraHopfHom (k := k) (QuotientGroup.mk' N)) b) ∈
      normalSubgroupAugmentationIdeal (k := k) N := by
  classical
  induction b using MonoidAlgebra.induction_on with
  | of g =>
      let s := normalizedQuotientSection N (QuotientGroup.mk' N g)
      have hs : QuotientGroup.mk' N s = QuotientGroup.mk' N g :=
        quotientMk_normalizedQuotientSection N _
      have hnmem : s⁻¹ * g ∈ N := by
        rw [← QuotientGroup.eq_one_iff]
        change QuotientGroup.mk' N (s⁻¹ * g) = 1
        rw [map_mul, map_inv, hs]
        simp
      let n : N := ⟨s⁻¹ * g, hnmem⟩
      have hsn : s * (n : G) = g := by simp [n]
      have hgen : MonoidAlgebra.single (n : G) (1 : k) - 1 ∈
          normalSubgroupAugmentationIdeal (k := k) N :=
        Ideal.subset_span ⟨n, rfl⟩
      have hmul := (normalSubgroupAugmentationIdeal (k := k) N).mul_mem_left
        (MonoidAlgebra.single s (1 : k)) hgen
      simpa [normalizedQuotientCoalgebraSection, groupAlgebraHopfHom,
        pointMapCoalgHom, MonoidAlgebra.of_apply,
        MonoidAlgebra.mapDomainLinearMap_single,
        MonoidAlgebra.mapDomain_single, s, n,
        MonoidAlgebra.single_mul_single, mul_sub, hsn] using hmul
  | add x y hx hy =>
      simpa only [map_add, add_sub_add_comm] using
        (normalSubgroupAugmentationIdeal (k := k) N).add_mem hx hy
  | smul r x hx =>
      rw [map_smul, map_smul, ← smul_sub]
      exact ((normalSubgroupAugmentationIdeal (k := k) N :
        Submodule (MonoidAlgebra k G) (MonoidAlgebra k G)).restrictScalars k).smul_mem r hx

/-- The explicit quotient-ideal identity
`ker(k[G] → k[G/N]) = k[G] k[N]⁺`. -/
theorem groupAlgebra_projection_ker :
    RingHom.ker (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' N)) =
      normalSubgroupAugmentationIdeal (k := k) N := by
  apply le_antisymm
  · intro b hb
    have hp : MonoidAlgebra.mapDomain (QuotientGroup.mk' N) b = 0 := hb
    have hmem := sub_section_projection_mem_normalSubgroupAugmentationIdeal
      (k := k) N b
    change b - normalizedQuotientCoalgebraSection (k := k) N
      (MonoidAlgebra.mapDomain (QuotientGroup.mk' N) b) ∈ _ at hmem
    rw [hp, map_zero, sub_zero] at hmem
    exact hmem
  · exact normalSubgroupAugmentationIdeal_le_projection_ker (k := k) N

noncomputable instance normalSubgroupAugmentationIdeal_isTwoSided :
    (normalSubgroupAugmentationIdeal (k := k) N).IsTwoSided := by
  rw [← groupAlgebra_projection_ker (k := k) N]
  infer_instance

/-- Consequently `k[G] / k[G]k[N]⁺ ≃ k[G/N]`. -/
noncomputable def groupAlgebraQuotientEquiv :
    (MonoidAlgebra k G ⧸
      RingHom.ker (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' N))) ≃+*
      MonoidAlgebra k (G ⧸ N) := by
  apply RingHom.quotientKerEquivOfSurjective
  exact (normalSubgroupCleftExactSequence (k := k) N).projection_surjective

end NormalSubgroup

end

end HopfAmenability
