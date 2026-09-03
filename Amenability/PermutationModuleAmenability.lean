/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremC
import Amenability.GroupAmenability
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # Permutation-module amenability infrastructure -/

open Coalgebra Module TensorProduct
namespace HopfAmenability
noncomputable section
universe u v w


variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G]

local notation "kG" => MonoidAlgebra k G

/-- The action of a group on a module over its group algebra. -/
@[instance_reducible]
noncomputable def groupActionOfModule
    [AddCommGroup V] [Module k V] [Module kG V] [IsScalarTower k kG V] :
    MulAction G V where
  smul g v := (MonoidAlgebra.single g (1 : k) : kG) • v
  one_smul v := by
    change (MonoidAlgebra.single (1 : G) (1 : k) : kG) • v = v
    rw [← MonoidAlgebra.one_def]
    exact one_smul kG v
  mul_smul g h v := by
    change (MonoidAlgebra.single (g * h) (1 : k) : kG) • v =
      (MonoidAlgebra.single g (1 : k) : kG) •
        (MonoidAlgebra.single h (1 : k) : kG) • v
    rw [← mul_smul, MonoidAlgebra.single_mul_single]
    simp

/-- The finite subcoalgebra spanned by a prescribed finite set of group-like
basis elements. -/
noncomputable def finiteGroupSpan (T : Finset G) :
    FiniteSubcoalgebra k kG where
  carrier := Submodule.span k (groupBasis (k := k) '' (T : Set G))
  isSubcoalgebra := by
    let P := Submodule.span k (groupBasis (k := k) '' (T : Set G))
    let stable : Submodule k kG :=
      (LinearMap.range (TensorProduct.mapIncl P P)).comap Coalgebra.comul
    change P ≤ stable
    apply Submodule.span_le.2
    rintro _ ⟨g, hg, rfl⟩
    let gp : P := ⟨groupBasis (k := k) g,
      Submodule.subset_span ⟨g, hg, rfl⟩⟩
    refine ⟨gp ⊗ₜ[k] gp, ?_⟩
    simp [gp, groupBasis, TensorProduct.mapIncl]
  finiteDimensional :=
    FiniteDimensional.span_of_finite k (T.finite_toSet.image _)

omit [Group G] in
theorem finiteGroupSpan_carrier (T : Finset G) :
    (finiteGroupSpan (k := k) T).carrier =
      Submodule.span k (groupBasis (k := k) '' (T : Set G)) :=
  rfl

omit [Group G] in
theorem finrank_finiteGroupSpan (T : Finset G) :
    finrank k (finiteGroupSpan (k := k) T).carrier = T.card := by
  classical
  rw [finiteGroupSpan_carrier]
  have himage : groupBasis (k := k) '' (T : Set G) =
      Set.range (fun g : (T : Set G) => groupBasis (k := k) (g : G)) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  rw [himage, finrank_span_eq_card]
  · simp
  · exact (MonoidAlgebra.basis G k).linearIndependent.comp
      (fun g : (T : Set G) => g.1) Subtype.val_injective

omit [Group G] in
/-- The spans of the elements of a finite set of group-likes have their
obvious complete subcoalgebra flag. -/
theorem finiteGroupSpan_hasCompleteSubcoalgebraFlag (T : Finset G) :
    PrimalTransfer.HasCompleteSubcoalgebraFlag (finiteGroupSpan (k := k) T) := by
  classical
  induction T using Finset.induction with
  | empty =>
      apply PrimalTransfer.HasCompleteSubcoalgebraFlag.bot
      simp [finiteGroupSpan]
  | @insert g T hg ih =>
      apply PrimalTransfer.HasCompleteSubcoalgebraFlag.step ih
      · rw [finiteGroupSpan_carrier, finiteGroupSpan_carrier]
        apply Submodule.span_mono
        exact Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert g T))
      · rw [finrank_finiteGroupSpan, finrank_finiteGroupSpan,
          Finset.card_insert_of_notMem hg]

section FiniteConfiguration

variable [AddCommGroup V] [Module k V]

local notation "kV" => MonoidAlgebra k V

/-- The tensor subspace which records a finite configuration with a distinct
formal basis tag on its first tensor factor. -/
def configurationTensor (A : Finset V) : Submodule k (kV ⊗[k] V) :=
  Submodule.span k (Set.range fun a : (A : Set V) =>
    pointBasis (k := k) (a : V) ⊗ₜ[k] (a : V))

/-- Nonzero vectors tagged by their formal basis vectors give a linearly
independent family of diagonal tensors. -/
theorem configurationTensors_linearIndependent (A : Finset V)
    (hA0 : ∀ a ∈ A, a ≠ 0) :
    LinearIndependent k (fun a : (A : Set V) =>
      pointBasis (k := k) (a : V) ⊗ₜ[k] (a : V)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hcontract := congrArg
    (TensorProduct.leftContract (pointCoordinate (k := k) (a : V))) hc
  simp only [map_sum, map_smul, TensorProduct.leftContract_tmul,
    pointCoordinate_pointBasis] at hcontract
  have ha0 : (a : V) ≠ 0 := hA0 a a.2
  have hac : c a • (a : V) = 0 := by
    have hsum :
        (∑ x, c x • (if (a : V) = (x : V) then (1 : k) else 0) • (x : V)) =
          c a • (a : V) := by
      calc
        _ = c a • (if (a : V) = (a : V) then (1 : k) else 0) • (a : V) :=
          Fintype.sum_eq_single a (by
            intro b hba
            have hab : (a : V) ≠ (b : V) := by
              intro hab
              exact hba (Subtype.ext hab.symm)
            simp [hab])
        _ = _ := by simp
    rw [hsum, map_zero] at hcontract
    exact hcontract
  exact (smul_eq_zero.mp hac).resolve_right ha0

/-- The tagged configuration subspace has dimension equal to the cardinality
of the configuration. -/
theorem finrank_configurationTensor (A : Finset V)
    (hA0 : ∀ a ∈ A, a ≠ 0) :
    finrank k (configurationTensor (k := k) A) = A.card := by
  classical
  rw [configurationTensor,
    finrank_span_eq_card (configurationTensors_linearIndependent A hA0)]
  simp

omit [Group G] in
/-- A tagged finite configuration is supported on the spans of its tags and
of its underlying vectors. -/
theorem configurationTensor_le_range_mapIncl (A : Finset V) :
    configurationTensor (k := k) A ≤
      LinearMap.range (TensorProduct.mapIncl
        (pointSpan (k := k) A)
        (Submodule.span k (A : Set V))) := by
  apply Submodule.span_le.2
  rintro _ ⟨a, rfl⟩
  let pa : pointSpan (k := k) A :=
    ⟨pointBasis (k := k) (a : V),
      Submodule.subset_span ⟨a, a.2, rfl⟩⟩
  let va : Submodule.span k (A : Set V) :=
    ⟨(a : V), Submodule.subset_span a.2⟩
  exact ⟨pa ⊗ₜ[k] va, rfl⟩

end FiniteConfiguration

section ModuleConfiguration

variable [AddCommGroup V] [Module (MonoidAlgebra k G) V]

/-- Expansion of a finite vector configuration by a finite set of group
elements, using the action induced by the group-algebra module structure. -/
def moduleGroupSetExpansion (S : Finset G) (A : Finset V) : Finset V := by
  classical
  exact (S.product A).image fun p =>
    (MonoidAlgebra.single p.1 (1 : k) : kG) • p.2

theorem mem_moduleGroupSetExpansion (S : Finset G) (A : Finset V)
    (g : G) (hg : g ∈ S) (a : V) (ha : a ∈ A) :
    (MonoidAlgebra.single g (1 : k) : kG) • a ∈
      moduleGroupSetExpansion (k := k) S A := by
  classical
  apply Finset.mem_image.2
  exact ⟨(g, a), Finset.mem_product.2 ⟨hg, ha⟩, rfl⟩

theorem subset_moduleGroupSetExpansion_of_one_mem
    (S : Finset G) (A : Finset V) (h1 : 1 ∈ S) :
    (A : Set V) ⊆ moduleGroupSetExpansion (k := k) S A := by
  intro a ha
  have hmem := mem_moduleGroupSetExpansion (k := k) S A 1 h1 a ha
  rw [← MonoidAlgebra.one_def, one_smul] at hmem
  exact hmem

theorem moduleGroupSetExpansion_ne_zero
    (S : Finset G) (A : Finset V)
    (hA0 : ∀ a ∈ A, a ≠ 0) :
    ∀ v ∈ moduleGroupSetExpansion (k := k) S A, v ≠ 0 := by
  classical
  intro v hv
  rcases Finset.mem_image.1 hv with ⟨⟨g, a⟩, hga, rfl⟩
  have ha0 := hA0 a (Finset.mem_product.1 hga).2
  intro hzero
  have hinv := congrArg
    (fun w : V => (MonoidAlgebra.single g⁻¹ (1 : k) : kG) • w) hzero
  rw [smul_zero, ← mul_smul, MonoidAlgebra.single_mul_single] at hinv
  have hinv' : (MonoidAlgebra.single (1 : G) (1 : k) : kG) • a = 0 := by
    simpa using hinv
  rw [← MonoidAlgebra.one_def, one_smul] at hinv'
  exact ha0 hinv'

end ModuleConfiguration

section Linearization

variable [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

local notation "kV" => MonoidAlgebra k V

set_option maxHeartbeats 800000 in
-- The proof internalizes two tagged tensor configurations and transports a
-- complete group-like flag through the coefficient-density construction.
/-- Linearization of a finite configuration (Lemma
`finite-configuration-linearization` in the article). -/
theorem exists_submodule_ratio_le_of_finite_configuration
    (S : Finset G) (h1 : 1 ∈ S)
    (A : Finset V) (hA : A.Nonempty)
    (hA0 : ∀ a ∈ A, a ≠ 0) :
    ∃ E : Submodule k V,
      E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k
            (actionSubspace (finiteGroupSpan (k := k) S).carrier E) : ℚ) /
              finrank k E ≤
          ((moduleGroupSetExpansion (k := k) S A).card : ℚ) / A.card := by
  classical
  let : MulAction G V := groupActionOfModule (k := k) (G := G) (V := V)
  let : Module kG kV := groupAlgebraModule
  let : IsScalarTower k kG kV :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change (groupActionRepresentation (k := k) (G := G) (X := V)).asAlgebraHom
        (algebraMap k kG r) m = r • m
      rw [(groupActionRepresentation (k := k) (G := G) (X := V)).asAlgebraHom.commutes]
      rfl)
  let : IsHopfModuleCoalgebra k kG kV := {
    counit_action := by
      ext g : 2
      ext x : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single]
    comul_action := by
      ext g : 2
      ext x : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single, MonoidAlgebra.comul_single,
        TensorProduct.comul_tmul] }
  let T : Finset V := moduleGroupSetExpansion (k := k) S A
  let P : Submodule k kV := pointSpan (k := k) T
  let R : Submodule k V := Submodule.span k (A : Set V)
  let R' : Submodule k V := Submodule.span k (T : Set V)
  let X₀ : Submodule k (kV ⊗[k] V) := configurationTensor (k := k) A
  let Y₀ : Submodule k (kV ⊗[k] V) := configurationTensor (k := k) T
  have hAT : (A : Set V) ⊆ T := by
    exact subset_moduleGroupSetExpansion_of_one_mem (k := k) S A h1
  have hpointAT : pointSpan (k := k) A ≤ P := by
    dsimp [P]
    apply Submodule.span_mono
    exact Set.image_mono hAT
  have hXsupport : X₀ ≤ LinearMap.range (TensorProduct.mapIncl P R) := by
    dsimp [X₀, R]
    exact (configurationTensor_le_range_mapIncl (k := k) A).trans
      (range_mapIncl_mono hpointAT le_rfl)
  have hYsupport : Y₀ ≤ LinearMap.range (TensorProduct.mapIncl P R') := by
    dsimp [Y₀, P, R']
    exact configurationTensor_le_range_mapIncl (k := k) T
  let : FiniteDimensional k P := by
    dsimp [P, pointSpan]
    exact FiniteDimensional.span_of_finite k (T.finite_toSet.image _)
  let : FiniteDimensional k R := by
    dsimp [R]
    exact FiniteDimensional.span_of_finite k A.finite_toSet
  let : FiniteDimensional k R' := by
    dsimp [R']
    exact FiniteDimensional.span_of_finite k T.finite_toSet
  let X : Submodule k (P ⊗[k] R) := internalTensorSubspace P R X₀
  let Y : Submodule k (P ⊗[k] R') := internalTensorSubspace P R' Y₀
  have hXimage : ambientTensorImage P R X = X₀ :=
    ambientTensorImage_internalTensorSubspace P R X₀ hXsupport
  have hYimage : ambientTensorImage P R' Y = Y₀ :=
    ambientTensorImage_internalTensorSubspace P R' Y₀ hYsupport
  have hT0 : ∀ v ∈ T, v ≠ 0 := by
    exact moduleGroupSetExpansion_ne_zero (k := k) S A hA0
  have hdimX : finrank k X = A.card := by
    calc
      finrank k X = finrank k (ambientTensorImage P R X) :=
        (ambientTensorImageEquiv P R X).finrank_eq
      _ = finrank k X₀ := by rw [hXimage]
      _ = A.card := finrank_configurationTensor A hA0
  have hdimY : finrank k Y = T.card := by
    calc
      finrank k Y = finrank k (ambientTensorImage P R' Y) :=
        (ambientTensorImageEquiv P R' Y).finrank_eq
      _ = finrank k Y₀ := by rw [hYimage]
      _ = T.card := finrank_configurationTensor T hT0
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hzero : finrank k X = 0 := by rw [hbot, finrank_bot]
    rw [hdimX] at hzero
    exact hA.ne_empty (Finset.card_eq_zero.1 hzero)
  have hT : T.Nonempty := by
    rcases hA with ⟨a, ha⟩
    exact ⟨a, hAT ha⟩
  have hPpos : 0 < finrank k P := by
    dsimp [P]
    rw [finrank_pointSpan]
    exact Finset.card_pos.2 hT
  have hact : ∀ (b : (finiteGroupSpan (k := k) S).carrier) (r : R),
      (b : kG) • (r : V) ∈ R' := by
    intro b r
    have hb : (b : kG) ∈ Submodule.span k
        (groupBasis (k := k) '' (S : Set G)) := by
      simpa only [finiteGroupSpan_carrier] using b.2
    refine Submodule.span_induction
      (p := fun x _ => x • (r : V) ∈ R') ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨g, hg, rfl⟩
      refine Submodule.span_induction
        (p := fun x _ => groupBasis (k := k) g • x ∈ R')
        ?_ ?_ ?_ ?_ r.2
      · intro a ha
        exact Submodule.subset_span
          (mem_moduleGroupSetExpansion (k := k) S A g hg a ha)
      · simp
      · intro x y hx hy ihx ihy
        simpa only [smul_add] using R'.add_mem ihx ihy
      · intro c x hx ihx
        rw [smul_comm]
        exact R'.smul_mem c ihx
    · simp
    · intro x y hx hy ihx ihy
      simpa only [add_smul] using R'.add_mem ihx ihy
    · intro c x hx ihx
      rw [smul_assoc]
      exact R'.smul_mem c ihx
  have hdiag₀ : ∀ (b : kG), b ∈ (finiteGroupSpan (k := k) S).carrier →
      ∀ z : kV ⊗[k] V, z ∈ X₀ →
        diagonalHopfActionBy (k := k) (H := kG) b z ∈ Y₀ := by
    intro b hb
    rw [finiteGroupSpan_carrier] at hb
    refine Submodule.span_induction
      (p := fun b _ => ∀ z : kV ⊗[k] V, z ∈ X₀ →
        diagonalHopfActionBy (k := k) (H := kG) b z ∈ Y₀) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨g, hg, rfl⟩ z hz
      refine Submodule.span_induction
        (p := fun z _ =>
          diagonalHopfActionBy (k := k) (H := kG)
            (groupBasis (k := k) g) z ∈ Y₀) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨a, rfl⟩
        have hgLike : IsGroupLikeElem k (groupBasis (k := k) g) := by
          constructor <;> simp [groupBasis]
        rw [diagonalHopfActionBy_tmul_of_groupLike hgLike]
        change
          (MonoidAlgebra.single g (1 : k) •
              MonoidAlgebra.single (a : V) (1 : k)) ⊗ₜ[k]
            ((MonoidAlgebra.single g (1 : k) : kG) • (a : V)) ∈ Y₀
        rw [group_single_smul_single]
        simp only [one_mul]
        apply Submodule.subset_span
        refine ⟨⟨(MonoidAlgebra.single g (1 : k) : kG) • (a : V),
          mem_moduleGroupSetExpansion (k := k) S A g hg a a.2⟩, ?_⟩
        rfl
      · simp
      · intro x y hx hy ihx ihy
        simpa only [map_add] using Y₀.add_mem ihx ihy
      · intro c x hx ihx
        simpa only [map_smul] using Y₀.smul_mem c ihx
    · intro z hz
      change diagonalHopfAction (k := k) (H := kG)
        (M := kV) (Q := V) (0 ⊗ₜ[k] z) ∈ Y₀
      simp
    · intro b c hb hc ihb ihc z hz
      change diagonalHopfAction (k := k) (H := kG)
        (M := kV) (Q := V) ((b + c) ⊗ₜ[k] z) ∈ Y₀
      rw [add_tmul, map_add]
      exact Y₀.add_mem (ihb z hz) (ihc z hz)
    · intro c b hb ih z hz
      change diagonalHopfAction (k := k) (H := kG)
        (M := kV) (Q := V) ((c • b) ⊗ₜ[k] z) ∈ Y₀
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Y₀.smul_mem c (ih z hz)
  have hdiag : ∀ (b : (finiteGroupSpan (k := k) S).carrier) (x : X),
      diagonalHopfActionBy (k := k) (H := kG) (b : kG)
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P R' Y := by
    intro b x
    rw [hYimage]
    apply hdiag₀ b b.2 (TensorProduct.mapIncl P R x)
    rw [← hXimage]
    exact ⟨x, x.2, rfl⟩
  have htransfer : ∀ t : ℚ,
      actionSubspace (finiteGroupSpan (k := k) S).carrier
          (ambientImage R (coefficientDensitySubspace X t)) ≤
        ambientImage R' (coefficientDensitySubspace Y t) :=
    fun t => coefficientDensity_transfer_of_completeFlag
      (finiteGroupSpan (k := k) S)
      (finiteGroupSpan_hasCompleteSubcoalgebraFlag (k := k) S)
      P R R' hPpos X Y hdiag hact t
  obtain ⟨t, hCt, hratio⟩ :=
    exists_coefficient_ratio_le_of_pointwise_transfer
      (finiteGroupSpan (k := k) S).carrier P hPpos R R' X Y hXne htransfer
  let E : Submodule k V := ambientImage R (coefficientDensitySubspace X t)
  let : FiniteDimensional k E :=
    FiniteDimensional.of_surjective
      (ambientImageEquiv R (coefficientDensitySubspace X t)).toLinearMap
      (ambientImageEquiv R (coefficientDensitySubspace X t)).surjective
  have hE : E ≠ ⊥ := by
    intro hbot
    apply hCt
    rw [eq_bot_iff]
    intro c hc
    have hcE : ((c : R) : V) ∈ E := ⟨c, hc, rfl⟩
    rw [hbot] at hcE
    exact Subtype.ext (by simpa using hcE)
  refine ⟨E, hE, inferInstance, ?_⟩
  have hdimE : finrank k E =
      sfinrank k (coefficientDensitySubspace X t) :=
    finrank_ambientImage R (coefficientDensitySubspace X t)
  change
    (sfinrank k
        (actionSubspace (finiteGroupSpan (k := k) S).carrier
          (ambientImage R (coefficientDensitySubspace X t))) : ℚ) /
        finrank k E ≤ (T.card : ℚ) / A.card
  rw [hdimE]
  rw [hdimX, hdimY] at hratio
  exact hratio

end Linearization

section FiniteGroupSupport

/-- Every finite-dimensional subspace of a group algebra is supported on a
finite set of group elements, which may be chosen to contain the identity. -/
theorem exists_finiteGroupSpan_containing
    (F : Submodule k kG) [FiniteDimensional k F] :
    ∃ S : Finset G, 1 ∈ S ∧ F ≤ (finiteGroupSpan (k := k) S).carrier := by
  classical
  let e := Module.finBasis k F
  let S : Finset G := insert 1
    (Finset.univ.biUnion fun i => ((e i : kG).coeff.support))
  refine ⟨S, ?_, ?_⟩
  · dsimp [S]
    exact Finset.mem_insert_self (1 : G) _
  intro x hx
  let xF : F := ⟨x, hx⟩
  have hxsum : x = ∑ i, (e.repr xF) i • (e i : kG) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      (congrArg Subtype.val (e.sum_repr xF)).symm
  rw [hxsum, finiteGroupSpan_carrier]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  change (e i : kG) ∈ Submodule.span k
    ((fun g : G => MonoidAlgebra.single g (1 : k)) '' (S : Set G))
  rw [← MonoidAlgebra.supported_eq_span_single, MonoidAlgebra.mem_supported]
  intro g hg
  dsimp [S]
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hg⟩)

end FiniteGroupSupport

section PointMap

variable {X : Type*} {Y : Type*}

/-- Linearizing a map of sets gives a counital coalgebra morphism between
the corresponding diagonal coalgebras. -/
def pointMapCoalgHom (f : X → Y) :
    MonoidAlgebra k X →ₗc[k] MonoidAlgebra k Y where
  toLinearMap := MonoidAlgebra.mapDomainLinearMap k k f
  counit_comp := by
    ext x : 2
    simp
  map_comp_comul := by
    ext x : 2
    simp

@[simp]
theorem pointMapCoalgHom_single (f : X → Y) (x : X) (a : k) :
    pointMapCoalgHom (k := k) f (MonoidAlgebra.single x a) =
      MonoidAlgebra.single (f x) a := by
  exact MonoidAlgebra.mapDomain_single

theorem pointMapCoalgHom_surjective {f : X → Y}
    (hf : Function.Surjective f) :
    Function.Surjective (pointMapCoalgHom (k := k) f) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hx

end PointMap

section QuotientActions

variable {X : Type*} {Y : Type*}
variable [MulAction G X] [MulAction G Y]

/-- Amenability of a group action passes to a surjective equivariant image.
This is the formal counterpart of pushing forward the invariant mean in the
proof of Theorem C. -/
theorem IsAmenableGroupAction.of_surjective_equivariant
    (k : Type u) [Field k]
    [DecidableEq G] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Surjective f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hX : IsAmenableGroupAction (G := G) (X := X)) :
    IsAmenableGroupAction (G := G) (X := Y) := by
  let : Module (MonoidAlgebra k G) (MonoidAlgebra k X) := groupAlgebraModule
  let : IsScalarTower k (MonoidAlgebra k G) (MonoidAlgebra k X) :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change (groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom
        (algebraMap k (MonoidAlgebra k G) r) m = r • m
      rw [(groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom.commutes]
      rfl)
  let : IsHopfModuleCoalgebra k (MonoidAlgebra k G) (MonoidAlgebra k X) := {
    counit_action := by
      ext g : 2
      ext x : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single]
    comul_action := by
      ext g : 2
      ext x : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single, MonoidAlgebra.comul_single,
        TensorProduct.comul_tmul] }
  let : Module (MonoidAlgebra k G) (MonoidAlgebra k Y) := groupAlgebraModule
  let : IsScalarTower k (MonoidAlgebra k G) (MonoidAlgebra k Y) :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change (groupActionRepresentation (k := k) (G := G) (X := Y)).asAlgebraHom
        (algebraMap k (MonoidAlgebra k G) r) m = r • m
      rw [(groupActionRepresentation (k := k) (G := G) (X := Y)).asAlgebraHom.commutes]
      rfl)
  let : IsHopfModuleCoalgebra k (MonoidAlgebra k G) (MonoidAlgebra k Y) := {
    counit_action := by
      ext g : 2
      ext y : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single]
    comul_action := by
      ext g : 2
      ext y : 2
      apply LinearMap.ext
      intro a
      simp [group_single_smul_single, MonoidAlgebra.comul_single,
        TensorProduct.comul_tmul] }
  have hXaction : HasActionFolnerSubspaces
      (k := k) (H := MonoidAlgebra k G) (M := MonoidAlgebra k X) := by
    intro F hF ε hε
    let : FiniteDimensional k F := hF
    obtain ⟨S, h1, hFS⟩ := exists_finiteGroupSpan_containing (k := k) F
    obtain ⟨E, hE, hEfd, hEfolner⟩ :=
      hX.hasFolnerSubspaces (k := k) S ε hε
    have hspanLe : (finiteGroupSpan (k := k) S).carrier ≤
        (groupActingSubcoalgebra (k := k) S).carrier := by
      rw [finiteGroupSpan_carrier, groupActingSubcoalgebra_carrier]
      apply Submodule.span_mono
      exact Set.image_mono (Finset.coe_subset.mpr
        (Finset.subset_insert (1 : G) S))
    have h1act : (1 : MonoidAlgebra k G) ∈
        (groupActingSubcoalgebra (k := k) S).carrier := by
      rw [groupActingSubcoalgebra_carrier]
      have hone : groupBasis (k := k) (1 : G) ∈
          Submodule.span k
            (groupBasis (k := k) '' (↑(insert 1 S) : Set G)) :=
        Submodule.subset_span
          ⟨1, Finset.mem_insert_self (1 : G) S, rfl⟩
      simpa [groupBasis, ← MonoidAlgebra.one_def] using hone
    have hmono : actionExpansion F E ≤
        actionSubspace (groupActingSubcoalgebra (k := k) S).carrier E := by
      rw [actionExpansion, sup_le_iff]
      constructor
      · intro x hx
        simpa using product_mem_actionSubspace h1act hx
      · exact actionSubspace_mono_left (hFS.trans hspanLe) E
    have hdim : (sfinrank k (actionExpansion F E) : ℚ) ≤
        sfinrank k
          (actionSubspace (groupActingSubcoalgebra (k := k) S).carrier E) := by
      exact_mod_cast Submodule.finrank_mono hmono
    exact ⟨E, hE, hEfd, hdim.trans hEfolner⟩
  have hXcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := MonoidAlgebra k G) (M := MonoidAlgebra k X) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra hXaction
  let q : MonoidAlgebra k X →ₗc[k] MonoidAlgebra k Y :=
    pointMapCoalgHom (k := k) f
  have hq : IsHopfModuleMap (H := MonoidAlgebra k G) q.toLinearMap := by
    intro a m
    induction a using MonoidAlgebra.induction_on with
    | of g =>
        let lhs : MonoidAlgebra k X →ₗ[k] MonoidAlgebra k Y :=
          q.toLinearMap.comp
            (Algebra.lsmul k k (MonoidAlgebra k X) (MonoidAlgebra.of k G g))
        let rhs : MonoidAlgebra k X →ₗ[k] MonoidAlgebra k Y :=
          (Algebra.lsmul k k (MonoidAlgebra k Y) (MonoidAlgebra.of k G g)).comp
            q.toLinearMap
        have hlr : lhs = rhs := by
          ext x : 2
          simp [lhs, rhs, q, pointMapCoalgHom, group_single_smul_single, heq]
        exact DFunLike.congr_fun hlr m
    | add a b ha hb =>
        simpa only [add_smul, map_add] using congrArg₂ (· + ·) ha hb
    | smul c a ha =>
        simpa only [smul_assoc, map_smul] using congrArg (fun z => c • z) ha
  have hYcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := MonoidAlgebra k G) (M := MonoidAlgebra k Y) :=
    IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom q hq
      (pointMapCoalgHom_surjective (k := k) hf) hXcoal
  have hYaction := hYcoal.hasActionFolnerSubspaces
  apply HasGroupFolnerSubspaces.isAmenableGroupAction (k := k)
  intro S ε hε
  obtain ⟨E, hE, hEfd, hEfolner⟩ :=
    hYaction (groupActingSubcoalgebra (k := k) S).carrier inferInstance ε hε
  have h1act : (1 : MonoidAlgebra k G) ∈
      (groupActingSubcoalgebra (k := k) S).carrier := by
    rw [groupActingSubcoalgebra_carrier]
    have hone : groupBasis (k := k) (1 : G) ∈
        Submodule.span k
          (groupBasis (k := k) '' (↑(insert 1 S) : Set G)) :=
      Submodule.subset_span
        ⟨1, Finset.mem_insert_self (1 : G) S, rfl⟩
    simpa [groupBasis, ← MonoidAlgebra.one_def] using hone
  rw [actionExpansion_eq_actionSubspace_of_one_mem h1act] at hEfolner
  exact ⟨E, hE, hEfd, hEfolner⟩

end QuotientActions

section Orbits

variable {X : Type*} [MulAction G X]

/-- Amenability of the orbit of a point, expressed by the finite Følner
condition on the orbit subtype. -/
def IsAmenableOrbit (x : X) : Prop := by
  classical
  exact IsAmenableGroupAction (G := G) (X := MulAction.orbit G x)

end Orbits

section PermutationQuotient

variable {X : Type*} [MulAction G X]
variable [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

/-- The image of a permutation module is algebraically amenable as soon as
one basis point has nonzero image and amenable orbit. -/
theorem hasActionFolnerSubspaces_of_amenable_permutation_image
    (q : MonoidAlgebra k X →ₗ[k] V)
    (hq : ∀ (g : G) (x : X),
      q (pointBasis (k := k) (g • x)) =
        (MonoidAlgebra.single g (1 : k) : kG) •
          q (pointBasis (k := k) x))
    (x : X) (hqx : q (pointBasis (k := k) x) ≠ 0)
    (hx : IsAmenableOrbit (G := G) x) :
    HasActionFolnerSubspaces (k := k) (H := kG) (M := V) := by
  classical
  let : MulAction G V := groupActionOfModule (k := k) (G := G) (V := V)
  let v : V := q (pointBasis (k := k) x)
  let f : MulAction.orbit G x → MulAction.orbit G v := fun y => by
    refine ⟨q (pointBasis (k := k) (y : X)), ?_⟩
    rcases MulAction.mem_orbit_iff.1 y.2 with ⟨g, hg⟩
    apply MulAction.mem_orbit_iff.2
    refine ⟨g, ?_⟩
    change (MonoidAlgebra.single g (1 : k) : kG) •
        q (pointBasis (k := k) x) = q (pointBasis (k := k) (y : X))
    rw [← hq, hg]
  have hf : Function.Surjective f := by
    intro y
    rcases MulAction.mem_orbit_iff.1 y.2 with ⟨g, hg⟩
    let z : MulAction.orbit G x := ⟨g • x, MulAction.mem_orbit x g⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    dsimp [f, z, v]
    calc
      q (pointBasis (k := k) (g • x)) =
          (MonoidAlgebra.single g (1 : k) : kG) •
            q (pointBasis (k := k) x) := hq g x
      _ = g • v := rfl
      _ = (y : V) := hg
  have heq : ∀ (g : G) (y : MulAction.orbit G x),
      f (g • y) = g • f y := by
    intro g y
    apply Subtype.ext
    exact hq g y
  have hvOrbit : IsAmenableGroupAction
      (G := G) (X := MulAction.orbit G v) :=
    IsAmenableGroupAction.of_surjective_equivariant k f hf heq hx
  intro F hF ε hε
  let : FiniteDimensional k F := hF
  obtain ⟨S, h1, hFS⟩ := exists_finiteGroupSpan_containing (k := k) F
  obtain ⟨A, hA, hAfolner⟩ := hvOrbit S ε hε
  let A' : Finset V := Finset.image
    (fun a : MulAction.orbit G v => (a : V)) A
  have hA' : A'.Nonempty := by
    dsimp [A']
    exact hA.image _
  have hA'card : A'.card = A.card := by
    dsimp [A']
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact Subtype.ext hab
  have hA'0 : ∀ a ∈ A', a ≠ 0 := by
    intro a ha
    rcases Finset.mem_image.1 ha with ⟨a₀, ha₀, rfl⟩
    rcases MulAction.mem_orbit_iff.1 a₀.2 with ⟨g, hg⟩
    rw [← hg]
    change (MonoidAlgebra.single g (1 : k) : kG) • v ≠ 0
    intro hzero
    have hinv := congrArg
      (fun z : V => (MonoidAlgebra.single g⁻¹ (1 : k) : kG) • z) hzero
    rw [smul_zero, ← mul_smul, MonoidAlgebra.single_mul_single] at hinv
    have hvzero : v = 0 := by
      simpa [← MonoidAlgebra.one_def] using hinv
    exact hqx hvzero
  have hexp : moduleGroupSetExpansion (k := k) S A' =
      Finset.image (fun a : MulAction.orbit G v => (a : V))
        (groupSetExpansion S A) := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.1 hy with ⟨⟨g, a⟩, hga, rfl⟩
      rcases Finset.mem_image.1 (Finset.mem_product.1 hga).2 with
        ⟨a₀, ha₀, rfl⟩
      apply Finset.mem_image.2
      refine ⟨g • a₀, ?_, ?_⟩
      · apply Finset.mem_image.2
        exact ⟨(g, a₀), Finset.mem_product.2
          ⟨Finset.mem_insert_of_mem (Finset.mem_product.1 hga).1, ha₀⟩, rfl⟩
      · rfl
    · intro hy
      rcases Finset.mem_image.1 hy with ⟨b, hb, rfl⟩
      rcases Finset.mem_image.1 hb with ⟨⟨g, a⟩, hga, rfl⟩
      have hg : g ∈ S := by
        rcases Finset.mem_insert.1 (Finset.mem_product.1 hga).1 with h | h
        · have hg1 : g = 1 := by simpa using h
          rw [hg1]
          exact h1
        · exact h
      apply Finset.mem_image.2
      refine ⟨(g, (a : V)), Finset.mem_product.2 ⟨hg, ?_⟩, ?_⟩
      · exact Finset.mem_image.2 ⟨a, (Finset.mem_product.1 hga).2, rfl⟩
      · rfl
  have hexpCard : (moduleGroupSetExpansion (k := k) S A').card =
      (groupSetExpansion S A).card := by
    rw [hexp, Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact Subtype.ext hab
  obtain ⟨E, hE, hEfd, hratio⟩ :=
    exists_submodule_ratio_le_of_finite_configuration
      (k := k) S h1 A' hA' hA'0
  let : FiniteDimensional k E := hEfd
  have hEpos : (0 : ℚ) < finrank k E := by
    let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hcardRatio :
      ((moduleGroupSetExpansion (k := k) S A').card : ℚ) / A'.card ≤
        1 + ε := by
    rw [hexpCard, hA'card]
    have hApos : (0 : ℚ) < A.card := by
      exact_mod_cast Finset.card_pos.2 hA
    exact (div_le_iff₀ hApos).2 hAfolner
  have hratio' :
      (sfinrank k
          (actionSubspace (finiteGroupSpan (k := k) S).carrier E) : ℚ) ≤
        (1 + ε) * finrank k E :=
    (div_le_iff₀ hEpos).1 (hratio.trans hcardRatio)
  have hmono : actionExpansion F E ≤
      actionSubspace (finiteGroupSpan (k := k) S).carrier E := by
    rw [actionExpansion, sup_le_iff]
    constructor
    · intro e he
      have hOne : (1 : kG) ∈ (finiteGroupSpan (k := k) S).carrier := by
        rw [finiteGroupSpan_carrier]
        have hone : groupBasis (k := k) (1 : G) ∈
            Submodule.span k (groupBasis (k := k) '' (S : Set G)) :=
          Submodule.subset_span ⟨1, h1, rfl⟩
        simpa [groupBasis, ← MonoidAlgebra.one_def] using hone
      simpa using product_mem_actionSubspace hOne he
    · exact actionSubspace_mono_left hFS E
  have hdim : (sfinrank k (actionExpansion F E) : ℚ) ≤
      sfinrank k
        (actionSubspace (finiteGroupSpan (k := k) S).carrier E) := by
    exact_mod_cast Submodule.finrank_mono hmono
  exact ⟨E, hE, inferInstance, hdim.trans hratio'⟩

end PermutationQuotient

section AmenableGroup

/-- The finite Følner-set definition of amenability of a group, using its
left regular action. -/
def IsAmenableGroup : Prop := by
  classical
  exact IsAmenableGroupAction (G := G) (X := G)

variable [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

end AmenableGroup

end

end HopfAmenability

