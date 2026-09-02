/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfAmenability
import Amenability.TensorContraction
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Rounding and amenability for group actions

This is the opt-in specialization of coalgebraic rounding to the diagonal
coalgebra on the linearization of a group action.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {G : Type v} {X : Type w}
variable [Field k] [Group G] [MulAction G X]

local notation "kG" => MonoidAlgebra k G
local notation "kX" => MonoidAlgebra k X

/-- The permutation representation associated to the action of G on X. -/
noncomputable def groupActionRepresentation : Representation k G kX :=
  Representation.ofMulAction k G X

/-- The induced module structure over the group algebra. -/
@[instance_reducible]
noncomputable def groupAlgebraModule : Module kG kX :=
  Module.compHom kX
    (groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom.toRingHom

noncomputable local instance : Module kG kX := groupAlgebraModule

noncomputable local instance : IsScalarTower k kG kX :=
  IsScalarTower.of_algebraMap_smul (fun r m => by
    change (groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom
      (algebraMap k kG r) m = r • m
    rw [(groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom.commutes]
    rfl)

@[simp]
theorem group_single_smul_single (g : G) (x : X) (a b : k) :
    MonoidAlgebra.single g a • MonoidAlgebra.single x b =
      MonoidAlgebra.single (g • x) (a * b) := by
  change (groupActionRepresentation (k := k) (G := G) (X := X)).asAlgebraHom
    (MonoidAlgebra.single g a) (MonoidAlgebra.single x b) = _
  rw [Representation.asAlgebraHom_single]
  simp [groupActionRepresentation, Representation.ofMulAction_single]

noncomputable local instance : IsHopfModuleCoalgebra k kG kX where
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
      TensorProduct.comul_tmul]

/-- The standard group-like basis vector in the group algebra. -/
def groupBasis (g : G) : kG :=
  MonoidAlgebra.single g 1

/-- The finite subcoalgebra spanned by the identity and a finite set of group
elements. -/
noncomputable def groupActingSubcoalgebra [DecidableEq G] (S : Finset G) :
    FiniteSubcoalgebra k kG := by
  exact {
  carrier := Submodule.span k
    (Set.range (fun g : (↑(insert 1 S) : Set G) => groupBasis (k := k) g))
  isSubcoalgebra := by
    let P : Submodule k kG := Submodule.span k
      (Set.range (fun g : (↑(insert 1 S) : Set G) => groupBasis (k := k) g))
    let stable : Submodule k kG :=
      (LinearMap.range (TensorProduct.mapIncl P P)).comap Coalgebra.comul
    change P ≤ stable
    apply Submodule.span_le.2
    rintro _ ⟨g, rfl⟩
    let gp : P := ⟨groupBasis (k := k) g,
      Submodule.subset_span ⟨g, rfl⟩⟩
    refine ⟨gp ⊗ₜ[k] gp, ?_⟩
    dsimp [TensorProduct.mapIncl, gp]
    simp [groupBasis]
  finiteDimensional := by
    apply FiniteDimensional.span_of_finite
    exact Set.finite_range _ }

theorem finrank_groupActingSubcoalgebra [DecidableEq G] (S : Finset G) :
    finrank k (groupActingSubcoalgebra (k := k) S).carrier =
      (insert 1 S).card := by
  classical
  have hcarrier :
      (groupActingSubcoalgebra (k := k) S).carrier =
        Submodule.span k
          (Set.range (fun g : (↑(insert 1 S) : Set G) =>
            groupBasis (k := k) (g : G))) := by
    rfl
  rw [hcarrier]
  rw [finrank_span_eq_card]
  · simp
  · exact (MonoidAlgebra.basis G k).linearIndependent.comp
      (fun g : (↑(insert 1 S) : Set G) => g.1) Subtype.val_injective

/-- The standard group-like basis vector of the diagonal coalgebra on X. -/
def pointBasis (x : X) : kX :=
  MonoidAlgebra.single x 1

/-- The coordinate functional at x. -/
def pointCoordinate (x : X) : kX →ₗ[k] k :=
  Finsupp.lapply x ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem pointCoordinate_pointBasis [DecidableEq X] (x y : X) :
    pointCoordinate (k := k) x (pointBasis (k := k) y) = if x = y then 1 else 0 := by
  change (MonoidAlgebra.single y (1 : k)).coeff x = _
  by_cases h : x = y
  · subst y
    simp
  · simp [h]

/-- Contracting one leg of the diagonal comultiplication extracts one
coordinate basis vector. -/
theorem leftContract_comul_point (x : X) (c : kX) :
    TensorProduct.leftContract (pointCoordinate (k := k) x)
        (Coalgebra.comul (R := k) c) =
      c.coeff x • pointBasis (k := k) x := by
  classical
  let lhs : kX →ₗ[k] kX :=
    TensorProduct.leftContract (pointCoordinate (k := k) x) ∘ₗ
      Coalgebra.comul (R := k)
  let rhs : kX →ₗ[k] kX :=
    LinearMap.id.smulRight (pointBasis (k := k) x) ∘ₗ
      pointCoordinate (k := k) x
  have hlr : lhs = rhs := by
    ext y : 1
    apply LinearMap.ext
    intro a
    by_cases h : x = y
    · subst y
      simp [lhs, rhs, pointCoordinate, pointBasis]
    · simp [lhs, rhs, pointCoordinate, pointBasis, h]
  change lhs c = _
  rw [hlr]
  rfl

/-- Every basis vector occurring with nonzero coefficient in an element of a
subcoalgebra of the diagonal coalgebra belongs to that subcoalgebra. -/
theorem pointBasis_mem_of_coeff_ne_zero
    (C : FiniteSubcoalgebra k kX) (c : kX) (hc : c ∈ C.carrier)
    (x : X) (hx : c.coeff x ≠ 0) :
    pointBasis (k := k) x ∈ C.carrier := by
  classical
  obtain ⟨z, hz⟩ := C.isSubcoalgebra hc
  let f := pointCoordinate (k := k) x
  let d : C.carrier :=
    TensorProduct.leftContract (f.comp C.carrier.subtype) z
  have hd : (d : kX) = c.coeff x • pointBasis (k := k) x := by
    calc
      (d : kX) =
          TensorProduct.leftContract f
            (TensorProduct.mapIncl C.carrier C.carrier z) := by
        exact (TensorProduct.leftContract_mapIncl f C.carrier C.carrier z).symm
      _ = TensorProduct.leftContract f (Coalgebra.comul (R := k) c) := by
        rw [hz]
      _ = c.coeff x • pointBasis (k := k) x :=
        leftContract_comul_point x c
  have hrecover :
      pointBasis (k := k) x = (c.coeff x)⁻¹ • (d : kX) := by
    rw [hd, smul_smul, inv_mul_cancel₀ hx, one_smul]
  rw [hrecover]
  exact C.carrier.smul_mem _ d.2

/-- The set of diagonal basis points contained in a finite subcoalgebra. -/
def subcoalgebraPoints (C : FiniteSubcoalgebra k kX) : Set X :=
  {x | pointBasis (k := k) x ∈ C.carrier}

/-- A finite subcoalgebra of the diagonal coalgebra is exactly the span of a
finite set of basis vectors. -/
theorem exists_finset_eq_carrier (C : FiniteSubcoalgebra k kX) :
    ∃ A : Finset X,
      C.carrier =
        Submodule.span k (pointBasis (k := k) '' (A : Set X)) ∧
      finrank k C.carrier = A.card := by
  classical
  let P : Set X := subcoalgebraPoints (k := k) C
  have hambient :
      LinearIndependent k (fun x : P => pointBasis (k := k) (x : X)) := by
    exact (MonoidAlgebra.basis X k).linearIndependent.comp
      (fun x : P => x.1) Subtype.val_injective
  have hsub :
      LinearIndependent k
        (fun x : P => (⟨pointBasis (k := k) (x : X), x.2⟩ : C.carrier)) := by
    exact LinearIndependent.of_comp C.carrier.subtype hambient
  let : Finite P := hsub.finite
  let : Fintype P := Fintype.ofFinite P
  have hPfinite : P.Finite := Set.toFinite P
  let A : Finset X := hPfinite.toFinset
  have hAP : (A : Set X) = P := by
    exact hPfinite.coe_toFinset
  have hCP :
      C.carrier = Submodule.span k (pointBasis (k := k) '' P) := by
    apply le_antisymm
    · intro c hc
      change c ∈ Submodule.span k
        ((fun x : X => MonoidAlgebra.single x (1 : k)) '' P)
      rw [← MonoidAlgebra.supported_eq_span_single]
      rw [MonoidAlgebra.mem_supported]
      intro x hx
      change pointBasis (k := k) x ∈ C.carrier
      exact pointBasis_mem_of_coeff_ne_zero C c hc x
        (Finsupp.mem_support_iff.mp hx)
    · apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact hx
  refine ⟨A, ?_, ?_⟩
  · rw [hAP]
    exact hCP
  · have himage :
        pointBasis (k := k) '' P =
          Set.range (fun x : P => pointBasis (k := k) (x : X)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
    rw [hCP, himage, finrank_span_eq_card hambient]
    exact hPfinite.card_toFinset.symm

/-- The span in kX of a finite set of points. -/
def pointSpan (A : Finset X) : Submodule k kX :=
  Submodule.span k (pointBasis (k := k) '' (A : Set X))

/-- Expansion of a finite subset of X by the identity and a finite subset of G. -/
def groupSetExpansion [DecidableEq G] [DecidableEq X]
    (S : Finset G) (A : Finset X) : Finset X :=
  ((insert 1 S).product A).image fun p => p.1 • p.2

theorem groupActingSubcoalgebra_carrier [DecidableEq G] (S : Finset G) :
    (groupActingSubcoalgebra (k := k) S).carrier =
      Submodule.span k (groupBasis (k := k) '' (↑(insert 1 S) : Set G)) := by
  change Submodule.span k
      (Set.range (fun g : (↑(insert 1 S) : Set G) =>
        groupBasis (k := k) (g : G))) = _
  congr 1
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem finrank_pointSpan (A : Finset X) :
    finrank k (pointSpan (k := k) A) = A.card := by
  classical
  change finrank k (Submodule.span k
      (pointBasis (k := k) '' (A : Set X))) = A.card
  have himage :
      pointBasis (k := k) '' (A : Set X) =
        Set.range (fun x : (A : Set X) => pointBasis (k := k) (x : X)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [himage, finrank_span_eq_card]
  · simp
  · exact (MonoidAlgebra.basis X k).linearIndependent.comp
      (fun x : (A : Set X) => x.1) Subtype.val_injective

/-- Acting on the span of a finite set produces the span of its set-theoretic
expansion. -/
theorem actionSubspace_groupActing_pointSpan
    [DecidableEq G] [DecidableEq X] (S : Finset G) (A : Finset X) :
    actionSubspace (groupActingSubcoalgebra (k := k) S).carrier
        (pointSpan (k := k) A) =
      pointSpan (k := k) (groupSetExpansion S A) := by
  rw [actionSubspace_eq_map₂, groupActingSubcoalgebra_carrier]
  change Submodule.map₂ (Algebra.lsmul k k kX).toLinearMap
      (Submodule.span k (groupBasis (k := k) '' (↑(insert 1 S) : Set G)))
      (Submodule.span k (pointBasis (k := k) '' (A : Set X))) = _
  rw [Submodule.map₂_span_span]
  apply congrArg (Submodule.span k)
  ext y
  constructor
  · rintro ⟨h, ⟨g, hg, rfl⟩, x, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨g • a, ?_, ?_⟩
    · change g • a ∈ ((insert 1 S).product A).image (fun p => p.1 • p.2)
      rw [Finset.mem_image]
      exact ⟨(g, a), Finset.mem_product.2 ⟨hg, ha⟩, rfl⟩
    · simp [groupBasis, pointBasis, group_single_smul_single]
  · rintro ⟨x, hx, rfl⟩
    change x ∈ ((insert 1 S).product A).image (fun p => p.1 • p.2) at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨⟨g, a⟩, hga, rfl⟩
    have hg : g ∈ insert 1 S := (Finset.mem_product.mp hga).1
    have ha : a ∈ A := (Finset.mem_product.mp hga).2
    refine ⟨groupBasis (k := k) g, ⟨g, hg, rfl⟩,
      pointBasis (k := k) a, ⟨a, ha, rfl⟩, ?_⟩
    simp [groupBasis, pointBasis, group_single_smul_single]

theorem finrank_actionSubspace_groupActing_pointSpan
    [DecidableEq G] [DecidableEq X] (S : Finset G) (A : Finset X) :
    finrank k (actionSubspace
        (groupActingSubcoalgebra (k := k) S).carrier
        (pointSpan (k := k) A)) =
      (groupSetExpansion S A).card := by
  rw [actionSubspace_groupActing_pointSpan, finrank_pointSpan]

/-- Coalgebraic rounding specialized to a finite subset of a group acting on
a set: a nonzero finite-dimensional subspace rounds to a nonempty finite
subset with no larger expansion ratio. -/
theorem exists_finset_group_ratio_le
    [DecidableEq G] [DecidableEq X]
    (S : Finset G) (E : Submodule k kX)
    [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ A : Finset X,
      A.Nonempty ∧
        ((groupSetExpansion S A).card : ℚ) / A.card ≤
          (sfinrank k
              (actionSubspace
                (groupActingSubcoalgebra (k := k) S).carrier E) : ℚ) /
            finrank k E := by
  classical
  obtain ⟨C, hC, hratio⟩ :=
    exists_finiteSubcoalgebra_action_ratio_le
      (groupActingSubcoalgebra (k := k) S) E hE
  obtain ⟨A, hCA, hdim⟩ := exists_finset_eq_carrier C
  have hCA' : C.carrier = pointSpan (k := k) A := by
    exact hCA
  have hA : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hC
    rw [hCA', h]
    simp [pointSpan]
  refine ⟨A, hA, ?_⟩
  simp only [sfinrank] at hratio
  rw [hCA', finrank_actionSubspace_groupActing_pointSpan,
    finrank_pointSpan] at hratio
  exact hratio

/-- The finite-set Følner condition for the G-set X. -/
def IsAmenableGroupAction [DecidableEq G] [DecidableEq X] : Prop :=
  ∀ (S : Finset G) (ε : ℚ), 0 < ε →
    ∃ A : Finset X,
      A.Nonempty ∧
        ((groupSetExpansion S A).card : ℚ) ≤ (1 + ε) * A.card

/-- The finite-dimensional Følner condition for the linearized action on kX. -/
def HasGroupFolnerSubspaces [DecidableEq G] : Prop :=
  ∀ (S : Finset G) (ε : ℚ), 0 < ε →
    ∃ E : Submodule k kX,
      E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k
            (actionSubspace
              (groupActingSubcoalgebra (k := k) S).carrier E) : ℚ) ≤
          (1 + ε) * sfinrank k E

/-- Følner subspaces round to Følner finite subsets with the same constant. -/
theorem HasGroupFolnerSubspaces.isAmenableGroupAction
    [DecidableEq G] [DecidableEq X]
    (hM : HasGroupFolnerSubspaces (k := k) (G := G) (X := X)) :
    IsAmenableGroupAction (G := G) (X := X) := by
  intro S ε hε
  obtain ⟨E, hE, hEfd, hFolner⟩ := hM S ε hε
  let : FiniteDimensional k E := hEfd
  obtain ⟨A, hA, hratio⟩ := exists_finset_group_ratio_le S E hE
  refine ⟨A, hA, ?_⟩
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  have hEpos : (0 : ℚ) < finrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hApos : (0 : ℚ) < A.card := by
    exact_mod_cast A.card_pos.mpr hA
  have hsource :
      (sfinrank k
          (actionSubspace
            (groupActingSubcoalgebra (k := k) S).carrier E) : ℚ) /
          finrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).mpr hFolner
  exact (div_le_iff₀ hApos).mp (hratio.trans hsource)

/-- A finite Følner subset spans a finite-dimensional Følner subspace. -/
theorem IsAmenableGroupAction.hasFolnerSubspaces
    [DecidableEq G] [DecidableEq X]
    (hX : IsAmenableGroupAction (G := G) (X := X)) :
    HasGroupFolnerSubspaces (k := k) (G := G) (X := X) := by
  intro S ε hε
  obtain ⟨A, hA, hFolner⟩ := hX S ε hε
  let E : Submodule k kX := pointSpan (k := k) A
  let : FiniteDimensional k E := by
    dsimp [E, pointSpan]
    exact FiniteDimensional.span_of_finite k (A.finite_toSet.image _)
  have hE : E ≠ ⊥ := by
    intro hbot
    have hzero : finrank k E = 0 := by rw [hbot]; simp
    rw [finrank_pointSpan] at hzero
    exact (A.card_pos.mpr hA).ne' hzero
  refine ⟨E, hE, inferInstance, ?_⟩
  change (sfinrank k
      (actionSubspace (groupActingSubcoalgebra (k := k) S).carrier
        (pointSpan (k := k) A)) : ℚ) ≤
    (1 + ε) * sfinrank k (pointSpan (k := k) A)
  simpa only [sfinrank, finrank_actionSubspace_groupActing_pointSpan,
    finrank_pointSpan] using hFolner

/-- The finite-set and linearized Følner conditions for a group action are
equivalent. -/
theorem isAmenableGroupAction_iff_hasFolnerSubspaces
    [DecidableEq G] [DecidableEq X] :
    IsAmenableGroupAction (G := G) (X := X) ↔
      HasGroupFolnerSubspaces (k := k) (G := G) (X := X) :=
  ⟨IsAmenableGroupAction.hasFolnerSubspaces,
    HasGroupFolnerSubspaces.isAmenableGroupAction⟩

/-- Every finite-dimensional subspace of a group algebra is contained in
one of the standard finite-dimensional acting subcoalgebras. -/
theorem exists_groupActingSubcoalgebra_containing
    [DecidableEq G]
    (F : Submodule k kG) [FiniteDimensional k F] :
    ∃ S : Finset G, F ≤ (groupActingSubcoalgebra (k := k) S).carrier := by
  classical
  let e := Module.finBasis k F
  let S : Finset G :=
    Finset.univ.biUnion fun i => ((e i : kG).coeff.support)
  refine ⟨S, ?_⟩
  intro x hx
  let xF : F := ⟨x, hx⟩
  have hxsum : x = ∑ i, (e.repr xF) i • (e i : kG) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      (congrArg Subtype.val (e.sum_repr xF)).symm
  rw [hxsum, groupActingSubcoalgebra_carrier]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  change (e i : kG) ∈ Submodule.span k
    ((fun g : G => MonoidAlgebra.single g (1 : k)) ''
      (↑(insert 1 S) : Set G))
  rw [← MonoidAlgebra.supported_eq_span_single, MonoidAlgebra.mem_supported]
  intro g hg
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hg⟩)

/-- A `G`-set is amenable exactly when its diagonal coalgebra is amenable as
a module coalgebra over the group Hopf algebra. -/
theorem isAmenableGroupAction_iff_isAmenableHopfModuleCoalgebra
    [DecidableEq G] [DecidableEq X] :
    IsAmenableGroupAction (G := G) (X := X) ↔
      IsAmenableHopfModuleCoalgebra (k := k) (H := kG) (M := kX) := by
  constructor
  · intro hX
    apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
    intro F hF ε hε
    let _ : FiniteDimensional k F := hF
    obtain ⟨S, hFS⟩ := exists_groupActingSubcoalgebra_containing
      (k := k) F
    obtain ⟨E, hE, hEfd, hratio⟩ :=
      hX.hasFolnerSubspaces (k := k) S ε hε
    have hmono : actionExpansion F E ≤
        actionSubspace (groupActingSubcoalgebra (k := k) S).carrier E := by
      rw [actionExpansion, sup_le_iff]
      constructor
      · intro e he
        have hOne : (1 : kG) ∈
            (groupActingSubcoalgebra (k := k) S).carrier := by
          rw [groupActingSubcoalgebra_carrier]
          have hone : groupBasis (k := k) (1 : G) ∈
              Submodule.span k
                (groupBasis (k := k) '' (↑(insert 1 S) : Set G)) :=
            Submodule.subset_span
              ⟨1, Finset.mem_insert_self (1 : G) S, rfl⟩
          simpa [groupBasis, ← MonoidAlgebra.one_def] using hone
        simpa using product_mem_actionSubspace hOne he
      · exact actionSubspace_mono_left hFS E
    have hdim : (sfinrank k (actionExpansion F E) : ℚ) ≤
        sfinrank k
          (actionSubspace (groupActingSubcoalgebra (k := k) S).carrier E) := by
      exact_mod_cast Submodule.finrank_mono hmono
    exact ⟨E, hE, hEfd, hdim.trans hratio⟩
  · intro hX
    apply HasGroupFolnerSubspaces.isAmenableGroupAction (k := k)
    intro S ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := hX.hasActionFolnerSubspaces
      (groupActingSubcoalgebra (k := k) S).carrier inferInstance ε hε
    have hOne : (1 : kG) ∈
        (groupActingSubcoalgebra (k := k) S).carrier := by
      rw [groupActingSubcoalgebra_carrier]
      have hone : groupBasis (k := k) (1 : G) ∈
          Submodule.span k
            (groupBasis (k := k) '' (↑(insert 1 S) : Set G)) :=
        Submodule.subset_span
          ⟨1, Finset.mem_insert_self (1 : G) S, rfl⟩
      simpa [groupBasis, ← MonoidAlgebra.one_def] using hone
    rw [actionExpansion_eq_actionSubspace_of_one_mem hOne] at hratio
    exact ⟨E, hE, hEfd, hratio⟩

end

end HopfAmenability
