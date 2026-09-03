/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AugmentationGradedHopfModuleCoalgebra
import Amenability.HopfActionSubspace
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! # Initial subspaces for separated descending filtrations -/

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

local instance filtrationGradedAddCommGroup (W : ℕ → Submodule k V) :
    AddCommGroup (FiltrationGraded W) :=
  inferInstanceAs (AddCommGroup (Π₀ n, FiltrationPiece W n))

/-- A finite-dimensional subspace meets a separated descending filtration
trivially from some stage onward. -/
theorem exists_inf_filtration_eq_bot
    (W : ℕ → Submodule k V) (hW : Antitone W) (hsep : ⨅ n, W n = ⊥)
    (E : Submodule k V) [FiniteDimensional k E] :
    ∃ N : ℕ, (W N).comap E.subtype = ⊥ := by
  let chain : ℕ →o (Submodule k E)ᵒᵈ :=
    OrderHom.mk (fun n => OrderDual.toDual ((W n).comap E.subtype)) (by
      intro i j hij
      exact Submodule.comap_mono (hW hij))
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes chain
  refine ⟨N, bot_unique ?_⟩
  intro x hx
  have hxall : ∀ n, (x : V) ∈ W n := by
    intro n
    by_cases hn : N ≤ n
    · have heq : (W N).comap E.subtype = (W n).comap E.subtype := by
        exact congrArg OrderDual.ofDual (hN n hn)
      change x ∈ (W n).comap E.subtype
      rw [← heq]
      exact hx
    · exact hW (Nat.le_of_lt (Nat.lt_of_not_ge hn)) hx
  have hxinf : (x : V) ∈ ⨅ n, W n := (Submodule.mem_iInf _).2 hxall
  rw [hsep, Submodule.mem_bot] at hxinf
  exact Subtype.ext hxinf

/-- A finite-dimensional subspace whose intersection with the infinite
filtration is trivial already meets one finite filtration term trivially. -/
theorem exists_filtration_comap_eq_bot
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (E : Submodule k V) [FiniteDimensional k E]
    (hsep : (⨅ n, W n).comap E.subtype = ⊥) :
    ∃ N : ℕ, (W N).comap E.subtype = ⊥ := by
  let chain : ℕ →o (Submodule k E)ᵒᵈ :=
    OrderHom.mk (fun n => OrderDual.toDual ((W n).comap E.subtype)) (by
      intro i j hij
      exact Submodule.comap_mono (hW hij))
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes chain
  refine ⟨N, bot_unique ?_⟩
  intro x hx
  have hxall : ∀ n, x ∈ (W n).comap E.subtype := by
    intro n
    by_cases hn : N ≤ n
    · have heq : (W N).comap E.subtype = (W n).comap E.subtype := by
        exact congrArg OrderDual.ofDual (hN n hn)
      rwa [← heq]
    · exact Submodule.comap_mono
        (hW (Nat.le_of_lt (Nat.lt_of_not_ge hn))) hx
  have hxinf : x ∈ (⨅ n, W n).comap E.subtype := by
    rw [Submodule.comap_iInf]
    exact (Submodule.mem_iInf _).2 hxall
  rw [hsep, Submodule.mem_bot] at hxinf
  exact hxinf

/-- The filtration induced on a subspace. -/
def inducedFiltration (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    Submodule k E :=
  (W n).comap E.subtype

/-- The degree-`n` layer of the filtration induced on a subspace. -/
abbrev InducedFiltrationPiece (W : ℕ → Submodule k V)
    (E : Submodule k V) (n : ℕ) :=
  inducedFiltration W E n ⧸
    (inducedFiltration W E (n + 1)).comap (inducedFiltration W E n).subtype

private def inducedFiltrationInclusion
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    inducedFiltration W E n →ₗ[k] W n where
  toFun x := ⟨x.1.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem inducedFiltrationInclusion_maps_next
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    (inducedFiltration W E (n + 1)).comap
        (inducedFiltration W E n).subtype ≤
      ((W (n + 1)).comap (W n).subtype).comap
        (inducedFiltrationInclusion (k := k) W E n) := by
  intro x hx
  exact hx

/-- The canonical injection of an induced filtration layer into the
corresponding ambient filtration layer. -/
def inducedFiltrationPieceMap
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    InducedFiltrationPiece W E n →ₗ[k] FiltrationPiece W n :=
  Submodule.mapQ _ _ (inducedFiltrationInclusion (k := k) W E n)
    (inducedFiltrationInclusion_maps_next (k := k) W E n)

@[simp]
theorem inducedFiltrationPieceMap_mk
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ)
    (x : inducedFiltration W E n) :
    inducedFiltrationPieceMap (k := k) W E n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x.1.1, x.2⟩ : W n) :=
  rfl

theorem inducedFiltrationPieceMap_injective
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    Function.Injective (inducedFiltrationPieceMap (k := k) W E n) := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          rw [inducedFiltrationPieceMap_mk,
            inducedFiltrationPieceMap_mk] at hxy
          rw [Submodule.Quotient.eq]
          rw [Submodule.Quotient.eq] at hxy
          exact hxy

/-- Include one induced layer as a homogeneous subspace of the ambient
associated graded. -/
def inducedFiltrationLayerMap
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    InducedFiltrationPiece W E n →ₗ[k] FiltrationGraded W :=
  (DirectSum.lof k ℕ (fun r => FiltrationPiece W r) n).comp
    (inducedFiltrationPieceMap (k := k) W E n)

theorem inducedFiltrationLayerMap_injective
    (W : ℕ → Submodule k V) (E : Submodule k V) (n : ℕ) :
    Function.Injective (inducedFiltrationLayerMap (k := k) W E n) := by
  intro x y hxy
  apply inducedFiltrationPieceMap_injective (k := k) W E n
  have hcomponent := congrArg
    (DirectSum.component k ℕ (fun r => FiltrationPiece W r) n) hxy
  simpa [inducedFiltrationLayerMap, LinearMap.comp_apply] using hcomponent

/-- The canonical initial-form subspace of `E` in the associated graded of
the ambient filtration. -/
def initialSubspace (W : ℕ → Submodule k V) (E : Submodule k V) :
    Submodule k (FiltrationGraded W) :=
  ⨆ n, LinearMap.range (inducedFiltrationLayerMap (k := k) W E n)

theorem initialSubspace_mono (W : ℕ → Submodule k V)
    {E E' : Submodule k V} (hEE' : E ≤ E') :
    initialSubspace (k := k) W E ≤ initialSubspace (k := k) W E' := by
  rw [initialSubspace, initialSubspace]
  apply iSup_le
  intro n
  rintro _ ⟨x, rfl⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      let x' : inducedFiltration W E' n :=
        ⟨⟨x.1.1, hEE' x.1.2⟩, x.2⟩
      apply le_iSup (fun r ↦ LinearMap.range
        (inducedFiltrationLayerMap (k := k) W E' r)) n
      refine ⟨Submodule.Quotient.mk x', ?_⟩
      rfl

/-- Replacing vectors by congruent vectors modulo the infinite filtration
can only enlarge their space of initial forms. -/
theorem initialSubspace_le_of_mod_iInf
    (W : ℕ → Submodule k V)
    {E E' : Submodule k V}
    (h : ∀ x ∈ E, ∃ y ∈ E', x - y ∈ ⨅ n, W n) :
    initialSubspace (k := k) W E ≤ initialSubspace (k := k) W E' := by
  rw [initialSubspace, initialSubspace]
  apply iSup_le
  intro n
  rintro _ ⟨q, rfl⟩
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      obtain ⟨y, hyE, hxy⟩ := h x.1.1 x.1.2
      have hxyN : x.1.1 - y ∈ W n := (Submodule.mem_iInf _).1 hxy n
      have hyN : y ∈ W n := by
        have := (W n).sub_mem x.2 hxyN
        simpa [sub_sub_cancel] using this
      let yN : inducedFiltration W E' n := ⟨⟨y, hyE⟩, hyN⟩
      apply le_iSup (fun r ↦ LinearMap.range
        (inducedFiltrationLayerMap (k := k) W E' r)) n
      refine ⟨Submodule.Quotient.mk yN, ?_⟩
      apply congrArg (DirectSum.of (fun r ↦ FiltrationPiece W r) n)
      rw [inducedFiltrationPieceMap_mk, inducedFiltrationPieceMap_mk]
      rw [Submodule.Quotient.eq]
      change y - x.1.1 ∈ W (n + 1)
      simpa only [neg_sub] using
        (W (n + 1)).neg_mem ((Submodule.mem_iInf _).1 hxy (n + 1))

/-- A linear choice of representative for the `n`th filtration quotient. -/
def filtrationPieceSection (W : ℕ → Submodule k V) (n : ℕ) :
    FiltrationPiece W n →ₗ[k] W n :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective
    ((W (n + 1)).comap (W n).subtype).mkQ
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)))

@[simp]
theorem filtrationPiece_mk_section (W : ℕ → Submodule k V) (n : ℕ)
    (x : FiltrationPiece W n) :
    Submodule.Quotient.mk (filtrationPieceSection (k := k) W n x) = x :=
  LinearMap.congr_fun
    (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective
      ((W (n + 1)).comap (W n).subtype).mkQ
      (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)))) x

/-- A simultaneous linear choice of filtered representatives of all
homogeneous elements of an associated graded vector space. -/
def filtrationGradedLift (W : ℕ → Submodule k V) :
    FiltrationGraded W →ₗ[k] V :=
  DirectSum.toModule k ℕ V fun n ↦
    (W n).subtype.comp (filtrationPieceSection (k := k) W n)

/-- Lift just one homogeneous coordinate of an associated-graded vector. -/
def filtrationGradedComponentLift (W : ℕ → Submodule k V) (n : ℕ) :
    FiltrationGraded W →ₗ[k] V :=
  ((W n).subtype.comp (filtrationPieceSection (k := k) W n)).comp
    (DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) n)

/-- The coefficient space obtained by lifting every homogeneous coordinate
of a graded coefficient space. -/
def liftHomogeneousSubspace (W : ℕ → Submodule k V)
    (F : Submodule k (FiltrationGraded W)) : Submodule k V :=
  ⨆ n, Submodule.map (filtrationGradedComponentLift (k := k) W n) F

theorem exists_finset_directSum_support
    (W : ℕ → Submodule k V) (F : Submodule k (FiltrationGraded W))
    [FiniteDimensional k F] :
    ∃ s : Finset ℕ, ∀ x ∈ F, ∀ n, n ∉ s →
      DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) n x = 0 := by
  classical
  let b := Module.finBasis k F
  let s : Finset ℕ := Finset.univ.biUnion fun i ↦ (b i : FiltrationGraded W).support
  refine ⟨s, ?_⟩
  intro x hx n hn
  let xF : F := ⟨x, hx⟩
  have hxsum : ∑ i, (b.repr xF i) • (b i : FiltrationGraded W) = x := by
    have h := congrArg F.subtype (b.sum_repr xF)
    rw [map_sum] at h
    simpa using h
  rw [← hxsum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  apply smul_eq_zero_of_right
  apply DFinsupp.notMem_support_iff.mp
  intro hmem
  apply hn
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩

theorem finiteDimensional_liftHomogeneousSubspace
    (W : ℕ → Submodule k V) (F : Submodule k (FiltrationGraded W))
    [FiniteDimensional k F] :
    FiniteDimensional k (liftHomogeneousSubspace (k := k) W F) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_directSum_support (k := k) W F
  let B : Submodule k V := ⨆ n : s,
    Submodule.map (filtrationGradedComponentLift (k := k) W n) F
  have hfinite : FiniteDimensional k B := by
    dsimp [B]
    infer_instance
  apply FiniteDimensional.of_injective
    (Submodule.inclusion (show liftHomogeneousSubspace (k := k) W F ≤ B by
      rw [liftHomogeneousSubspace]
      apply iSup_le
      intro n
      by_cases hn : n ∈ s
      · exact le_iSup (fun i : s ↦
          Submodule.map (filtrationGradedComponentLift (k := k) W i) F) ⟨n, hn⟩
      · rintro _ ⟨x, hx, rfl⟩
        have hcomponent := hs x hx n hn
        change ((W n).subtype.comp (filtrationPieceSection (k := k) W n))
          (DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) n x) ∈ B
        rw [hcomponent, map_zero]
        exact Submodule.zero_mem B))
    (Submodule.inclusion_injective _)

@[simp]
theorem filtrationGradedLift_of (W : ℕ → Submodule k V) (n : ℕ)
    (x : FiltrationPiece W n) :
    filtrationGradedLift (k := k) W (DirectSum.of _ n x) =
      filtrationPieceSection (k := k) W n x := by
  change filtrationGradedLift (k := k) W
      (DirectSum.lof k ℕ (fun r ↦ FiltrationPiece W r) n x) = _
  rw [filtrationGradedLift, DirectSum.toModule_lof]
  rfl

@[simp]
theorem filtrationGradedLeading_lift_of (W : ℕ → Submodule k V)
    (n : ℕ) (x : FiltrationPiece W n) :
    filtrationGradedLeading (k := k) W n
        (filtrationGradedLift (k := k) W (DirectSum.of _ n x)) =
      DirectSum.of _ n x := by
  rw [filtrationGradedLift_of]
  exact (filtrationGradedLeading_apply (k := k) W n _).trans
    (congrArg (DirectSum.of (fun r ↦ FiltrationPiece W r) n)
      (filtrationPiece_mk_section (k := k) W n x))

/-- Dimensions of the successive induced quotients telescope. -/
theorem sum_finrank_inducedFiltrationPiece_add
    (W : ℕ → Submodule k V) (hW : Antitone W) (hzero : W 0 = ⊤)
    (E : Submodule k V) [FiniteDimensional k E] (N : ℕ) :
    (∑ n ∈ Finset.range N, Module.finrank k (InducedFiltrationPiece W E n)) +
        Module.finrank k (inducedFiltration W E N) =
      Module.finrank k E := by
  induction N with
  | zero =>
      rw [Finset.sum_range_zero, zero_add]
      change Module.finrank k ((W 0).comap E.subtype) = _
      rw [hzero]
      exact finrank_top k E
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hle : inducedFiltration W E (N + 1) ≤ inducedFiltration W E N :=
        Submodule.comap_mono (hW (Nat.le_succ N))
      have hequiv : Module.finrank k
          ((inducedFiltration W E (N + 1)).comap
            (inducedFiltration W E N).subtype) =
          Module.finrank k (inducedFiltration W E (N + 1)) :=
        (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
      have hquot := Submodule.finrank_quotient_add_finrank
        ((inducedFiltration W E (N + 1)).comap
          (inducedFiltration W E N).subtype)
      change Module.finrank k (InducedFiltrationPiece W E N) +
          Module.finrank k
            ((inducedFiltration W E (N + 1)).comap
              (inducedFiltration W E N).subtype) =
        Module.finrank k (inducedFiltration W E N) at hquot
      omega

/-- The direct sum of the first `N` induced layers, embedded in the ambient
associated graded. -/
def finiteInitialMap (W : ℕ → Submodule k V) (E : Submodule k V) (N : ℕ) :
    (DirectSum (Fin N) fun i ↦ InducedFiltrationPiece W E i) →ₗ[k]
      FiltrationGraded W :=
  DirectSum.toModule k (Fin N) (FiltrationGraded W) fun i ↦
    inducedFiltrationLayerMap (k := k) W E i

@[simp]
theorem finiteInitialMap_of (W : ℕ → Submodule k V)
    (E : Submodule k V) (N : ℕ) (i : Fin N)
    (x : InducedFiltrationPiece W E i) :
    finiteInitialMap (k := k) W E N (DirectSum.of _ i x) =
      inducedFiltrationLayerMap (k := k) W E i x := by
  change finiteInitialMap (k := k) W E N
      (DirectSum.lof k (Fin N)
        (fun j ↦ InducedFiltrationPiece W E j) i x) = _
  rw [finiteInitialMap, DirectSum.toModule_lof]

theorem finiteInitialMap_injective (W : ℕ → Submodule k V)
    (E : Submodule k V) (N : ℕ) :
    Function.Injective (finiteInitialMap (k := k) W E N) := by
  intro x y hxy
  apply DirectSum.ext_component k
  intro i
  apply inducedFiltrationPieceMap_injective (k := k) W E i
  have hcomponent := congrArg
    (DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) i) hxy
  have hformula (z : DirectSum (Fin N) fun j ↦
      InducedFiltrationPiece W E j) : DirectSum.component k ℕ
        (fun r ↦ FiltrationPiece W r) i
        (finiteInitialMap (k := k) W E N z) =
          inducedFiltrationPieceMap (k := k) W E i
            (DirectSum.component k (Fin N)
              (fun j ↦ InducedFiltrationPiece W E j) i z) := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j z =>
        by_cases hji : j = i
        · subst j
          rw [finiteInitialMap_of]
          change DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) i
              (DirectSum.lof k ℕ (fun r ↦ FiltrationPiece W r) i
                (inducedFiltrationPieceMap (k := k) W E i z)) =
            inducedFiltrationPieceMap (k := k) W E i
            (DirectSum.component k (Fin N)
              (fun j ↦ InducedFiltrationPiece W E j) i
              (DirectSum.lof k (Fin N)
                (fun j ↦ InducedFiltrationPiece W E j) i z))
          rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
        · have hval : (j : ℕ) ≠ (i : ℕ) := by
            intro h
            exact hji (Fin.ext h)
          rw [finiteInitialMap_of]
          change DirectSum.component k ℕ (fun r ↦ FiltrationPiece W r) i
              (DirectSum.lof k ℕ (fun r ↦ FiltrationPiece W r) j
                (inducedFiltrationPieceMap (k := k) W E j z)) =
            inducedFiltrationPieceMap (k := k) W E i
              (DirectSum.component k (Fin N)
                (fun l ↦ InducedFiltrationPiece W E l) i
                (DirectSum.lof k (Fin N)
                  (fun l ↦ InducedFiltrationPiece W E l) j z))
          have hleft : DirectSum.component k ℕ
              (fun r ↦ FiltrationPiece W r) i
              (DirectSum.lof k ℕ (fun r ↦ FiltrationPiece W r) j
                (inducedFiltrationPieceMap (k := k) W E j z)) = 0 := by
            rw [← LinearMap.comp_apply, DirectSum.component_comp_lof]
            simp [hval]
          have hcomp : DirectSum.component k (Fin N)
              (fun l ↦ InducedFiltrationPiece W E l) i
              (DirectSum.lof k (Fin N)
                (fun l ↦ InducedFiltrationPiece W E l) j z) = 0 := by
            rw [← LinearMap.comp_apply, DirectSum.component_comp_lof]
            simp [hji]
          rw [hleft, hcomp, map_zero]
    | add a b ha hb => simp [ha, hb]
  rw [hformula x, hformula y] at hcomponent
  exact hcomponent

theorem inducedFiltration_eq_bot_of_le
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (E : Submodule k V) {N n : ℕ}
    (hN : inducedFiltration W E N = ⊥) (hn : N ≤ n) :
    inducedFiltration W E n = ⊥ := by
  apply bot_unique
  exact (Submodule.comap_mono (hW hn)).trans_eq hN

/-- Once the induced filtration vanishes at `N`, the full initial subspace
is exactly the range of the sum of its first `N` homogeneous layers. -/
theorem initialSubspace_eq_range_finiteInitialMap
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (E : Submodule k V) (N : ℕ)
    (hN : inducedFiltration W E N = ⊥) :
    initialSubspace (k := k) W E =
      LinearMap.range (finiteInitialMap (k := k) W E N) := by
  apply le_antisymm
  · rw [initialSubspace]
    apply iSup_le
    intro n
    rintro _ ⟨x, rfl⟩
    by_cases hn : n < N
    · let i : Fin N := ⟨n, hn⟩
      refine ⟨DirectSum.of (fun j : Fin N ↦
          InducedFiltrationPiece W E j) i x, ?_⟩
      exact finiteInitialMap_of (k := k) W E N i x
    · have hbot : inducedFiltration W E n = ⊥ :=
        inducedFiltration_eq_bot_of_le W hW E hN (Nat.le_of_not_gt hn)
      have hx : x = 0 := by
        induction x using Submodule.Quotient.induction_on with
        | _ y =>
            have hy : y = 0 := by
              apply Subtype.ext
              exact hbot.le y.property
            subst y
            rfl
      rw [hx, map_zero]
      exact Submodule.zero_mem _
  · rintro _ ⟨x, rfl⟩
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
        rw [finiteInitialMap_of]
        exact le_iSup (fun n ↦ LinearMap.range
          (inducedFiltrationLayerMap (k := k) W E n)) i ⟨x, rfl⟩
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy

theorem finiteDimensional_initialSubspace
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (E : Submodule k V) [FiniteDimensional k E]
    (N : ℕ) (hN : inducedFiltration W E N = ⊥) :
    FiniteDimensional k (initialSubspace (k := k) W E) := by
  let _ (i : Fin N) : Module.Finite k (InducedFiltrationPiece W E i) := by
    let _ : Module.Finite k (inducedFiltration W E i) := inferInstance
    exact Module.Finite.quotient k _
  rw [initialSubspace_eq_range_finiteInitialMap W hW E N hN]
  infer_instance

/-- For a finite-dimensional subspace separated by the filtration, passing
to all its initial forms preserves dimension. -/
theorem finrank_initialSubspace
    (W : ℕ → Submodule k V) (hW : Antitone W) (hzero : W 0 = ⊤)
    (E : Submodule k V) [FiniteDimensional k E]
    (N : ℕ) (hN : inducedFiltration W E N = ⊥) :
    Module.finrank k (initialSubspace (k := k) W E) =
      Module.finrank k E := by
  let _ (i : Fin N) : Module.Finite k (InducedFiltrationPiece W E i) := by
    let _ : Module.Finite k (inducedFiltration W E i) := inferInstance
    exact Module.Finite.quotient k _
  let _ (i : Fin N) : Module.Free k (InducedFiltrationPiece W E i) :=
    Module.Free.of_divisionRing k _
  rw [initialSubspace_eq_range_finiteInitialMap W hW E N hN]
  rw [LinearMap.finrank_range_of_inj
    (finiteInitialMap_injective (k := k) W E N)]
  rw [Module.finrank_directSum]
  have htel := sum_finrank_inducedFiltrationPiece_add
    (k := k) W hW hzero E N
  rw [hN, finrank_bot, add_zero] at htel
  rw [← Fin.sum_univ_eq_sum_range] at htel
  exact htel

theorem initialSubspace_ne_bot
    (W : ℕ → Submodule k V) (hW : Antitone W) (hzero : W 0 = ⊤)
    (E : Submodule k V) [FiniteDimensional k E]
    (N : ℕ) (hN : inducedFiltration W E N = ⊥) (hE : E ≠ ⊥) :
    initialSubspace (k := k) W E ≠ ⊥ := by
  intro hbot
  have hdim := finrank_initialSubspace (k := k) W hW hzero E N hN
  rw [hbot] at hdim
  have hErank : Module.finrank k E = 0 := by simpa using hdim.symm
  apply hE
  rw [eq_bot_iff]
  intro x hx
  let _ : Subsingleton E :=
    (Module.finrank_eq_zero_iff_of_free k E).mp hErank
  exact congrArg E.subtype (show (⟨x, hx⟩ : E) = 0 from Subsingleton.elim _ _)

section AugmentationAction

universe w

variable {H : Type v} {M : Type w}
variable [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- Leading forms turn the action of a graded coefficient space on the
initial forms of `E` into the original action of homogeneous lifts on `E`. -/
theorem actionExpansion_initialSubspace_le
    (F : Submodule k (AugmentationGradedHopf (k := k) (H := H)))
    (E : Submodule k M) :
    actionExpansion F
        (initialSubspace (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := M)) E) ≤
      initialSubspace (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M))
        (actionExpansion
          (liftHomogeneousSubspace (k := k)
            (augmentationFiltration (k := k) (H := H)) F) E) := by
  apply sup_le
  · exact initialSubspace_mono _ le_sup_left
  · rw [actionSubspace_eq_map₂]
    apply Submodule.map₂_le.2
    intro f hf e he
    classical
    rw [← DirectSum.sum_support_of f]
    change ((Algebra.lsmul k k
      (AugmentationGradedModule (k := k) (H := H) (M := M))).toLinearMap
        (∑ i ∈ f.support, DirectSum.of _ i (f i))) e ∈ _
    rw [map_sum]
    simp only [LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i hi
    have hlift : filtrationGradedComponentLift (k := k)
        (augmentationFiltration (k := k) (H := H)) i f ∈
          liftHomogeneousSubspace (k := k)
            (augmentationFiltration (k := k) (H := H)) F := by
      apply Submodule.mem_iSup_of_mem i
      exact ⟨f, hf, rfl⟩
    induction he using Submodule.iSup_induction' with
    | mem j e hej =>
        rcases hej with ⟨x, rfl⟩
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
            let h : augmentationFiltration (k := k) (H := H) i :=
              filtrationPieceSection (k := k)
                (augmentationFiltration (k := k) (H := H)) i
                (DirectSum.component k ℕ
                  (fun r ↦ AugmentationGradedHopfPiece
                    (k := k) (H := H) r) i f)
            have hh : (h : H) ∈ liftHomogeneousSubspace (k := k)
                (augmentationFiltration (k := k) (H := H)) F := hlift
            have hfil : (h : H) • (x.1.1 : M) ∈
                augmentationModuleFiltration (k := k) (H := H) (M := M)
                  (i + j) :=
              augmentationFiltration_action_le i j
                (product_mem_actionSubspace h.property x.2)
            have hexp : (h : H) • (x.1.1 : M) ∈
                actionExpansion
                  (liftHomogeneousSubspace (k := k)
                    (augmentationFiltration (k := k) (H := H)) F) E :=
              Submodule.mem_sup_right
                (product_mem_actionSubspace hh x.1.2)
            let z : inducedFiltration
                (augmentationModuleFiltration (k := k) (H := H) (M := M))
                (actionExpansion
                  (liftHomogeneousSubspace (k := k)
                    (augmentationFiltration (k := k) (H := H)) F) E)
                (i + j) := ⟨⟨(h : H) • (x.1.1 : M), hexp⟩, hfil⟩
            apply le_iSup (fun n ↦ LinearMap.range
              (inducedFiltrationLayerMap (k := k)
                (augmentationModuleFiltration (k := k) (H := H) (M := M))
                (actionExpansion
                  (liftHomogeneousSubspace (k := k)
                    (augmentationFiltration (k := k) (H := H)) F) E) n)) (i + j)
            refine ⟨Submodule.Quotient.mk z, ?_⟩
            change DirectSum.of
                (fun q ↦ AugmentationGradedModulePiece
                  (k := k) (H := H) (M := M) q) (i + j)
                (Submodule.Quotient.mk
                  (⟨(h : H) • (x.1.1 : M), hfil⟩ : augmentationModuleFiltration
                    (k := k) (H := H) (M := M) (i + j))) =
              (DirectSum.of
                (fun q ↦ AugmentationGradedHopfPiece
                  (k := k) (H := H) q) i (f i)) •
                DirectSum.of
                  (fun q ↦ AugmentationGradedModulePiece
                    (k := k) (H := H) (M := M) q) j (Submodule.Quotient.mk
                  (⟨x.1.1, x.2⟩ :
                    augmentationModuleFiltration
                      (k := k) (H := H) (M := M) j) :
                    AugmentationGradedModulePiece
                      (k := k) (H := H) (M := M) j)
            rw [DirectSum.Gmodule.of_smul_of]
            change DirectSum.of
                (fun q ↦ AugmentationGradedModulePiece
                  (k := k) (H := H) (M := M) q) (i + j)
                  (Submodule.Quotient.mk _) =
              DirectSum.of
                (fun q ↦ AugmentationGradedModulePiece
                  (k := k) (H := H) (M := M) q) (i + j)
                  (augmentationGradedAction (k := k) (H := H) (M := M)
                    i j (f i) (Submodule.Quotient.mk
                      (⟨x.1.1, x.2⟩ : augmentationModuleFiltration
                        (k := k) (H := H) (M := M) j)))
            apply congrArg (DirectSum.of
              (fun q ↦ AugmentationGradedModulePiece
                (k := k) (H := H) (M := M) q) (i + j))
            rw [← filtrationPiece_mk_section (k := k)
              (augmentationFiltration (k := k) (H := H)) i (f i)]
            rw [augmentationGradedAction_mk]
            rfl
    | zero => simp
    | add a b _ _ ha hb => simpa [smul_add] using Submodule.add_mem _ ha hb

end AugmentationAction

end

end HopfAmenability
