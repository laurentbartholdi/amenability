/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremA
import Amenability.HopfModuleMap
import Amenability.TensorRightComodule
import Amenability.HopfCodimOneActionTransfer
import Amenability.HopfModuleCoalgebraBaseChange
import Amenability.CocommutativeSplittingFlag
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

/-!
# Theorem B: quotients of amenable Hopf-module coalgebras

This file formalizes preservation of amenability by surjective, equivariant
coalgebra morphisms between Hopf-module coalgebras.
-/

open Coalgebra Module TensorProduct
open scoped HopfModuleBaseChange

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {H : Type v} {M : Type w} {Q : Type x}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [AddCommGroup Q] [Module k Q] [Module H Q] [IsScalarTower k H Q]

namespace IsHopfModuleMap

omit [HopfAlgebra k H] [IsScalarTower k H M] in
theorem id : IsHopfModuleMap (H := H)
    (LinearMap.id (R := k) (M := M)) := by
  intro h m
  rfl

omit [IsScalarTower k H M] [IsScalarTower k H Q] in
theorem comp {P : Type*}
    [AddCommGroup P] [Module k P] [Module H P] [IsScalarTower k H P]
    {g : Q →ₗ[k] P} {f : M →ₗ[k] Q}
    (hg : IsHopfModuleMap (H := H) g)
    (hf : IsHopfModuleMap (H := H) f) :
    IsHopfModuleMap (H := H) (g.comp f) := by
  intro h m
  simp only [LinearMap.comp_apply, hf h m, hg h (f m)]

/-- Equivariance is preserved by extension of scalars. -/
theorem baseChange
    {K : Type*} [Field K] [Algebra k K]
    {f : M →ₗ[k] Q} (hf : IsHopfModuleMap (H := H) f) :
    IsHopfModuleMap (k := K) (H := K ⊗[k] H)
      (M := K ⊗[k] M) (Q := K ⊗[k] Q) (f.baseChange K) := by
  intro h m
  induction h using TensorProduct.induction_on with
  | zero => simp
  | add h h' hh hh' =>
      simpa only [add_smul, map_add] using congrArg₂ (· + ·) hh hh'
  | tmul a x =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | add m m' hm hm' =>
          simpa only [smul_add, map_add] using congrArg₂ (· + ·) hm hm'
      | tmul b y =>
          simp only [baseChange_smul_tmul, LinearMap.baseChange_tmul]
          rw [hf]

theorem map_actionSubspace
    {f : M →ₗ[k] Q} (hf : IsHopfModuleMap (H := H) f)
    (F : Submodule k H) (E : Submodule k M) :
    (actionSubspace F E).map f = actionSubspace F (E.map f) := by
  rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, Submodule.map₂_le]
    intro h hh m hm
    change f (h • m) ∈
      Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F (E.map f)
    rw [hf h m]
    exact Submodule.apply_mem_map₂
      (Algebra.lsmul k k Q).toLinearMap hh
      (show f m ∈ E.map f from ⟨m, hm, rfl⟩)
  · rw [Submodule.map₂_le]
    rintro h hh _ ⟨m, hm, rfl⟩
    change h • f m ∈ _
    rw [← hf h m]
    exact ⟨h • m, Submodule.apply_mem_map₂ _ hh hm, rfl⟩

theorem map_actionExpansion
    {f : M →ₗ[k] Q} (hf : IsHopfModuleMap (H := H) f)
    (F : Submodule k H) (E : Submodule k M) :
    (actionExpansion F E).map f = actionExpansion F (E.map f) := by
  rw [actionExpansion, Submodule.map_sup, hf.map_actionSubspace,
    actionExpansion]

end IsHopfModuleMap

/-- The diagonal action of `H` on a tensor product of two `H`-modules. -/
def diagonalHopfAction : H ⊗[k] (M ⊗[k] Q) →ₗ[k] M ⊗[k] Q :=
  TensorProduct.map
      (hopfModuleAction (k := k) (H := H) (M := M))
      (hopfModuleAction (k := k) (H := H) (M := Q)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k H H M Q).toLinearMap ∘ₗ
    (Coalgebra.comul (R := k) (A := H)).rTensor (M ⊗[k] Q)

/-- The diagonal action by a fixed element of `H`. -/
def diagonalHopfActionBy (h : H) : M ⊗[k] Q →ₗ[k] M ⊗[k] Q :=
  diagonalHopfAction ∘ₗ TensorProduct.mk k H (M ⊗[k] Q) h

theorem diagonalHopfActionBy_apply (h : H) (z : M ⊗[k] Q) :
    diagonalHopfActionBy (k := k) (H := H) h z =
      TensorProduct.map
          (hopfModuleAction (k := k) (H := H) (M := M))
          (hopfModuleAction (k := k) (H := H) (M := Q))
        (TensorProduct.tensorTensorTensorComm k H H M Q
          (Coalgebra.comul (R := k) (A := H) h ⊗ₜ[k] z)) := by
  rfl

@[simp]
theorem diagonalHopfActionBy_tmul_of_groupLike
    {g : H} (hg : IsGroupLikeElem k g) (m : M) (q : Q) :
    diagonalHopfActionBy (k := k) (H := H) g (m ⊗ₜ[k] q) =
      (g • m) ⊗ₜ[k] (g • q) := by
  rw [diagonalHopfActionBy_apply, hg.comul_eq_tmul_self]
  rfl

/-- Action by a fixed Hopf-algebra element, restricted to a subspace of the
module. -/
def actionOnSubspace (a : H) (C : Submodule k Q) : C →ₗ[k] Q :=
  (Algebra.lsmul k k Q a).comp C.subtype

@[simp]
theorem actionOnSubspace_apply (a : H) (C : Submodule k Q) (c : C) :
    actionOnSubspace (k := k) a C c = a • (c : Q) :=
  rfl

/-- The diagonal action map with both acting coefficients restricted to a
finite subcoalgebra. -/
noncomputable def diagonalSubcoalgebraActionMap
    (A : FiniteSubcoalgebra k H) :
    (A.carrier ⊗[k] A.carrier) ⊗[k] (M ⊗[k] Q) →ₗ[k] M ⊗[k] Q :=
  TensorProduct.map
      ((hopfModuleAction (k := k) (H := H) (M := M)).comp
        (A.carrier.subtype.rTensor M))
      ((hopfModuleAction (k := k) (H := H) (M := Q)).comp
        (A.carrier.subtype.rTensor Q)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k A.carrier A.carrier M Q).toLinearMap

/-- The diagonal action written using the coproduct internal to a finite
subcoalgebra. -/
noncomputable def diagonalSubcoalgebraActionBy
    (A : FiniteSubcoalgebra k H) (a : A.carrier) :
    M ⊗[k] Q →ₗ[k] M ⊗[k] Q :=
  diagonalSubcoalgebraActionMap (M := M) (Q := Q) A ∘ₗ
    TensorProduct.mk k (A.carrier ⊗[k] A.carrier) (M ⊗[k] Q)
      (Coalgebra.comul (R := k) (A := A.carrier) a)

@[simp]
theorem diagonalSubcoalgebraActionMap_tmul_tmul
    (A : FiniteSubcoalgebra k H) (x y : A.carrier) (m : M) (q : Q) :
    diagonalSubcoalgebraActionMap (M := M) (Q := Q) A
        ((x ⊗ₜ[k] y) ⊗ₜ[k] (m ⊗ₜ[k] q)) =
      ((x : H) • m) ⊗ₜ[k] ((y : H) • q) :=
  rfl

/-- The internal and ambient descriptions of the diagonal action agree. -/
theorem diagonalSubcoalgebraActionBy_eq
    (A : FiniteSubcoalgebra k H) (a : A.carrier) :
    diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a =
      diagonalHopfActionBy (k := k) (H := H) (a : H) := by
  apply LinearMap.ext
  intro z
  have hcomul := CoalgHomClass.map_comp_comul_apply
    (subcoalgebraInclusion A.carrier A.isSubcoalgebra) a
  change TensorProduct.map A.carrier.subtype A.carrier.subtype
      (Coalgebra.comul (R := k) (A := A.carrier) a) =
    Coalgebra.comul (R := k) (A := H) (a : H) at hcomul
  rw [diagonalHopfActionBy_apply, ← hcomul]
  change
    TensorProduct.map
        ((hopfModuleAction (k := k) (H := H) (M := M)).comp
          (A.carrier.subtype.rTensor M))
        ((hopfModuleAction (k := k) (H := H) (M := Q)).comp
          (A.carrier.subtype.rTensor Q))
      (TensorProduct.tensorTensorTensorComm k A.carrier A.carrier M Q
        (Coalgebra.comul (R := k) (A := A.carrier) a ⊗ₜ[k] z)) =
      TensorProduct.map
          (hopfModuleAction (k := k) (H := H) (M := M))
          (hopfModuleAction (k := k) (H := H) (M := Q))
        (TensorProduct.tensorTensorTensorComm k H H M Q
          (TensorProduct.map A.carrier.subtype A.carrier.subtype
              (Coalgebra.comul (R := k) (A := A.carrier) a) ⊗ₜ[k] z))
  generalize Coalgebra.comul (R := k) (A := A.carrier) a = d
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [add_tmul, map_add] using
        congrArg₂ (fun p q : M ⊗[k] Q => p + q) hx hy
  | tmul x y =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw =>
          simpa only [tmul_add, map_add] using
            congrArg₂ (fun p q : M ⊗[k] Q => p + q) hz hw
      | tmul m q => rfl

/-- Modulo a coefficient subspace stable under the lower flag term, the
codimension-one diagonal action is the tensor product of the group-like
action on the first factor and action by the chosen complement on the
second factor. -/
theorem quotient_diagonalSubcoalgebraAction_codimOne
    [Coalgebra.IsCocomm k H]
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (ell : A.carrier →ₗ[k] k) (a : A.carrier)
    (hker : LinearMap.ker ell = codimOneLower A' A)
    (ha : ell a = 1)
    (P : Submodule k M) (C D : Submodule k Q)
    (hlower : ∀ (x : codimOneLower A' A) (c : C),
      (x.1 : H) • (c : Q) ∈ D)
    (z : P ⊗[k] C) :
    (D.mkQ.lTensor M)
        (diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a
          (TensorProduct.mapIncl P C z)) =
      (((Algebra.lsmul k k M
          ((codimOneGroupLikeCandidate A ell a : A.carrier) : H)).comp
            P.subtype).rTensor (Q ⧸ D))
        (((D.mkQ.comp (actionOnSubspace (k := k) (a : H) C)).lTensor P) z) := by
  let g : A.carrier := codimOneGroupLikeCandidate A ell a
  let r := Coalgebra.comul (R := k) (A := A.carrier) a - g ⊗ₜ[k] a
  obtain ⟨r₀, hr₀⟩ :=
    comul_sub_codimOneGroupLikeCandidate_tmul_mem
      A' A hAA ell a hker ha
  have hr : r = ((codimOneLower A' A).subtype.lTensor A.carrier) r₀ :=
    hr₀.symm
  have herror : ∀ v : A.carrier ⊗[k] codimOneLower A' A,
      ∀ w : P ⊗[k] C,
      (D.mkQ.lTensor M)
        (diagonalSubcoalgebraActionMap (M := M) (Q := Q) A
          (((codimOneLower A' A).subtype.lTensor A.carrier v) ⊗ₜ[k]
            TensorProduct.mapIncl P C w)) = 0 := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero =>
        intro w
        simp
    | add v v' hv hv' =>
        intro w
        simp only [map_add, add_tmul]
        rw [hv w, hv' w, add_zero]
    | tmul x y =>
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add w w' hw hw' =>
            simpa only [map_add, tmul_add, zero_add] using
              congrArg₂ (fun p q : M ⊗[k] (Q ⧸ D) => p + q) hw hw'
        | tmul p c =>
            change ((x : H) • (p : M)) ⊗ₜ[k]
              D.mkQ ((y.1 : H) • (c : Q)) = 0
            have hy : D.mkQ ((y.1 : H) • (c : Q)) = 0 :=
              (Submodule.Quotient.mk_eq_zero D).2 (hlower y c)
            rw [hy, tmul_zero]
  have hmain : ∀ w : P ⊗[k] C,
      (D.mkQ.lTensor M)
          (diagonalSubcoalgebraActionMap (M := M) (Q := Q) A
            ((g ⊗ₜ[k] a) ⊗ₜ[k] TensorProduct.mapIncl P C w)) =
        (((Algebra.lsmul k k M (g : H)).comp P.subtype).rTensor (Q ⧸ D))
          (((D.mkQ.comp (actionOnSubspace (k := k) (a : H) C)).lTensor P) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' =>
        simpa only [map_add, tmul_add] using
          congrArg₂ (fun p q : M ⊗[k] (Q ⧸ D) => p + q) hw hw'
    | tmul p c => rfl
  have hsplit : Coalgebra.comul (R := k) (A := A.carrier) a =
      g ⊗ₜ[k] a + r := by
    dsimp [r]
    abel
  change (D.mkQ.lTensor M)
      (diagonalSubcoalgebraActionMap (M := M) (Q := Q) A
        (Coalgebra.comul (R := k) (A := A.carrier) a ⊗ₜ[k]
          TensorProduct.mapIncl P C z)) = _
  rw [hsplit, add_tmul, map_add, map_add, hmain]
  have hz := herror r₀ z
  rw [← hr] at hz
  rw [hz, add_zero]

/-- Tensor exactness isolates the kernel in the second factor after an
injective twist of the first factor. -/
theorem mem_range_ker_lTensor_of_rTensor_eq_zero
    {P₀ T U V : Type*}
    [AddCommGroup P₀] [Module k P₀]
    [AddCommGroup T] [Module k T]
    [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    (g : P₀ →ₗ[k] T) (hg : Function.Injective g)
    (f : U →ₗ[k] V) (z : P₀ ⊗[k] U)
    (hz : (g.rTensor V) (f.lTensor P₀ z) = 0) :
    z ∈ LinearMap.range ((LinearMap.ker f).subtype.lTensor P₀) := by
  have hginj : Function.Injective (g.rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap g hg
  have hfz : f.lTensor P₀ z = 0 :=
    hginj (hz.trans (map_zero _).symm)
  let i : LinearMap.ker f →ₗ[k] U := (LinearMap.ker f).subtype
  have hexact : Function.Exact i f := by
    change Function.Exact (LinearMap.ker f).subtype f
    exact f.exact_subtype_ker_map
  have htensorExact : Function.Exact
      (i.lTensor P₀) (f.lTensor P₀) :=
    Module.Flat.lTensor_exact P₀ hexact
  rw [← htensorExact.linearMap_ker_eq, LinearMap.mem_ker]
  exact hfz

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

section TensorSubspaceLattice

variable {P : Type*} [AddCommGroup P] [Module k P]

/-- The canonical equivalence between a tensor product with a subspace and
its tensor-copy subspace in the ambient tensor product. -/
noncomputable def tensorSubspaceEquiv (U : Submodule k Q) :
    P ⊗[k] U ≃ₗ[k] tensorSubspace (k := k) P U :=
  LinearEquiv.ofInjective (U.subtype.lTensor P)
    (Module.Flat.lTensor_preserves_injective_linearMap
      U.subtype U.injective_subtype)

@[simp]
theorem coe_tensorSubspaceEquiv_apply (U : Submodule k Q)
    (z : P ⊗[k] U) :
    ((tensorSubspaceEquiv (k := k) (P := P) U z :
      tensorSubspace (k := k) P U) : P ⊗[k] Q) =
      U.subtype.lTensor P z :=
  rfl

/-- Passing successively through nested ambient subspaces gives the same
tensor in the original ambient tensor product. -/
theorem mapIncl_tensorSubspaceEquiv_ambient
    (P₀ : Submodule k M) (R : Submodule k Q) (C : Submodule k R)
    (z : P₀ ⊗[k] C) :
    TensorProduct.mapIncl P₀ R
        ((tensorSubspaceEquiv (k := k) (P := P₀) C z :
          tensorSubspace (k := k) P₀ C) : P₀ ⊗[k] R) =
      TensorProduct.mapIncl P₀ (ambientImage R C)
        (TensorProduct.map LinearMap.id
          (ambientImageEquiv R C).toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add, Submodule.coe_add] using
        congrArg₂ (fun x y : M ⊗[k] Q => x + y) hz hz'
  | tmul p c => rfl

/-- The preceding compatibility in the inverse direction. -/
theorem mapIncl_tensorSubspaceEquiv_symm_ambient
    (P₀ : Submodule k M) (R : Submodule k Q) (C : Submodule k R)
    (x : tensorSubspace (k := k) P₀ C) :
    TensorProduct.mapIncl P₀ R (x : P₀ ⊗[k] R) =
      TensorProduct.mapIncl P₀ (ambientImage R C)
        (TensorProduct.map LinearMap.id
          (ambientImageEquiv R C).toLinearMap
            ((tensorSubspaceEquiv (k := k) (P := P₀) C).symm x)) := by
  rw [← mapIncl_tensorSubspaceEquiv_ambient]
  exact congrArg (TensorProduct.mapIncl P₀ R)
    (congrArg Subtype.val
      ((tensorSubspaceEquiv (k := k) (P := P₀) C).apply_symm_apply x).symm)

/-- A tensor supported on an internal subspace remains supported on the
ambient image of that subspace after one more inclusion. -/
theorem tensorSubspaceEquiv_mem_ambientImage
    {R : Type*} [AddCommGroup R] [Module k R]
    (C : Submodule k R) (K : Submodule k C)
    (z : P ⊗[k] C)
    (hz : z ∈ LinearMap.range (K.subtype.lTensor P)) :
    ((tensorSubspaceEquiv (k := k) (P := P) C z :
      tensorSubspace (k := k) P C) : P ⊗[k] R) ∈
        tensorSubspace (k := k) P (ambientImage C K) := by
  rcases hz with ⟨w, rfl⟩
  let w' : P ⊗[k] ambientImage C K :=
    TensorProduct.map LinearMap.id (ambientImageEquiv C K).toLinearMap w
  refine ⟨w', ?_⟩
  change (ambientImage C K).subtype.lTensor P w' =
    C.subtype.lTensor P (K.subtype.lTensor P w)
  dsimp [w']
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul p x => rfl

/-- Action by one Hopf-algebra element between two prescribed ambient
coefficient spaces. -/
def actionBetweenSubspaces
    (a : H) (R S : Submodule k Q) (C : Submodule k R)
    (ha : ∀ c : C, a • ((c : R) : Q) ∈ S) : C →ₗ[k] S :=
  LinearMap.codRestrict S
    ((Algebra.lsmul k k Q a).comp (R.subtype.comp C.subtype)) ha

@[simp]
theorem coe_actionBetweenSubspaces_apply
    (a : H) (R S : Submodule k Q) (C : Submodule k R)
    (ha : ∀ c : C, a • ((c : R) : Q) ∈ S) (c : C) :
    ((actionBetweenSubspaces (k := k) a R S C ha c : S) : Q) =
      a • ((c : R) : Q) :=
  rfl

/-- Action by one element from an entire prescribed source coefficient
space into a prescribed target coefficient space. -/
def actionFromSubspace
    (a : H) (R S : Submodule k Q)
    (ha : ∀ r : R, a • (r : Q) ∈ S) : R →ₗ[k] S :=
  LinearMap.codRestrict S
    ((Algebra.lsmul k k Q a).comp R.subtype) ha

@[simp]
theorem coe_actionFromSubspace_apply
    (a : H) (R S : Submodule k Q)
    (ha : ∀ r : R, a • (r : Q) ∈ S) (r : R) :
    ((actionFromSubspace (k := k) a R S ha r : S) : Q) = a • (r : Q) :=
  rfl

/-- Membership in the ambient image of the kernel of a quotient map is the
expected ambient membership condition. -/
theorem coe_mem_ambientImage_ker_mkQ_comp_iff
    {R S : Type*}
    [AddCommGroup R] [Module k R]
    [AddCommGroup S] [Module k S]
    (C : Submodule k R) (D : Submodule k S) (f : C →ₗ[k] S)
    (c : C) :
    (c : R) ∈ ambientImage C (LinearMap.ker (D.mkQ.comp f)) ↔
      f c ∈ D := by
  constructor
  · rintro ⟨z, hz, hzc⟩
    have hzc' : (z : C) = c := C.injective_subtype hzc
    subst c
    have hz0 := (LinearMap.mem_ker).1 hz
    change D.mkQ (f z) = 0 at hz0
    exact (Submodule.Quotient.mk_eq_zero D).1 hz0
  · intro hc
    refine ⟨c, ?_, rfl⟩
    apply (LinearMap.mem_ker).2
    change D.mkQ (f c) = 0
    exact (Submodule.Quotient.mk_eq_zero D).2 hc

/-- The inclusion of an ambient subspace induces an inclusion on the
corresponding quotients. -/
def ambientQuotientMap (S : Submodule k Q) (D : Submodule k S) :
    (S ⧸ D) →ₗ[k] (Q ⧸ ambientImage S D) :=
  D.mapQ (ambientImage S D) S.subtype (by
    intro s hs
    exact ⟨s, hs, rfl⟩)

@[simp]
theorem ambientQuotientMap_mkQ
    (S : Submodule k Q) (D : Submodule k S) (s : S) :
    ambientQuotientMap S D (D.mkQ s) =
      (ambientImage S D).mkQ (s : Q) :=
  rfl

/-- The map on quotients induced by a subspace inclusion is injective. -/
theorem ambientQuotientMap_injective
    (S : Submodule k Q) (D : Submodule k S) :
    Function.Injective (ambientQuotientMap S D) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  constructor
  · intro hx
    obtain ⟨s, rfl⟩ := D.mkQ_surjective x
    rw [LinearMap.mem_ker] at hx
    change (ambientImage S D).mkQ (s : Q) = 0 at hx
    have hsAmbient : (s : Q) ∈ ambientImage S D :=
      (Submodule.Quotient.mk_eq_zero (ambientImage S D)).1 hx
    have hs : s ∈ D := by
      rw [show D = (ambientImage S D).comap S.subtype by
        symm
        exact Submodule.comap_map_eq_of_injective S.injective_subtype D]
      exact hsAmbient
    have : D.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero D).2 hs
    simp [this]
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact LinearMap.map_zero _

omit [Module H M] [IsScalarTower k H M] in
/-- Quotienting an action map commutes with passing from internal source and
target coefficient spaces to their ambient images. -/
theorem quotient_actionBetweenSubspaces_natural
    (a : H) (P₀ : Submodule k M)
    (R S : Submodule k Q) (C : Submodule k R) (D : Submodule k S)
    (ha : ∀ c : C, a • ((c : R) : Q) ∈ S)
    (z : P₀ ⊗[k] C) :
    (((ambientImage S D).mkQ.comp
        (actionOnSubspace (k := k) a (ambientImage R C))).lTensor P₀)
      (TensorProduct.map LinearMap.id
        (ambientImageEquiv R C).toLinearMap z) =
    ((ambientQuotientMap S D).lTensor P₀)
      (((D.mkQ.comp (actionBetweenSubspaces (k := k) a R S C ha)).lTensor P₀) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add] using
        congrArg₂ (fun x y : P₀ ⊗[k] (Q ⧸ ambientImage S D) => x + y) hz hz'
  | tmul p c => rfl

theorem tensorSubspace_sup (U V : Submodule k Q) :
    tensorSubspace (k := k) P (U ⊔ V) =
      tensorSubspace (k := k) P U ⊔ tensorSubspace (k := k) P V := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simpa only [map_add] using add_mem hz hz'
    | tmul p q =>
        rcases q with ⟨q, hq⟩
        rw [Submodule.mem_sup] at hq
        rcases hq with ⟨u, hu, v, hv, huv⟩
        subst q
        change p ⊗ₜ[k] (u + v) ∈ _
        rw [tmul_add]
        exact add_mem
          ((le_sup_left : tensorSubspace (k := k) P U ≤ _)
            ⟨p ⊗ₜ[k] ⟨u, hu⟩, rfl⟩)
          ((le_sup_right : tensorSubspace (k := k) P V ≤ _)
            ⟨p ⊗ₜ[k] ⟨v, hv⟩, rfl⟩)
  · exact sup_le
      (tensorSubspace_mono (W := P) le_sup_left)
      (tensorSubspace_mono (W := P) le_sup_right)

private theorem ker_equiv_comp
    {A B D : Type*}
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    [AddCommGroup D] [Module k D]
    (e : B ≃ₗ[k] D) (f : A →ₗ[k] B) :
    LinearMap.ker (e.toLinearMap.comp f) = LinearMap.ker f := by
  ext x
  simp

private theorem range_subtype_lTensor_eq_ker_mkQ_lTensor
    (U : Submodule k Q) :
    LinearMap.range (U.subtype.lTensor P) =
      LinearMap.ker (U.mkQ.lTensor P) := by
  have h := Module.Flat.lTensor_exact P
    (LinearMap.exact_subtype_ker_map U.mkQ)
  have hU : LinearMap.ker U.mkQ = U := by ext x; simp
  have hex := (LinearMap.exact_iff.mp h).symm
  rw [hU] at hex
  exact hex

/-- Tensor-copy membership is reflected by nested ambient inclusions. -/
theorem mapIncl_mem_tensorSubspace_ambient_iff
    (P₀ : Submodule k M) (S : Submodule k Q) (D : Submodule k S)
    (z : P₀ ⊗[k] S) :
    TensorProduct.mapIncl P₀ S z ∈
        tensorSubspace (k := k) M (ambientImage S D) ↔
      z ∈ tensorSubspace (k := k) P₀ D := by
  let qmap : (S ⧸ D) →ₗ[k] (Q ⧸ ambientImage S D) :=
    ambientQuotientMap S D
  have hnatural :
      ((ambientImage S D).mkQ.lTensor M)
          (TensorProduct.mapIncl P₀ S z) =
        (P₀.subtype.rTensor (Q ⧸ ambientImage S D))
          (qmap.lTensor P₀ (D.mkQ.lTensor P₀ z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simpa only [map_add] using
          congrArg₂ (fun x y : M ⊗[k] (Q ⧸ ambientImage S D) => x + y) hz hz'
    | tmul p s => rfl
  have hPinj : Function.Injective
      (P₀.subtype.rTensor (Q ⧸ ambientImage S D)) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      P₀.subtype P₀.injective_subtype
  have hqinj : Function.Injective (qmap.lTensor P₀) :=
    Module.Flat.lTensor_preserves_injective_linearMap qmap
      (ambientQuotientMap_injective S D)
  change TensorProduct.mapIncl P₀ S z ∈
      LinearMap.range ((ambientImage S D).subtype.lTensor M) ↔
    z ∈ LinearMap.range (D.subtype.lTensor P₀)
  rw [range_subtype_lTensor_eq_ker_mkQ_lTensor,
    range_subtype_lTensor_eq_ker_mkQ_lTensor,
    LinearMap.mem_ker, LinearMap.mem_ker, hnatural]
  constructor
  · intro hz0
    have hq0 : qmap.lTensor P₀ (D.mkQ.lTensor P₀ z) = 0 :=
      hPinj (hz0.trans (map_zero _).symm)
    exact hqinj (hq0.trans (map_zero _).symm)
  · intro hz0
    rw [hz0, map_zero, map_zero]

theorem tensorSubspace_inf (U V : Submodule k Q) :
    tensorSubspace (k := k) P (U ⊓ V) =
      tensorSubspace (k := k) P U ⊓ tensorSubspace (k := k) P V := by
  let q : Q →ₗ[k] (Q ⧸ U) × (Q ⧸ V) := U.mkQ.prod V.mkQ
  let e :
      P ⊗[k] ((Q ⧸ U) × (Q ⧸ V)) ≃ₗ[k]
        (P ⊗[k] (Q ⧸ U)) × (P ⊗[k] (Q ⧸ V)) :=
    TensorProduct.prodRight k k P (Q ⧸ U) (Q ⧸ V)
  have hkerq : LinearMap.ker q = U ⊓ V := by
    simp [q]
  have hq :
      LinearMap.range ((LinearMap.ker q).subtype.lTensor P) =
        LinearMap.ker (q.lTensor P) := by
    have h := Module.Flat.lTensor_exact P
      (LinearMap.exact_subtype_ker_map q)
    exact (LinearMap.exact_iff.mp h).symm
  have hcomp :
      e.toLinearMap.comp (q.lTensor P) =
        (U.mkQ.lTensor P).prod (V.mkQ.lTensor P) := by
    ext p x
    · simp [q, e, TensorProduct.prodRight]
    · simp [q, e, TensorProduct.prodRight]
  have hker : LinearMap.ker (q.lTensor P) =
      LinearMap.ker (U.mkQ.lTensor P) ⊓
        LinearMap.ker (V.mkQ.lTensor P) := by
    calc
      LinearMap.ker (q.lTensor P) =
          LinearMap.ker (e.toLinearMap.comp (q.lTensor P)) :=
        (ker_equiv_comp e (q.lTensor P)).symm
      _ = LinearMap.ker
          ((U.mkQ.lTensor P).prod (V.mkQ.lTensor P)) := by rw [hcomp]
      _ = _ := LinearMap.ker_prod _ _
  rw [hkerq] at hq
  change LinearMap.range ((U ⊓ V).subtype.lTensor P) = _
  calc
    LinearMap.range ((U ⊓ V).subtype.lTensor P) =
        LinearMap.ker (q.lTensor P) := hq
    _ = LinearMap.ker (U.mkQ.lTensor P) ⊓
        LinearMap.ker (V.mkQ.lTensor P) := hker
    _ = _ := by
      change LinearMap.ker (U.mkQ.lTensor P) ⊓
          LinearMap.ker (V.mkQ.lTensor P) =
        LinearMap.range (U.subtype.lTensor P) ⊓
          LinearMap.range (V.subtype.lTensor P)
      rw [range_subtype_lTensor_eq_ker_mkQ_lTensor,
        range_subtype_lTensor_eq_ker_mkQ_lTensor]

theorem tensorSubspace_le_iff [FiniteDimensional k P]
    (hP : 0 < finrank k P) {U V : Submodule k Q} :
    tensorSubspace (k := k) P U ≤ tensorSubspace (k := k) P V ↔ U ≤ V := by
  constructor
  · intro hUV
    obtain ⟨ell, a, ha⟩ := exists_leftFunctional_apply_eq_one (k := k) hP
    have hcontract_mem : ∀ z : P ⊗[k] V,
        TensorProduct.leftContract ell ((V.subtype.lTensor P) z) ∈ V := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' ih ih' =>
          simpa only [map_add] using V.add_mem ih ih'
      | tmul p v =>
          change ell p • (v : Q) ∈ V
          exact V.smul_mem _ v.2
    intro q hq
    have haq : a ⊗ₜ[k] q ∈ tensorSubspace (k := k) P U :=
      ⟨a ⊗ₜ[k] (⟨q, hq⟩ : U), rfl⟩
    rcases hUV haq with ⟨z, hz⟩
    have hcontract := hcontract_mem z
    rw [hz, TensorProduct.leftContract_tmul, ha, one_smul] at hcontract
    exact hcontract
  · exact tensorSubspace_mono (W := P)

/-- The lattice of subspaces of `Q` embedded as tensor copies in `P ⊗ Q`. -/
def tensorSubspaceAdmissibleFamily : AdmissibleFamily k (P ⊗[k] Q) where
  admissible Z := ∃ U : Submodule k Q,
    Z = tensorSubspace (k := k) P U
  bot_admissible := ⟨⊥, tensorSubspace_bot.symm⟩
  sup_admissible := by
    rintro C D ⟨U, rfl⟩ ⟨V, rfl⟩
    exact ⟨U ⊔ V, (tensorSubspace_sup U V).symm⟩
  inf_admissible := by
    rintro C D ⟨U, rfl⟩ ⟨V, rfl⟩
    exact ⟨U ⊓ V, (tensorSubspace_inf U V).symm⟩

/-- The density parameter on a tensor copy corresponding to the unscaled
coefficient-space parameter `t`. -/
def coefficientTensorParameter (P : Type*)
    [AddCommGroup P] [Module k P] [FiniteDimensional k P] (t : ℚ) : ℚ :=
  t / finrank k P

/-- The coefficient subspace represented by the largest tensor-copy density
maximizer, with parameter normalized by the dimension of the first factor. -/
noncomputable def coefficientDensitySubspace
    [FiniteDimensional k P]
    [FiniteDimensional k (P ⊗[k] Q)]
    (X : Submodule k (P ⊗[k] Q)) (t : ℚ) : Submodule k Q :=
  Classical.choose
    (densitySubspace_admissible
      (tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := Q)) X
        (coefficientTensorParameter (k := k) P t))

theorem tensorSubspace_coefficientDensitySubspace
    [FiniteDimensional k P]
    [FiniteDimensional k (P ⊗[k] Q)]
    (X : Submodule k (P ⊗[k] Q)) (t : ℚ) :
    tensorSubspace (k := k) P (coefficientDensitySubspace X t) =
      densitySubspace
        (tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := Q)) X
          (coefficientTensorParameter (k := k) P t) := by
  exact (Classical.choose_spec
    (densitySubspace_admissible
      (tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := Q)) X
        (coefficientTensorParameter (k := k) P t))).symm

/-- The rank of a coefficient subspace relative to a finite tensor subspace. -/
def coefficientRank (X : Submodule k (P ⊗[k] Q))
    (U : Submodule k Q) : ℕ :=
  sfinrank k (X ⊓ tensorSubspace (k := k) P U)

/-- Semistability of the coefficient-density maximizer. -/
theorem coefficientDensitySubspace_semistable
    [FiniteDimensional k P] [FiniteDimensional k Q]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] Q)) (t : ℚ)
    (B : Submodule k Q) :
    t * ((sfinrank k (coefficientDensitySubspace X t) : ℚ) -
        sfinrank k B) ≤
      (coefficientRank X (coefficientDensitySubspace X t) : ℚ) -
        coefficientRank X B := by
  let family : AdmissibleFamily k (P ⊗[k] Q) :=
    tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := Q)
  have hmax := densitySubspace_isMaximizer family X
    (coefficientTensorParameter (k := k) P t)
  have hsem := hmax.semistable
    (show family.admissible (tensorSubspace (k := k) P B) from ⟨B, rfl⟩)
  rw [← tensorSubspace_coefficientDensitySubspace X t] at hsem
  simp only [coefficientTensorParameter, intersectionRank,
    coefficientRank, sfinrank_tensorSubspace, Nat.cast_mul] at hsem ⊢
  have hPq : (finrank k P : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hP)
  have hscale :
      t / (finrank k P : ℚ) *
          ((finrank k P : ℚ) *
              (sfinrank k (coefficientDensitySubspace X t) : ℚ) -
            (finrank k P : ℚ) * (sfinrank k B : ℚ)) =
        t * ((sfinrank k (coefficientDensitySubspace X t) : ℚ) -
          sfinrank k B) := by
    field_simp [hPq]
  rw [hscale] at hsem
  exact hsem

/-- The coefficient density subspace is the largest maximizer of its
coefficient-space score. -/
theorem coefficientDensitySubspace_largest
    [FiniteDimensional k P] [FiniteDimensional k Q]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] Q)) (t : ℚ)
    (D : Submodule k Q)
    (hscore :
      (coefficientRank X (coefficientDensitySubspace X t) : ℚ) -
          t * sfinrank k (coefficientDensitySubspace X t) ≤
        (coefficientRank X D : ℚ) - t * sfinrank k D) :
    D ≤ coefficientDensitySubspace X t := by
  let family : AdmissibleFamily k (P ⊗[k] Q) :=
    tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := Q)
  let C := coefficientDensitySubspace X t
  have hmax := densitySubspace_isLargestMaximizer family X
    (coefficientTensorParameter (k := k) P t)
  have hDadm : family.admissible (tensorSubspace (k := k) P D) := ⟨D, rfl⟩
  have hCeq : tensorSubspace (k := k) P C =
      densitySubspace family X (coefficientTensorParameter (k := k) P t) := by
    exact tensorSubspace_coefficientDensitySubspace X t
  have hscoreEq : densityScore X (coefficientTensorParameter (k := k) P t)
      (tensorSubspace (k := k) P D) =
      densityScore X (coefficientTensorParameter (k := k) P t)
        (densitySubspace family X (coefficientTensorParameter (k := k) P t)) := by
    have hmaxle := hmax.1.2 (tensorSubspace (k := k) P D) hDadm
    rw [← hCeq] at hmaxle ⊢
    apply le_antisymm hmaxle
    simp only [densityScore, intersectionRank, coefficientTensorParameter,
      sfinrank_tensorSubspace, Nat.cast_mul]
    have hPq : (finrank k P : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hP)
    have hscale (U : Submodule k Q) :
        t / (finrank k P : ℚ) *
            ((finrank k P : ℚ) * (sfinrank k U : ℚ)) =
          t * sfinrank k U := by
      field_simp [hPq]
    rw [hscale, hscale]
    exact hscore
  have hDmax : IsDensityMaximizer family X
      (coefficientTensorParameter (k := k) P t)
      (tensorSubspace (k := k) P D) := by
    refine ⟨hDadm, ?_⟩
    intro Z hZ
    calc
      densityScore X (coefficientTensorParameter (k := k) P t) Z ≤
          densityScore X (coefficientTensorParameter (k := k) P t)
            (densitySubspace family X
              (coefficientTensorParameter (k := k) P t)) := hmax.1.2 Z hZ
      _ = densityScore X (coefficientTensorParameter (k := k) P t)
          (tensorSubspace (k := k) P D) := hscoreEq.symm
  have hleTensor := hmax.2 (tensorSubspace (k := k) P D) hDmax
  rw [← hCeq] at hleTensor
  exact (tensorSubspace_le_iff (k := k) hP).1 hleTensor

/-- A finite-dimensional tensor subspace is supported on finite-dimensional
subspaces of both tensor factors. -/
theorem exists_finite_tensor_envelope
    (X : Submodule k (M ⊗[k] Q)) [FiniteDimensional k X] :
    ∃ (P : Submodule k M) (R : Submodule k Q),
      FiniteDimensional k P ∧ FiniteDimensional k R ∧
        X ≤ LinearMap.range (TensorProduct.mapIncl P R) := by
  let e := Module.finBasis k X
  let s : Set (M ⊗[k] Q) :=
    Set.range fun i : Fin (finrank k X) => (e i : M ⊗[k] Q)
  have hs : s.Finite := Set.finite_range _
  obtain ⟨P, R, hP, hR, hsupp⟩ :=
    TensorProduct.exists_finite_submodule_of_setFinite s hs
  let : Module.Finite k P := hP
  let : Module.Finite k R := hR
  let : FiniteDimensional k P := by infer_instance
  let : FiniteDimensional k R := by infer_instance
  refine ⟨P, R, inferInstance, inferInstance, ?_⟩
  intro x hx
  let x' : X := ⟨x, hx⟩
  have hxsum : x = ∑ i, (e.repr x') i • (e i : M ⊗[k] Q) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      (congrArg Subtype.val (e.sum_repr x')).symm
  rw [hxsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (hsupp
      (show (e i : M ⊗[k] Q) ∈ s from ⟨i, rfl⟩))

/-- The ambient image of a tensor subspace supported on two ambient
submodules. -/
def ambientTensorImage (P : Submodule k M) (R : Submodule k Q)
    (X : Submodule k (P ⊗[k] R)) : Submodule k (M ⊗[k] Q) :=
  X.map (TensorProduct.mapIncl P R)

theorem ambientTensorImage_mono
    (P : Submodule k M) (R : Submodule k Q)
    {X Y : Submodule k (P ⊗[k] R)} (hXY : X ≤ Y) :
    ambientTensorImage P R X ≤ ambientTensorImage P R Y :=
  Submodule.map_mono hXY

/-- A linear map which is injective modulo prescribed subspaces gives the
corresponding codimension inequality. -/
theorem finrank_sub_le_finrank_sub_of_ker_le
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (V₀ : Submodule k V) (W₀ : Submodule k W)
    (f : V →ₗ[k] W)
    (hker : LinearMap.ker (W₀.mkQ.comp f) ≤ V₀) :
    finrank k V - sfinrank k V₀ ≤ finrank k W - sfinrank k W₀ := by
  let qf : V →ₗ[k] W ⧸ W₀ := W₀.mkQ.comp f
  have hrank := LinearMap.finrank_range_add_finrank_ker qf
  have hkerdim : finrank k (LinearMap.ker qf) ≤ sfinrank k V₀ :=
    Submodule.finrank_mono hker
  have hrange : finrank k (LinearMap.range qf) ≤ finrank k (W ⧸ W₀) :=
    Submodule.finrank_le _
  have hquot := W₀.finrank_quotient_add_finrank
  have hV₀ : sfinrank k V₀ ≤ finrank k V := Submodule.finrank_le V₀
  have hW₀ : sfinrank k W₀ ≤ finrank k W := Submodule.finrank_le W₀
  have hVsub : finrank k V - sfinrank k V₀ + sfinrank k V₀ =
      finrank k V := Nat.sub_add_cancel hV₀
  have hWsub : finrank k W - sfinrank k W₀ + sfinrank k W₀ =
      finrank k W := Nat.sub_add_cancel hW₀
  simp only [sfinrank] at *
  omega

/-- Ambient form of the preceding codimension comparison.  The linear map is
defined on the larger source subspace and takes values in the larger target
subspace; its kernel modulo the smaller target is required to lie in the
smaller source. -/
theorem sfinrank_sub_le_sfinrank_sub_of_ker_le
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (V₀ V₁ : Submodule k V) (W₀ W₁ : Submodule k W)
    (hV : V₀ ≤ V₁) (hW : W₀ ≤ W₁)
    (f : V₁ →ₗ[k] W₁)
    (hker : LinearMap.ker
        ((W₀.comap W₁.subtype).mkQ.comp f) ≤ V₀.comap V₁.subtype) :
    sfinrank k V₁ - sfinrank k V₀ ≤
      sfinrank k W₁ - sfinrank k W₀ := by
  have h := finrank_sub_le_finrank_sub_of_ker_le
    (V₀.comap V₁.subtype) (W₀.comap W₁.subtype) f hker
  have hVimage : ambientImage V₁ (V₀.comap V₁.subtype) = V₀ :=
    ambientImage_comap_eq_of_le V₁ V₀ hV
  have hWimage : ambientImage W₁ (W₀.comap W₁.subtype) = W₀ :=
    ambientImage_comap_eq_of_le W₁ W₀ hW
  have hVdim : sfinrank k (V₀.comap V₁.subtype) = sfinrank k V₀ := by
    calc
      sfinrank k (V₀.comap V₁.subtype) =
          sfinrank k (ambientImage V₁ (V₀.comap V₁.subtype)) :=
        (finrank_ambientImage V₁ (V₀.comap V₁.subtype)).symm
      _ = sfinrank k V₀ := by rw [hVimage]
  have hWdim : sfinrank k (W₀.comap W₁.subtype) = sfinrank k W₀ := by
    calc
      sfinrank k (W₀.comap W₁.subtype) =
          sfinrank k (ambientImage W₁ (W₀.comap W₁.subtype)) :=
        (finrank_ambientImage W₁ (W₀.comap W₁.subtype)).symm
      _ = sfinrank k W₀ := by rw [hWimage]
  simpa only [sfinrank, hVdim, hWdim] using h

/-- A linear map between the relevant intersections proves the rank-gain
inequality used in the coefficient-density argument. -/
theorem coefficientRank_sub_le_coefficientRank_sub_of_ker_le
    {R S : Type*}
    [AddCommGroup R] [Module k R] [FiniteDimensional k R]
    [AddCommGroup S] [Module k S] [FiniteDimensional k S]
    [FiniteDimensional k P]
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (K C : Submodule k R) (D D' : Submodule k S)
    (hKC : K ≤ C) (hDD' : D ≤ D')
    (f : (X ⊓ tensorSubspace (k := k) P C :
        Submodule k (P ⊗[k] R)) →ₗ[k]
      (Y ⊓ tensorSubspace (k := k) P D' :
        Submodule k (P ⊗[k] S)))
    (hker : LinearMap.ker
        (((Y ⊓ tensorSubspace (k := k) P D).comap
            (Y ⊓ tensorSubspace (k := k) P D').subtype).mkQ.comp f) ≤
      (X ⊓ tensorSubspace (k := k) P K).comap
        (X ⊓ tensorSubspace (k := k) P C).subtype) :
    coefficientRank X C - coefficientRank X K ≤
      coefficientRank Y D' - coefficientRank Y D := by
  apply sfinrank_sub_le_sfinrank_sub_of_ker_le
    (X ⊓ tensorSubspace (k := k) P K)
    (X ⊓ tensorSubspace (k := k) P C)
    (Y ⊓ tensorSubspace (k := k) P D)
    (Y ⊓ tensorSubspace (k := k) P D')
    (inf_le_inf le_rfl (tensorSubspace_mono (W := P) hKC))
    (inf_le_inf le_rfl (tensorSubspace_mono (W := P) hDD')) f hker

/-- Rank-nullity for adjoining the image of a linear map to a fixed
subspace. -/
theorem finrank_sup_range_sub_eq
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (D : Submodule k W) (f : V →ₗ[k] W) :
    sfinrank k (D ⊔ LinearMap.range f) - sfinrank k D =
      finrank k V - finrank k (LinearMap.ker (D.mkQ.comp f)) := by
  let N : Submodule k W := D ⊔ LinearMap.range f
  let qf : V →ₗ[k] W ⧸ D := D.mkQ.comp f
  let π : N →ₗ[k] LinearMap.range qf :=
    { toFun := fun n => ⟨D.mkQ n, by
        rcases Submodule.mem_sup.1 n.2 with ⟨d, hd, y, hy, hdy⟩
        rcases hy with ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        change D.mkQ (f v) = D.mkQ n
        rw [← hdy, map_add]
        have : D.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero D).2 hd
        rw [this, zero_add]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }
  have hπsurj : Function.Surjective π := by
    rintro ⟨_, v, rfl⟩
    refine ⟨⟨f v, Submodule.mem_sup_right ⟨v, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let Dint : Submodule k N := D.comap N.subtype
  have hkerπ : LinearMap.ker π = Dint := by
    ext n
    rw [LinearMap.mem_ker]
    constructor
    · intro hn
      have hn' := congrArg Subtype.val hn
      change D.mkQ (n : W) = 0 at hn'
      exact (Submodule.Quotient.mk_eq_zero D).1 hn'
    · intro hn
      apply Subtype.ext
      change D.mkQ (n : W) = 0
      exact (Submodule.Quotient.mk_eq_zero D).2 hn
  have hDimage : ambientImage N Dint = D := by
    exact ambientImage_comap_eq_of_le N D le_sup_left
  have hdimDint : finrank k Dint = sfinrank k D := by
    calc
      finrank k Dint = finrank k (ambientImage N Dint) :=
        (finrank_ambientImage N Dint).symm
      _ = sfinrank k D := by rw [hDimage]
  have hπrank := LinearMap.finrank_range_add_finrank_ker π
  have hπrange : LinearMap.range π = ⊤ := LinearMap.range_eq_top.2 hπsurj
  rw [hπrange, finrank_top, hkerπ, hdimDint] at hπrank
  have hqfrank := LinearMap.finrank_range_add_finrank_ker qf
  have hDle : sfinrank k D ≤ sfinrank k N := Submodule.finrank_mono le_sup_left
  have hkerle : finrank k (LinearMap.ker qf) ≤ finrank k V :=
    Submodule.finrank_le _
  have hNsub : sfinrank k N - sfinrank k D + sfinrank k D =
      sfinrank k N := Nat.sub_add_cancel hDle
  have hVsub : finrank k V - finrank k (LinearMap.ker qf) +
      finrank k (LinearMap.ker qf) = finrank k V :=
    Nat.sub_add_cancel hkerle
  change sfinrank k N - sfinrank k D =
    finrank k V - finrank k (LinearMap.ker qf)
  simp only [sfinrank] at *
  omega

/-- The numerical codimension-one density step.  Its only geometric input is
the rank-gain inequality produced by the triangular coproduct formula. -/
theorem coefficientDensity_codimOne_of_rank_gain
    [FiniteDimensional k P]
    {R S : Type*}
    [AddCommGroup R] [Module k R] [FiniteDimensional k R]
    [AddCommGroup S] [Module k S] [FiniteDimensional k S]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (t : ℚ)
    (f : coefficientDensitySubspace X t →ₗ[k] S)
    (hgain :
      (coefficientRank X (coefficientDensitySubspace X t) : ℚ) -
          coefficientRank X
            (ambientImage (coefficientDensitySubspace X t)
              (LinearMap.ker
                ((coefficientDensitySubspace Y t).mkQ.comp f))) ≤
        (coefficientRank Y
            (coefficientDensitySubspace Y t ⊔ LinearMap.range f) : ℚ) -
          coefficientRank Y (coefficientDensitySubspace Y t)) :
    LinearMap.range f ≤ coefficientDensitySubspace Y t := by
  let C := coefficientDensitySubspace X t
  let D := coefficientDensitySubspace Y t
  let Kint := LinearMap.ker (D.mkQ.comp f)
  let K := ambientImage C Kint
  let D' := D ⊔ LinearMap.range f
  have hsem := coefficientDensitySubspace_semistable hP X t K
  have hdimNat := finrank_sup_range_sub_eq D f
  have hdimK : sfinrank k K = finrank k Kint := by
    exact finrank_ambientImage C Kint
  have hDle : sfinrank k D ≤ sfinrank k D' :=
    Submodule.finrank_mono le_sup_left
  have hKle : finrank k Kint ≤ finrank k C := Submodule.finrank_le _
  have hdim :
      (sfinrank k D' : ℚ) - sfinrank k D =
        (finrank k C : ℚ) - sfinrank k K := by
    calc
      (sfinrank k D' : ℚ) - sfinrank k D =
          ((sfinrank k D' - sfinrank k D : ℕ) : ℚ) := by
        rw [Nat.cast_sub hDle]
      _ = ((finrank k C - finrank k Kint : ℕ) : ℚ) := by rw [hdimNat]
      _ = (finrank k C : ℚ) - finrank k Kint := by rw [Nat.cast_sub hKle]
      _ = (finrank k C : ℚ) - sfinrank k K := by rw [hdimK]
  have htargetGain :
      t * ((sfinrank k D' : ℚ) - sfinrank k D) ≤
        (coefficientRank Y D' : ℚ) - coefficientRank Y D := by
    calc
      t * ((sfinrank k D' : ℚ) - sfinrank k D) =
          t * ((finrank k C : ℚ) - sfinrank k K) := by rw [hdim]
      _ ≤ (coefficientRank X C : ℚ) - coefficientRank X K := hsem
      _ ≤ (coefficientRank Y D' : ℚ) - coefficientRank Y D := hgain
  have hscore :
      (coefficientRank Y D : ℚ) - t * sfinrank k D ≤
        (coefficientRank Y D' : ℚ) - t * sfinrank k D' := by
    linarith [htargetGain]
  have hD'le : D' ≤ D :=
    coefficientDensitySubspace_largest hP Y t D' hscore
  exact le_trans le_sup_right hD'le

/-- Natural-number version of the codimension-one density step, convenient
when the rank gain has been obtained from an injection of quotient spaces. -/
theorem coefficientDensity_codimOne_of_rank_gain_nat
    [FiniteDimensional k P]
    {R S : Type*}
    [AddCommGroup R] [Module k R] [FiniteDimensional k R]
    [AddCommGroup S] [Module k S] [FiniteDimensional k S]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (t : ℚ)
    (f : coefficientDensitySubspace X t →ₗ[k] S)
    (hgain :
      coefficientRank X (coefficientDensitySubspace X t) -
          coefficientRank X
            (ambientImage (coefficientDensitySubspace X t)
              (LinearMap.ker
                ((coefficientDensitySubspace Y t).mkQ.comp f))) ≤
        coefficientRank Y
            (coefficientDensitySubspace Y t ⊔ LinearMap.range f) -
          coefficientRank Y (coefficientDensitySubspace Y t)) :
    LinearMap.range f ≤ coefficientDensitySubspace Y t := by
  apply coefficientDensity_codimOne_of_rank_gain hP X Y t f
  let C := coefficientDensitySubspace X t
  let D := coefficientDensitySubspace Y t
  let K := ambientImage C (LinearMap.ker (D.mkQ.comp f))
  let D' := D ⊔ LinearMap.range f
  have hKC : K ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hDD' : D ≤ D' := le_sup_left
  have hrankKC : coefficientRank X K ≤ coefficientRank X C := by
    exact Submodule.finrank_mono
      (inf_le_inf le_rfl (tensorSubspace_mono (W := P) hKC))
  have hrankDD' : coefficientRank Y D ≤ coefficientRank Y D' := by
    exact Submodule.finrank_mono
      (inf_le_inf le_rfl (tensorSubspace_mono (W := P) hDD'))
  rw [← Nat.cast_sub hrankKC, ← Nat.cast_sub hrankDD']
  exact_mod_cast hgain

/-- The coefficient-density codimension-one step in the form directly
supplied by the triangular-action injection. -/
theorem coefficientDensity_codimOne_of_internal_map
    [FiniteDimensional k P]
    {R S : Type*}
    [AddCommGroup R] [Module k R] [FiniteDimensional k R]
    [AddCommGroup S] [Module k S] [FiniteDimensional k S]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (t : ℚ)
    (f : coefficientDensitySubspace X t →ₗ[k] S)
    (T : (X ⊓ tensorSubspace (k := k) P
          (coefficientDensitySubspace X t) : Submodule k (P ⊗[k] R)) →ₗ[k]
      (Y ⊓ tensorSubspace (k := k) P
          (coefficientDensitySubspace Y t ⊔ LinearMap.range f) :
            Submodule k (P ⊗[k] S)))
    (hkerT : LinearMap.ker
        (((Y ⊓ tensorSubspace (k := k) P
              (coefficientDensitySubspace Y t)).comap
            (Y ⊓ tensorSubspace (k := k) P
              (coefficientDensitySubspace Y t ⊔ LinearMap.range f)).subtype).mkQ.comp T) ≤
      (X ⊓ tensorSubspace (k := k) P
          (ambientImage (coefficientDensitySubspace X t)
            (LinearMap.ker
              ((coefficientDensitySubspace Y t).mkQ.comp f)))).comap
        (X ⊓ tensorSubspace (k := k) P
          (coefficientDensitySubspace X t)).subtype) :
    LinearMap.range f ≤ coefficientDensitySubspace Y t := by
  apply coefficientDensity_codimOne_of_rank_gain_nat hP X Y t f
  refine coefficientRank_sub_le_coefficientRank_sub_of_ker_le
    X Y
    (ambientImage (coefficientDensitySubspace X t)
      (LinearMap.ker ((coefficientDensitySubspace Y t).mkQ.comp f)))
    (coefficientDensitySubspace X t)
    (coefficientDensitySubspace Y t)
    (coefficientDensitySubspace Y t ⊔ LinearMap.range f) ?_ ?_ T ?_
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact le_sup_left
  · exact hkerT

/-- A tensor subspace is linearly equivalent to its ambient image. -/
noncomputable def ambientTensorImageEquiv
    (P : Submodule k M) (R : Submodule k Q)
    (X : Submodule k (P ⊗[k] R)) :
    X ≃ₗ[k] ambientTensorImage P R X := by
  let f : X →ₗ[k] ambientTensorImage P R X :=
    (TensorProduct.mapIncl P R).domRestrict X |>.codRestrict
      (ambientTensorImage P R X) fun x => ⟨x, x.2, rfl⟩
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact (TensorProduct.map_injective_of_flat_flat
      P.subtype R.subtype P.subtype_injective R.subtype_injective)
      (congrArg Subtype.val hxy)
  · rintro ⟨z, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

@[simp]
theorem coe_ambientTensorImageEquiv_apply
    (P : Submodule k M) (R : Submodule k Q)
    (X : Submodule k (P ⊗[k] R)) (x : X) :
    ((ambientTensorImageEquiv P R X x : ambientTensorImage P R X) :
      M ⊗[k] Q) = TensorProduct.mapIncl P R x :=
  rfl

/-- A tensor subspace supported on `P ⊗ R`, pulled back to that finite
tensor product. -/
def internalTensorSubspace
    (P : Submodule k M) (R : Submodule k Q)
    (Z : Submodule k (M ⊗[k] Q)) : Submodule k (P ⊗[k] R) :=
  Z.comap (TensorProduct.mapIncl P R)

/-- Internalization recovers a tensor subspace known to have the prescribed
finite support. -/
theorem ambientTensorImage_internalTensorSubspace
    (P : Submodule k M) (R : Submodule k Q)
    (Z : Submodule k (M ⊗[k] Q))
    (hZ : Z ≤ LinearMap.range (TensorProduct.mapIncl P R)) :
    ambientTensorImage P R (internalTensorSubspace P R Z) = Z :=
  Submodule.map_comap_eq_self hZ

/-- Enlarging either finite support subspace enlarges the range of the
corresponding tensor inclusion. -/
theorem range_mapIncl_mono
    {P P' : Submodule k M} {R R' : Submodule k Q}
    (hP : P ≤ P') (hR : R ≤ R') :
    LinearMap.range (TensorProduct.mapIncl P R) ≤
      LinearMap.range (TensorProduct.mapIncl P' R') := by
  rintro _ ⟨z, rfl⟩
  let iP : P →ₗ[k] P' :=
    LinearMap.codRestrict P' P.subtype (fun p => hP p.2)
  let iR : R →ₗ[k] R' :=
    LinearMap.codRestrict R' R.subtype (fun r => hR r.2)
  refine ⟨TensorProduct.map iP iR z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul p r => rfl

/-- The diagonal action restricted between two finite tensor subspaces. -/
noncomputable def diagonalActionInternal
    (P : Submodule k M) (R S : Submodule k Q)
    (X : Submodule k (P ⊗[k] R)) (Y : Submodule k (P ⊗[k] S))
    (a : H)
    (ha : ∀ x : X,
      diagonalHopfActionBy (k := k) (H := H) a
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P S Y) :
    X →ₗ[k] Y :=
  (ambientTensorImageEquiv P S Y).symm.toLinearMap.comp
    ((diagonalHopfActionBy (k := k) (H := H) a).comp
      ((TensorProduct.mapIncl P R).domRestrict X) |>.codRestrict
        (ambientTensorImage P S Y) ha)

theorem diagonalActionInternal_ambient
    (P : Submodule k M) (R S : Submodule k Q)
    (X : Submodule k (P ⊗[k] R)) (Y : Submodule k (P ⊗[k] S))
    (a : H)
    (ha : ∀ x : X,
      diagonalHopfActionBy (k := k) (H := H) a
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P S Y)
    (x : X) :
    TensorProduct.mapIncl P S (diagonalActionInternal P R S X Y a ha x) =
      diagonalHopfActionBy (k := k) (H := H) a
        (TensorProduct.mapIncl P R x) := by
  change (((ambientTensorImageEquiv P S Y)
    ((ambientTensorImageEquiv P S Y).symm _)) : M ⊗[k] Q) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 800000 in
-- The nested tensor exactness calculation requires extra elaboration time.
/-- The coefficient-density inclusion for one codimension-one step of a
complete subcoalgebra flag.  This is the formal version of the triangular
coproduct injection in the proof of Theorem B. -/
theorem coefficientDensity_codimOne
    [Coalgebra.IsCocomm k H]
    (A' A : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1)
    (P : Submodule k M) (R S : Submodule k Q)
    [FiniteDimensional k P] [FiniteDimensional k R] [FiniteDimensional k S]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (hdiag : ∀ (a : A.carrier) (x : X),
      diagonalHopfActionBy (k := k) (H := H) (a : H)
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P S Y)
    (hact : ∀ (a : A.carrier) (r : R),
      (a : H) • (r : Q) ∈ S)
    (t : ℚ)
    (hlower : actionSubspace A'.carrier
        (ambientImage R (coefficientDensitySubspace X t)) ≤
      ambientImage S (coefficientDensitySubspace Y t)) :
    actionSubspace A.carrier
        (ambientImage R (coefficientDensitySubspace X t)) ≤
      ambientImage S (coefficientDensitySubspace Y t) := by
  obtain ⟨ell, a, hker, ha⟩ :=
    exists_normalized_codimOne_functional A' A hAA hdim
  let C := coefficientDensitySubspace X t
  let D := coefficientDensitySubspace Y t
  have haC : ∀ c : C, (a : H) • ((c : R) : Q) ∈ S :=
    fun c => hact a c
  let f : C →ₗ[k] S := actionBetweenSubspaces (k := k) (a : H) R S C haC
  let D' : Submodule k S := D ⊔ LinearMap.range f
  let XC : Submodule k (P ⊗[k] R) := X ⊓ tensorSubspace (k := k) P C
  let YD' : Submodule k (P ⊗[k] S) := Y ⊓ tensorSubspace (k := k) P D'
  have htarget : ∀ x : XC,
      ((diagonalActionInternal P R S X Y (a : H) (hdiag a)
        (⟨x.1, x.2.1⟩ : X) : Y) : P ⊗[k] S) ∈ YD' := by
    intro x
    let xX : X := ⟨x.1, x.2.1⟩
    have hxC : (x.1 : P ⊗[k] R) ∈ tensorSubspace (k := k) P C := x.2.2
    let xC : tensorSubspace (k := k) P C := ⟨x.1, hxC⟩
    let zC : P ⊗[k] C := (tensorSubspaceEquiv (k := k) (P := P) C).symm xC
    let Cbar : Submodule k Q := ambientImage R C
    let Dbar' : Submodule k Q := ambientImage S D'
    let zbar : P ⊗[k] Cbar :=
      TensorProduct.map LinearMap.id (ambientImageEquiv R C).toLinearMap zC
    have hlower' : ∀ (y : codimOneLower A' A) (c : Cbar),
        (y.1 : H) • (c : Q) ∈ Dbar' := by
      intro y c
      have hyA' : (y.1 : H) ∈ A'.carrier := y.2
      have hcC : (c : Q) ∈ ambientImage R C := c.2
      exact Submodule.map_mono (le_sup_left : D ≤ D')
        (hlower (product_mem_actionSubspace hyA' hcC))
    have hφzero :
        (Dbar'.mkQ.comp
          (actionOnSubspace (k := k) (a : H) Cbar)) = 0 := by
      apply LinearMap.ext
      intro c
      apply (Submodule.Quotient.mk_eq_zero Dbar').2
      rcases c.2 with ⟨r, hr, hrc⟩
      let cr : C := ⟨r, hr⟩
      have hvalue : (a : H) • (c : Q) = (f cr : S) := by
        exact congrArg (fun q : Q => (a : H) • q) hrc.symm
      change (a : H) • (c : Q) ∈ Dbar'
      rw [hvalue]
      exact ⟨f cr, Submodule.mem_sup_right ⟨cr, rfl⟩, rfl⟩
    have hquot := quotient_diagonalSubcoalgebraAction_codimOne
      A' A hAA ell a hker ha P Cbar Dbar' hlower' zbar
    have hquotZero : (Dbar'.mkQ.lTensor M)
        (diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a
          (TensorProduct.mapIncl P Cbar zbar)) = 0 := by
      rw [hquot, hφzero]
      simp
    have hsource : TensorProduct.mapIncl P Cbar zbar =
        TensorProduct.mapIncl P R (x.1 : P ⊗[k] R) := by
      dsimp [zbar, zC, xC]
      exact (mapIncl_tensorSubspaceEquiv_symm_ambient P R C
        ⟨x.1, hxC⟩).symm
    have hambientEq : TensorProduct.mapIncl P S
        (diagonalActionInternal P R S X Y (a : H) (hdiag a) xX) =
      diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a
        (TensorProduct.mapIncl P Cbar zbar) := by
      rw [hsource, diagonalSubcoalgebraActionBy_eq]
      exact diagonalActionInternal_ambient P R S X Y (a : H)
        (hdiag a) xX
    have hambientMem : TensorProduct.mapIncl P S
        (diagonalActionInternal P R S X Y (a : H) (hdiag a) xX) ∈
          tensorSubspace (k := k) M Dbar' := by
      change _ ∈ LinearMap.range (Dbar'.subtype.lTensor M)
      rw [range_subtype_lTensor_eq_ker_mkQ_lTensor, LinearMap.mem_ker,
        hambientEq]
      exact hquotZero
    refine ⟨(diagonalActionInternal P R S X Y (a : H) (hdiag a) xX).2,
      ?_⟩
    exact (mapIncl_mem_tensorSubspace_ambient_iff P S D'
      (diagonalActionInternal P R S X Y (a : H) (hdiag a) xX)).1 hambientMem
  let XCtoX : XC →ₗ[k] X :=
    LinearMap.codRestrict X XC.subtype (fun x => x.2.1)
  let T : XC →ₗ[k] YD' :=
    (Y.subtype.comp
      ((diagonalActionInternal P R S X Y (a : H) (hdiag a)).comp XCtoX)).codRestrict
        YD' (fun x => htarget x)
  let XK : Submodule k XC :=
    (X ⊓ tensorSubspace (k := k) P
      (ambientImage C (LinearMap.ker (D.mkQ.comp f)))).comap XC.subtype
  have hpreimage : ∀ x : XC,
      (T x : P ⊗[k] S) ∈ Y ⊓ tensorSubspace (k := k) P D → x ∈ XK := by
    intro x hTxSmall
    let xX : X := ⟨x.1, x.2.1⟩
    have hxC : (x.1 : P ⊗[k] R) ∈ tensorSubspace (k := k) P C := x.2.2
    let xC : tensorSubspace (k := k) P C := ⟨x.1, hxC⟩
    let zC : P ⊗[k] C := (tensorSubspaceEquiv (k := k) (P := P) C).symm xC
    let Cbar : Submodule k Q := ambientImage R C
    let Dbar : Submodule k Q := ambientImage S D
    let zbar : P ⊗[k] Cbar :=
      TensorProduct.map LinearMap.id (ambientImageEquiv R C).toLinearMap zC
    have hlowerD : ∀ (y : codimOneLower A' A) (c : Cbar),
        (y.1 : H) • (c : Q) ∈ Dbar := by
      intro y c
      exact hlower (product_mem_actionSubspace y.2 c.2)
    have hsource : TensorProduct.mapIncl P Cbar zbar =
        TensorProduct.mapIncl P R (x.1 : P ⊗[k] R) := by
      dsimp [zbar, zC, xC]
      exact (mapIncl_tensorSubspaceEquiv_symm_ambient P R C
        ⟨x.1, hxC⟩).symm
    have hdiagMem : diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a
        (TensorProduct.mapIncl P Cbar zbar) ∈
          tensorSubspace (k := k) M Dbar := by
      rw [hsource, diagonalSubcoalgebraActionBy_eq,
        ← diagonalActionInternal_ambient P R S X Y (a : H) (hdiag a) xX]
      apply (mapIncl_mem_tensorSubspace_ambient_iff P S D (T x)).2
      exact hTxSmall.2
    have hdiagZero : (Dbar.mkQ.lTensor M)
        (diagonalSubcoalgebraActionBy (M := M) (Q := Q) A a
          (TensorProduct.mapIncl P Cbar zbar)) = 0 := by
      change _ ∈ LinearMap.ker (Dbar.mkQ.lTensor M)
      rw [← range_subtype_lTensor_eq_ker_mkQ_lTensor]
      exact hdiagMem
    have hquot := quotient_diagonalSubcoalgebraAction_codimOne
      A' A hAA ell a hker ha P Cbar Dbar hlowerD zbar
    let gP : P →ₗ[k] M :=
      (Algebra.lsmul k k M
        ((codimOneGroupLikeCandidate A ell a : A.carrier) : H)).comp P.subtype
    have hgP : Function.Injective gP :=
      (groupLike_action_injective
        (codimOneGroupLikeCandidate_isGroupLike_ambient
          A' A hAA ell a hker ha)).comp P.injective_subtype
    have hambientKernel :
        (((Dbar.mkQ.comp (actionOnSubspace (k := k) (a : H) Cbar)).lTensor P)
          zbar) = 0 := by
      apply (Module.Flat.rTensor_preserves_injective_linearMap gP hgP)
      rw [← hquot]
      exact hdiagZero
    have hinternalKernel :
        (((D.mkQ.comp f).lTensor P) zC) = 0 := by
      have hnat := quotient_actionBetweenSubspaces_natural
        (M := M) (a : H) P R S C D haC zC
      have hqzero : (ambientQuotientMap S D).lTensor P
          (((D.mkQ.comp f).lTensor P) zC) = 0 := by
        rw [← hnat]
        exact hambientKernel
      exact (Module.Flat.lTensor_preserves_injective_linearMap
        (ambientQuotientMap S D) (ambientQuotientMap_injective S D))
          (hqzero.trans (map_zero _).symm)
    have hzCrange : zC ∈ LinearMap.range
        ((LinearMap.ker (D.mkQ.comp f)).subtype.lTensor P) := by
      let φ := D.mkQ.comp f
      apply mem_range_ker_lTensor_of_rTensor_eq_zero
        (LinearMap.id (R := k) (M := P)) Function.injective_id φ zC
      simpa [φ] using hinternalKernel
    have hxK : (x.1 : P ⊗[k] R) ∈ tensorSubspace (k := k) P
        (ambientImage C (LinearMap.ker (D.mkQ.comp f))) := by
      dsimp [zC, xC] at hzCrange ⊢
      have hmem := tensorSubspaceEquiv_mem_ambientImage C
        (LinearMap.ker (D.mkQ.comp f))
        ((tensorSubspaceEquiv (k := k) (P := P) C).symm ⟨x.1, hxC⟩) hzCrange
      simpa using hmem
    exact ⟨x.2.1, hxK⟩
  have hrange : LinearMap.range f ≤ D := by
    apply coefficientDensity_codimOne_of_internal_map hP X Y t f T
    intro x hx
    apply hpreimage x
    have hx0 := (LinearMap.mem_ker).1 hx
    have hxmem := (Submodule.Quotient.mk_eq_zero _).1 hx0
    exact hxmem
  rw [actionSubspace_eq_map₂, Submodule.map₂_le]
  intro b hbA c hcC
  have hbdecomp : (b : H) - ell ⟨b, hbA⟩ • (a : H) ∈ A'.carrier := by
    have hlow : (⟨b, hbA⟩ : A.carrier) - ell ⟨b, hbA⟩ • a ∈
        codimOneLower A' A := by
      rw [← hker, LinearMap.mem_ker]
      simp [ha]
    exact hlow
  have hc : ∃ cR : C, ((cR : R) : Q) = c := by
    rcases hcC with ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  rcases hc with ⟨cR, rfl⟩
  have hlowerTerm : ((b : H) - ell ⟨b, hbA⟩ • (a : H)) • ((cR : R) : Q) ∈
      ambientImage S D :=
    hlower (product_mem_actionSubspace hbdecomp
      (show ((cR : R) : Q) ∈ ambientImage R C from
        ⟨(cR : R), cR.2, rfl⟩))
  have haTerm : (a : H) • ((cR : R) : Q) ∈ ambientImage S D := by
    have hfD : f cR ∈ D := hrange ⟨cR, rfl⟩
    exact ⟨f cR, hfD, rfl⟩
  have hsum := (ambientImage S D).add_mem hlowerTerm
    ((ambientImage S D).smul_mem (ell ⟨b, hbA⟩) haTerm)
  convert hsum using 1
  change b • ((cR : R) : Q) =
    (b - ell ⟨b, hbA⟩ • (a : H)) • ((cR : R) : Q) +
      ell ⟨b, hbA⟩ • ((a : H) • ((cR : R) : Q))
  rw [sub_smul, smul_assoc]
  abel

/-- Pointwise coefficient-density transfer along a complete subcoalgebra
flag. -/
theorem coefficientDensity_transfer_of_completeFlag
    [Coalgebra.IsCocomm k H]
    (A : FiniteSubcoalgebra k H)
    (hflag : PrimalTransfer.HasCompleteSubcoalgebraFlag A)
    (P : Submodule k M) (R S : Submodule k Q)
    [FiniteDimensional k P] [FiniteDimensional k R] [FiniteDimensional k S]
    (hP : 0 < finrank k P)
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (hdiag : ∀ (a : A.carrier) (x : X),
      diagonalHopfActionBy (k := k) (H := H) (a : H)
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P S Y)
    (hact : ∀ (a : A.carrier) (r : R),
      (a : H) • (r : Q) ∈ S)
    (t : ℚ) :
    actionSubspace A.carrier
        (ambientImage R (coefficientDensitySubspace X t)) ≤
      ambientImage S (coefficientDensitySubspace Y t) := by
  induction hflag with
  | @bot A₀ hA₀ =>
      rw [hA₀, actionSubspace_bot_left]
      exact bot_le
  | @step A' A₀ hflag hAA hdim ih =>
      apply coefficientDensity_codimOne A' A₀ hAA hdim P R S hP X Y
        hdiag hact t
      apply ih
      · intro a x
        exact hdiag ⟨a, hAA a.2⟩ x
      · intro a r
        exact hact ⟨a, hAA a.2⟩ r

/-- Coefficient-density transfer when the acting operator changes only the
coefficient factor.  This is the linear-algebra input for descent from a
finite scalar extension. -/
theorem coefficientDensity_secondFactor_transfer
    (F : Submodule k H)
    (P₀ : Type*) [AddCommGroup P₀] [Module k P₀] [FiniteDimensional k P₀]
    (R S : Submodule k Q)
    [FiniteDimensional k R] [FiniteDimensional k S]
    (hP₀ : 0 < finrank k P₀)
    (X : Submodule k (P₀ ⊗[k] R))
    (Y : Submodule k (P₀ ⊗[k] S))
    (hact : ∀ (a : F) (r : R), (a : H) • (r : Q) ∈ S)
    (hXY : ∀ (a : F) (x : X),
      TensorProduct.map LinearMap.id
        (actionFromSubspace (k := k) (a : H) R S (fun r => hact a r))
        (x : P₀ ⊗[k] R) ∈ Y)
    (t : ℚ) :
    actionSubspace F
        (ambientImage R (coefficientDensitySubspace X t)) ≤
      ambientImage S (coefficientDensitySubspace Y t) := by
  let C := coefficientDensitySubspace X t
  let D := coefficientDensitySubspace Y t
  rw [actionSubspace_eq_map₂, Submodule.map₂_le]
  intro a ha c hc
  let aF : F := ⟨a, ha⟩
  have haC : ∀ c : C, (a : H) • ((c : R) : Q) ∈ S :=
    fun c => hact aF c
  let f : C →ₗ[k] S :=
    actionBetweenSubspaces (k := k) a R S C haC
  let D' : Submodule k S := D ⊔ LinearMap.range f
  let XC : Submodule k (P₀ ⊗[k] R) :=
    X ⊓ tensorSubspace (k := k) P₀ C
  let YD' : Submodule k (P₀ ⊗[k] S) :=
    Y ⊓ tensorSubspace (k := k) P₀ D'
  let actR : R →ₗ[k] S :=
    actionFromSubspace (k := k) a R S (fun r => hact aF r)
  let T₀ : XC →ₗ[k] P₀ ⊗[k] S :=
    (TensorProduct.map LinearMap.id actR).comp XC.subtype
  have htarget : ∀ x : XC, T₀ x ∈ YD' := by
    intro x
    have hxC : (x.1 : P₀ ⊗[k] R) ∈ tensorSubspace (k := k) P₀ C := x.2.2
    let xC : tensorSubspace (k := k) P₀ C := ⟨x.1, hxC⟩
    let zC : P₀ ⊗[k] C :=
      (tensorSubspaceEquiv (k := k) (P := P₀) C).symm xC
    have hmap : T₀ x = TensorProduct.map LinearMap.id f zC := by
      have hxrepr : C.subtype.lTensor P₀ zC = (x.1 : P₀ ⊗[k] R) := by
        exact congrArg Subtype.val
          ((tensorSubspaceEquiv (k := k) (P := P₀) C).apply_symm_apply xC)
      dsimp [T₀]
      rw [← hxrepr]
      induction zC using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
      | tmul p c => rfl
    refine ⟨?_, ?_⟩
    · exact hXY aF ⟨x.1, x.2.1⟩
    · rw [hmap]
      refine ⟨TensorProduct.map LinearMap.id
        (LinearMap.codRestrict D' f (fun c =>
          Submodule.mem_sup_right ⟨c, rfl⟩)) zC, ?_⟩
      induction zC using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
      | tmul p c => rfl
  let T : XC →ₗ[k] YD' := LinearMap.codRestrict YD' T₀ htarget
  let XK : Submodule k XC :=
    (X ⊓ tensorSubspace (k := k) P₀
      (ambientImage C (LinearMap.ker (D.mkQ.comp f)))).comap XC.subtype
  have hpreimage : ∀ x : XC,
      (T x : P₀ ⊗[k] S) ∈ Y ⊓ tensorSubspace (k := k) P₀ D → x ∈ XK := by
    intro x hx
    have hxC : (x.1 : P₀ ⊗[k] R) ∈ tensorSubspace (k := k) P₀ C := x.2.2
    let xC : tensorSubspace (k := k) P₀ C := ⟨x.1, hxC⟩
    let zC : P₀ ⊗[k] C :=
      (tensorSubspaceEquiv (k := k) (P := P₀) C).symm xC
    have hmap : (T x : P₀ ⊗[k] S) =
        TensorProduct.map LinearMap.id f zC := by
      have hxrepr : C.subtype.lTensor P₀ zC = (x.1 : P₀ ⊗[k] R) := by
        exact congrArg Subtype.val
          ((tensorSubspaceEquiv (k := k) (P := P₀) C).apply_symm_apply xC)
      change T₀ x = _
      dsimp [T₀]
      rw [← hxrepr]
      induction zC using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
      | tmul p c => rfl
    have hzero : ((D.mkQ.comp f).lTensor P₀) zC = 0 := by
      have hxzero : D.mkQ.lTensor P₀ (T x : P₀ ⊗[k] S) = 0 := by
        change (T x : P₀ ⊗[k] S) ∈ LinearMap.ker (D.mkQ.lTensor P₀)
        rw [← range_subtype_lTensor_eq_ker_mkQ_lTensor]
        exact hx.2
      rw [hmap] at hxzero
      have hcomp : ((D.mkQ.comp f).lTensor P₀) zC =
          D.mkQ.lTensor P₀ (TensorProduct.map LinearMap.id f zC) := by
        induction zC using TensorProduct.induction_on with
        | zero => simp
        | add z z' hz hz' =>
            simpa only [map_add] using congrArg₂ (· + ·) hz hz'
        | tmul p c => rfl
      rw [hcomp]
      exact hxzero
    have hzrange : zC ∈ LinearMap.range
        ((LinearMap.ker (D.mkQ.comp f)).subtype.lTensor P₀) := by
      apply mem_range_ker_lTensor_of_rTensor_eq_zero
        (LinearMap.id (R := k) (M := P₀)) Function.injective_id
        (D.mkQ.comp f) zC
      simpa using hzero
    have hxK : (x.1 : P₀ ⊗[k] R) ∈ tensorSubspace (k := k) P₀
        (ambientImage C (LinearMap.ker (D.mkQ.comp f))) := by
      dsimp [zC, xC] at hzrange ⊢
      simpa using tensorSubspaceEquiv_mem_ambientImage C
        (LinearMap.ker (D.mkQ.comp f))
        ((tensorSubspaceEquiv (k := k) (P := P₀) C).symm ⟨x.1, hxC⟩)
        hzrange
    exact ⟨x.2.1, hxK⟩
  have hrange : LinearMap.range f ≤ D := by
    apply coefficientDensity_codimOne_of_internal_map hP₀ X Y t f T
    intro x hx
    apply hpreimage x
    have hxmem := (Submodule.Quotient.mk_eq_zero _).1 ((LinearMap.mem_ker).1 hx)
    exact hxmem
  rcases hc with ⟨r, hr, rfl⟩
  let cr : C := ⟨r, hr⟩
  have hfD : f cr ∈ D := hrange ⟨cr, rfl⟩
  exact ⟨f cr, hfD, rfl⟩

/-- Density averaging for coefficient subspaces, assuming the pointwise
flag-transfer inclusion. -/
theorem exists_coefficient_ratio_le_of_pointwise_transfer
    (A : Submodule k H) [FiniteDimensional k A]
    (P : Type*) [AddCommGroup P] [Module k P] [FiniteDimensional k P]
    (hP : 0 < finrank k P)
    (R S : Submodule k Q)
    [FiniteDimensional k R] [FiniteDimensional k S]
    (X : Submodule k (P ⊗[k] R))
    (Y : Submodule k (P ⊗[k] S))
    (hX : X ≠ ⊥)
    (htransfer : ∀ t : ℚ,
      actionSubspace A
          (ambientImage R (coefficientDensitySubspace X t)) ≤
        ambientImage S (coefficientDensitySubspace Y t)) :
    ∃ t : ℚ,
      coefficientDensitySubspace X t ≠ ⊥ ∧
        (sfinrank k (actionSubspace A
            (ambientImage R (coefficientDensitySubspace X t))) : ℚ) /
              sfinrank k (coefficientDensitySubspace X t) ≤
          (finrank k Y : ℚ) / finrank k X := by
  let sourceFamily : AdmissibleFamily k (P ⊗[k] R) :=
    tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := R)
  let targetFamily : AdmissibleFamily k (P ⊗[k] S) :=
    tensorSubspaceAdmissibleFamily (k := k) (P := P) (Q := S)
  let b : ℚ → ℚ := fun t =>
    (finrank k P : ℚ) *
      sfinrank k (actionSubspace A
        (ambientImage R (coefficientDensitySubspace X
          ((finrank k P : ℚ) * t))))
  have hsourceHull : ∃ Z : Submodule k (P ⊗[k] R),
      sourceFamily.admissible Z ∧ X ≤ Z := by
    exact ⟨⊤, ⟨⊤, tensorSubspace_top.symm⟩, le_top⟩
  have hb0 : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ b t := by
    intro t ht0 ht1
    positivity
  have hb : ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      b t ≤ finrank k (densitySubspace targetFamily Y t) := by
    intro t ht0 ht1
    let Ct : Submodule k R := coefficientDensitySubspace X
      ((finrank k P : ℚ) * t)
    let Dt : Submodule k S := coefficientDensitySubspace Y
      ((finrank k P : ℚ) * t)
    let : FiniteDimensional k (ambientImage R Ct) :=
      FiniteDimensional.of_surjective
        (ambientImageEquiv R Ct).toLinearMap (ambientImageEquiv R Ct).surjective
    let : FiniteDimensional k (ambientImage S Dt) :=
      FiniteDimensional.of_surjective
        (ambientImageEquiv S Dt).toLinearMap (ambientImageEquiv S Dt).surjective
    let : FiniteDimensional k
        (actionSubspace A (ambientImage R Ct)) :=
      finiteDimensional_actionSubspace A (ambientImage R Ct)
    have hle := htransfer ((finrank k P : ℚ) * t)
    have hleInt : actionSubspace A (ambientImage R Ct) ≤
        ambientImage S Dt := hle
    have hdim := Submodule.finrank_mono hleInt
    have hdimQ :
        (sfinrank k (actionSubspace A (ambientImage R Ct)) : ℚ) ≤
          sfinrank k (ambientImage S Dt) := by
      exact_mod_cast hdim
    change (finrank k P : ℚ) *
        (sfinrank k (actionSubspace A (ambientImage R Ct)) : ℚ) ≤
      (finrank k (densitySubspace targetFamily Y t) : ℚ)
    have hparam : coefficientTensorParameter (k := k) P
        ((finrank k P : ℚ) * t) = t := by
      simp only [coefficientTensorParameter]
      field_simp [show (finrank k P : ℚ) ≠ 0 by
        exact_mod_cast (Nat.ne_of_gt hP)]
    have hYtensor : tensorSubspace (k := k) P Dt =
        densitySubspace targetFamily Y t := by
      rw [tensorSubspace_coefficientDensitySubspace]
      exact congrArg (densitySubspace targetFamily Y) hparam
    simp only [sfinrank] at hdimQ
    rw [finrank_ambientImage S] at hdimQ
    rw [← hYtensor]
    change (finrank k P : ℚ) *
        (sfinrank k (actionSubspace A (ambientImage R Ct)) : ℚ) ≤
      (sfinrank k (tensorSubspace (k := k) P Dt) : ℚ)
    rw [sfinrank_tensorSubspace]
    have hdimNat :
        sfinrank k (actionSubspace A (ambientImage R Ct)) ≤
          sfinrank k Dt := by
      exact_mod_cast hdimQ
    exact_mod_cast Nat.mul_le_mul_left (finrank k P) hdimNat
  obtain ⟨u, huBreak, huPos, huRatio⟩ :=
    exists_ratio_le_of_density_filtrations sourceFamily targetFamily
      X Y hX hsourceHull b hb0 hb
  let t : ℚ := (finrank k P : ℚ) * u
  refine ⟨t, ?_, ?_⟩
  · intro hbot
    have hparam : coefficientTensorParameter (k := k) P t = u := by
      dsimp [t, coefficientTensorParameter]
      field_simp [show (finrank k P : ℚ) ≠ 0 by
        exact_mod_cast (Nat.ne_of_gt hP)]
    have hXtensor : tensorSubspace (k := k) P
        (coefficientDensitySubspace X t) =
          densitySubspace sourceFamily X u := by
      dsimp [sourceFamily]
      rw [tensorSubspace_coefficientDensitySubspace, hparam]
    have hzero : finrank k (densitySubspace sourceFamily X u) = 0 := by
      rw [← hXtensor, hbot]
      simp
    exact (Nat.ne_of_gt huPos) hzero
  · change ((finrank k P : ℚ) *
        sfinrank k (actionSubspace A
          (ambientImage R (coefficientDensitySubspace X t)))) /
        finrank k (densitySubspace sourceFamily X u) ≤
      (finrank k Y : ℚ) / finrank k X at huRatio
    have hparam : coefficientTensorParameter (k := k) P t = u := by
      dsimp [t, coefficientTensorParameter]
      field_simp [show (finrank k P : ℚ) ≠ 0 by
        exact_mod_cast (Nat.ne_of_gt hP)]
    have hXtensor : tensorSubspace (k := k) P
        (coefficientDensitySubspace X t) =
          densitySubspace sourceFamily X u := by
      dsimp [sourceFamily]
      rw [tensorSubspace_coefficientDensitySubspace, hparam]
    have hsourceDim : finrank k (densitySubspace sourceFamily X u) =
        finrank k P * sfinrank k (coefficientDensitySubspace X t) := by
      rw [← hXtensor]
      exact sfinrank_tensorSubspace (k := k) (W := P)
        (coefficientDensitySubspace X t)
    rw [hsourceDim, Nat.cast_mul] at huRatio
    have hPq : (finrank k P : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hP)
    simpa [mul_div_mul_left _ _ hPq] using huRatio

set_option maxHeartbeats 800000 in
-- The finite-envelope descent argument contains several nested subspace coercions.
/-- Descent of Følner ratios through a finite scalar extension.  This is
Lemma `folner-descent` in the article. -/
theorem exists_action_ratio_le_of_finite_extension
    {K : Type*} [Field K] [Algebra k K] [FiniteDimensional k K]
    (F : Submodule k H) [FiniteDimensional k F]
    (V : Submodule K (K ⊗[k] Q)) [FiniteDimensional K V]
    (hV : V ≠ ⊥) :
    ∃ U : Submodule k Q,
      U ≠ ⊥ ∧ FiniteDimensional k U ∧
        (sfinrank k (actionSubspace F U) : ℚ) / sfinrank k U ≤
          (sfinrank K
            (actionSubspace (baseChangeSubspace (k := k) K F) V) : ℚ) /
            sfinrank K V := by
  let FK : Submodule K (K ⊗[k] H) := baseChangeSubspace (k := k) K F
  let : FiniteDimensional K FK := by
    let g := F.subtype.baseChange K
    exact FiniteDimensional.of_surjective g.rangeRestrict (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)
  let W : Submodule K (K ⊗[k] Q) := actionSubspace FK V
  let : FiniteDimensional K W := finiteDimensional_actionSubspace FK V
  let X₀ : Submodule k (K ⊗[k] Q) := V.restrictScalars k
  let Y₀ : Submodule k (K ⊗[k] Q) := W.restrictScalars k
  let Z : Submodule k (K ⊗[k] Q) := X₀ ⊔ Y₀
  let : Module.Finite K X₀ :=
    Module.Finite.equiv (V.restrictScalarsEquiv k K).symm
  let : Module.Finite k X₀ := Module.Finite.trans K X₀
  let : Module.Finite K Y₀ :=
    Module.Finite.equiv (W.restrictScalarsEquiv k K).symm
  let : Module.Finite k Y₀ := Module.Finite.trans K Y₀
  let : FiniteDimensional k X₀ := by
    dsimp [X₀]
    infer_instance
  let : FiniteDimensional k Y₀ := by
    dsimp [Y₀]
    infer_instance
  let : FiniteDimensional k Z := by
    dsimp [Z]
    infer_instance
  obtain ⟨P, R, hPfd, hRfd, hZsupport⟩ :=
    exists_finite_tensor_envelope Z
  let : FiniteDimensional k P := hPfd
  let : FiniteDimensional k R := hRfd
  let S : Submodule k Q := R ⊔ actionSubspace F R
  let : FiniteDimensional k S := by
    dsimp [S]
    infer_instance
  have hXsupport : X₀ ≤ LinearMap.range (TensorProduct.mapIncl P R) :=
    le_trans le_sup_left hZsupport
  have hYsupportR : Y₀ ≤ LinearMap.range (TensorProduct.mapIncl P R) :=
    le_trans le_sup_right hZsupport
  have hYsupport : Y₀ ≤ LinearMap.range (TensorProduct.mapIncl P S) :=
    hYsupportR.trans (range_mapIncl_mono le_rfl le_sup_left)
  let X : Submodule k (P ⊗[k] R) := internalTensorSubspace P R X₀
  let Y : Submodule k (P ⊗[k] S) := internalTensorSubspace P S Y₀
  have hXimage : ambientTensorImage P R X = X₀ :=
    ambientTensorImage_internalTensorSubspace P R X₀ hXsupport
  have hYimage : ambientTensorImage P S Y = Y₀ :=
    ambientTensorImage_internalTensorSubspace P S Y₀ hYsupport
  have hX₀ne : X₀ ≠ ⊥ := by
    intro hbot
    apply hV
    ext z
    constructor
    · intro hz
      have : z ∈ X₀ := hz
      rw [hbot] at this
      simpa using this
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      exact zero_mem V
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hX₀ne
    rw [← hXimage, hbot]
    exact Submodule.map_bot _
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hX₀ne
    rw [← hXimage]
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [map_add] using add_mem hz hz'
      | tmul p r =>
          have hp : (p : K) = 0 := by
            have hpbot : (p : K) ∈ (⊥ : Submodule k K) := by
              rw [← hPbot]
              exact p.2
            simpa using hpbot
          rw [show TensorProduct.mapIncl P R (p ⊗ₜ[k] r) =
              (p : K) ⊗ₜ[k] (r : Q) from rfl, hp, zero_tmul]
          exact zero_mem _
    · exact bot_le
  let : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hPne
  have hPpos : 0 < finrank k P := Module.finrank_pos
  have hact : ∀ (a : F) (r : R), (a : H) • (r : Q) ∈ S := by
    intro a r
    exact Submodule.mem_sup_right (product_mem_actionSubspace a.2 r.2)
  have hXY : ∀ (a : F) (x : X),
      TensorProduct.map LinearMap.id
        (actionFromSubspace (k := k) (a : H) R S (fun r => hact a r))
          (x : P ⊗[k] R) ∈ Y := by
    intro a x
    change TensorProduct.mapIncl P S
      (TensorProduct.map LinearMap.id
        (actionFromSubspace (k := k) (a : H) R S (fun r => hact a r)) x) ∈ Y₀
    have hx₀ : TensorProduct.mapIncl P R x ∈ X₀ := by
      rw [← hXimage]
      exact ⟨x, x.2, rfl⟩
    have hsecond : TensorProduct.mapIncl P S
        (TensorProduct.map LinearMap.id
          (actionFromSubspace (k := k) (a : H) R S (fun r => hact a r)) x) =
      ((1 : K) ⊗ₜ[k] (a : H) : K ⊗[k] H) •
        TensorProduct.mapIncl P R x := by
      induction (x : P ⊗[k] R) using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' =>
          simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz hz'
      | tmul p r => simp [baseChange_smul_tmul]
    rw [hsecond]
    exact product_mem_actionSubspace
      (show ((1 : K) ⊗ₜ[k] (a : H) : K ⊗[k] H) ∈ FK from
        ⟨(1 : K) ⊗ₜ[k] a, rfl⟩) hx₀
  have htransfer : ∀ t : ℚ,
      actionSubspace F (ambientImage R (coefficientDensitySubspace X t)) ≤
        ambientImage S (coefficientDensitySubspace Y t) :=
    fun t => coefficientDensity_secondFactor_transfer
      F P R S hPpos X Y hact hXY t
  obtain ⟨t, hCt, hratio⟩ :=
    exists_coefficient_ratio_le_of_pointwise_transfer
      F P hPpos R S X Y hXne htransfer
  let U : Submodule k Q := ambientImage R (coefficientDensitySubspace X t)
  let : FiniteDimensional k U :=
    FiniteDimensional.of_surjective
      (ambientImageEquiv R (coefficientDensitySubspace X t)).toLinearMap
      (ambientImageEquiv R (coefficientDensitySubspace X t)).surjective
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hCt
    rw [eq_bot_iff]
    intro c hc
    have : ((c : R) : Q) ∈ U := ⟨c, hc, rfl⟩
    rw [hbot] at this
    exact Subtype.ext (by simpa using this)
  have hdimX : finrank k X = finrank k K * finrank K V := by
    calc
      finrank k X = finrank k (ambientTensorImage P R X) :=
        (ambientTensorImageEquiv P R X).finrank_eq
      _ = sfinrank k X₀ := by rw [hXimage]
      _ = finrank k K * finrank K V := sfinrank_restrictScalars V
  have hdimY : finrank k Y = finrank k K * finrank K W := by
    calc
      finrank k Y = finrank k (ambientTensorImage P S Y) :=
        (ambientTensorImageEquiv P S Y).finrank_eq
      _ = sfinrank k Y₀ := by rw [hYimage]
      _ = finrank k K * finrank K W := sfinrank_restrictScalars W
  refine ⟨U, hUne, inferInstance, ?_⟩
  rw [show sfinrank k U = sfinrank k (coefficientDensitySubspace X t) by
    exact finrank_ambientImage R (coefficientDensitySubspace X t)]
  have hd : (finrank k K : ℚ) ≠ 0 := by
    exact_mod_cast (show finrank k K ≠ 0 from
      Nat.ne_of_gt (Module.finrank_pos (R := k) (M := K)))
  rw [hdimX, hdimY, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ hd] at hratio
  exact hratio

end TensorSubspaceLattice

section Coalgebra

variable [Coalgebra k M] [Coalgebra k Q]

/-- The right `Q`-coaction on `M` induced by a coalgebra morphism `M → Q`. -/
def coactionAlong (q : M →ₗc[k] Q) : M →ₗ[k] M ⊗[k] Q :=
  q.toLinearMap.lTensor M ∘ₗ Coalgebra.comul

theorem coactionAlong_apply (q : M →ₗc[k] Q) (m : M) :
    coactionAlong q m =
      q.toLinearMap.lTensor M (Coalgebra.comul (R := k) (A := M) m) :=
  rfl

/-- The coaction induced by a counital coalgebra morphism is injective. -/
theorem coactionAlong_injective (q : M →ₗc[k] Q) :
    Function.Injective (coactionAlong q) := by
  intro m m' hmm'
  have hcontract : ∀ x : M,
      TensorProduct.rid k M
          ((Coalgebra.counit (R := k) (A := Q)).lTensor M
            (coactionAlong q x)) = x := by
    intro x
    have hnatural : ∀ z : M ⊗[k] M,
        (Coalgebra.counit (R := k) (A := Q)).lTensor M
            (q.toLinearMap.lTensor M z) =
          (Coalgebra.counit (R := k) (A := M)).lTensor M z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' =>
          simpa only [map_add] using congrArg₂ (fun a b => a + b) hz hz'
      | tmul a b =>
          simp only [LinearMap.lTensor_tmul]
          have hq := CoalgHomClass.counit_comp_apply q b
          change Coalgebra.counit (R := k) (A := Q) (q.toLinearMap b) =
            Coalgebra.counit (R := k) (A := M) b at hq
          rw [hq]
    rw [coactionAlong_apply, hnatural,
      Coalgebra.lTensor_counit_comul]
    simp
  calc
    m = TensorProduct.rid k M
        ((Coalgebra.counit (R := k) (A := Q)).lTensor M
          (coactionAlong q m)) := (hcontract m).symm
    _ = TensorProduct.rid k M
        ((Coalgebra.counit (R := k) (A := Q)).lTensor M
          (coactionAlong q m')) := by rw [hmm']
    _ = m' := hcontract m'

variable [IsHopfModuleCoalgebra k H M]

/-- An equivariant coalgebra morphism makes its induced coaction equivariant
for the diagonal action. -/
theorem coactionAlong_smul (q : M →ₗc[k] Q)
    (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (h : H) (m : M) :
    coactionAlong q (h • m) =
      diagonalHopfActionBy (k := k) (H := H) h (coactionAlong q m) := by
  rw [coactionAlong_apply, comul_smul, diagonalHopfActionBy_apply,
    coactionAlong_apply]
  rw [TensorProduct.comul_tmul]
  generalize hh : Coalgebra.comul (R := k) (A := H) h = dh
  generalize hm : Coalgebra.comul (R := k) (A := M) m = dm
  clear hh hm h m
  induction dh using TensorProduct.induction_on with
  | zero => simp
  | add dh dh' hdh hdh' =>
      simpa only [add_tmul, map_add] using
        congrArg₂ (fun a b => a + b) hdh hdh'
  | tmul h₁ h₂ =>
      induction dm using TensorProduct.induction_on with
      | zero => simp
      | add dm dm' hdm hdm' =>
          simpa only [tmul_add, map_add] using
            congrArg₂ (fun a b => a + b) hdm hdm'
      | tmul m₁ m₂ =>
          simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul,
            TensorProduct.tensorTensorTensorComm_tmul,
            TensorProduct.map_tmul, hopfModuleAction_tmul,
            LinearMap.lTensor_tmul]
          rw [hq h₂ m₂]

set_option maxHeartbeats 800000 in
-- Constructing both coefficient envelopes requires extra elaboration time.
/-- The split-field quotient estimate obtained by coefficient-density
averaging. -/
theorem exists_action_ratio_le_of_completeFlag
    [Coalgebra.IsCocomm k H]
    (A : FiniteSubcoalgebra k H)
    (hflag : PrimalTransfer.HasCompleteSubcoalgebraFlag A)
    (q : M →ₗc[k] Q)
    (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (E : Submodule k M) [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ V : Submodule k Q,
      V ≠ ⊥ ∧ FiniteDimensional k V ∧
        (sfinrank k (actionSubspace A.carrier V) : ℚ) /
            sfinrank k V ≤
          (sfinrank k (actionSubspace A.carrier E) : ℚ) /
            sfinrank k E := by
  let ρ : M →ₗ[k] M ⊗[k] Q := coactionAlong q
  let AE : Submodule k M := actionSubspace A.carrier E
  let X₀ : Submodule k (M ⊗[k] Q) := E.map ρ
  let Y₀ : Submodule k (M ⊗[k] Q) := AE.map ρ
  let Z : Submodule k (M ⊗[k] Q) := X₀ ⊔ Y₀
  let : FiniteDimensional k AE :=
    finiteDimensional_actionSubspace A.carrier E
  let : FiniteDimensional k X₀ := by
    dsimp [X₀]
    infer_instance
  let : FiniteDimensional k Y₀ := by
    dsimp [Y₀]
    infer_instance
  let : FiniteDimensional k Z := by
    dsimp [Z]
    infer_instance
  obtain ⟨P, R, hPfd, hRfd, hZsupport⟩ := exists_finite_tensor_envelope Z
  let : FiniteDimensional k P := hPfd
  let : FiniteDimensional k R := hRfd
  let S : Submodule k Q := R ⊔ actionSubspace A.carrier R
  let : FiniteDimensional k S := by
    dsimp [S]
    infer_instance
  have hXsupport : X₀ ≤ LinearMap.range (TensorProduct.mapIncl P R) :=
    le_trans le_sup_left hZsupport
  have hYsupportR : Y₀ ≤ LinearMap.range (TensorProduct.mapIncl P R) :=
    le_trans le_sup_right hZsupport
  have hYsupport : Y₀ ≤ LinearMap.range (TensorProduct.mapIncl P S) :=
    hYsupportR.trans (range_mapIncl_mono le_rfl le_sup_left)
  let X : Submodule k (P ⊗[k] R) := internalTensorSubspace P R X₀
  let Y : Submodule k (P ⊗[k] S) := internalTensorSubspace P S Y₀
  have hXimage : ambientTensorImage P R X = X₀ :=
    ambientTensorImage_internalTensorSubspace P R X₀ hXsupport
  have hYimage : ambientTensorImage P S Y = Y₀ :=
    ambientTensorImage_internalTensorSubspace P S Y₀ hYsupport
  have hρinj : Function.Injective ρ := coactionAlong_injective q
  have hX₀ne : X₀ ≠ ⊥ := by
    intro hbot
    have hmapzero : ∀ e : E, ρ e = 0 := by
      intro e
      have : ρ e ∈ X₀ := ⟨(e : M), e.2, rfl⟩
      rw [hbot] at this
      simpa using this
    let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    obtain ⟨e, he⟩ := exists_ne (0 : E)
    exact he (Subtype.ext (hρinj ((hmapzero e).trans (map_zero ρ).symm)))
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hX₀ne
    rw [← hXimage, hbot]
    exact Submodule.map_bot _
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hX₀ne
    rw [← hXimage]
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simpa only [map_add] using add_mem hz hz'
      | tmul p r =>
          have hp : (p : M) = 0 := by
            have hpbot : (p : M) ∈ (⊥ : Submodule k M) := by
              rw [← hPbot]
              exact p.2
            simpa using hpbot
          rw [show TensorProduct.mapIncl P R (p ⊗ₜ[k] r) =
              (p : M) ⊗ₜ[k] (r : Q) from rfl, hp, zero_tmul]
          exact zero_mem _
    · exact bot_le
  let : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hPne
  have hPpos : 0 < finrank k P := Module.finrank_pos
  have hdiag : ∀ (a : A.carrier) (x : X),
      diagonalHopfActionBy (k := k) (H := H) (a : H)
          (TensorProduct.mapIncl P R x) ∈ ambientTensorImage P S Y := by
    intro a x
    rw [hYimage]
    have hx₀ : TensorProduct.mapIncl P R x ∈ X₀ := by
      rw [← hXimage]
      exact ⟨x, x.2, rfl⟩
    rcases hx₀ with ⟨e, he, hρe⟩
    rw [← hρe, ← coactionAlong_smul q hq]
    exact ⟨(a : H) • e,
      product_mem_actionSubspace a.2 he, rfl⟩
  have hact : ∀ (a : A.carrier) (r : R),
      (a : H) • (r : Q) ∈ S := by
    intro a r
    exact Submodule.mem_sup_right (product_mem_actionSubspace a.2 r.2)
  have htransfer : ∀ t : ℚ,
      actionSubspace A.carrier
          (ambientImage R (coefficientDensitySubspace X t)) ≤
        ambientImage S (coefficientDensitySubspace Y t) :=
    fun t => coefficientDensity_transfer_of_completeFlag
      A hflag P R S hPpos X Y hdiag hact t
  obtain ⟨t, hCt, hratio⟩ :=
    exists_coefficient_ratio_le_of_pointwise_transfer
      A.carrier P hPpos R S X Y hXne htransfer
  let V : Submodule k Q := ambientImage R (coefficientDensitySubspace X t)
  let : FiniteDimensional k V :=
    FiniteDimensional.of_surjective
      (ambientImageEquiv R (coefficientDensitySubspace X t)).toLinearMap
      (ambientImageEquiv R (coefficientDensitySubspace X t)).surjective
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hCt
    rw [eq_bot_iff]
    intro c hc
    have : ((c : R) : Q) ∈ V := ⟨c, hc, rfl⟩
    rw [hbot] at this
    exact Subtype.ext (by simpa using this)
  have hdimX₀ : sfinrank k X₀ = finrank k E := by
    let ρE : E →ₗ[k] M ⊗[k] Q := ρ.domRestrict E
    have hrangeρE : LinearMap.range ρE = X₀ := by
      ext x
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨(e : M), e.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨(⟨m, hm⟩ : E), rfl⟩
    have hkerρE : LinearMap.ker ρE = ⊥ := LinearMap.ker_eq_bot.2
      (hρinj.comp E.injective_subtype)
    have hrank := LinearMap.finrank_range_add_finrank_ker ρE
    rw [← hrangeρE]
    simp only [sfinrank]
    rw [hkerρE, finrank_bot, add_zero] at hrank
    exact hrank
  have hdimY₀ : sfinrank k Y₀ = finrank k AE := by
    let ρAE : AE →ₗ[k] M ⊗[k] Q := ρ.domRestrict AE
    have hrangeρAE : LinearMap.range ρAE = Y₀ := by
      ext x
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨(e : M), e.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨(⟨m, hm⟩ : AE), rfl⟩
    have hkerρAE : LinearMap.ker ρAE = ⊥ := LinearMap.ker_eq_bot.2
      (hρinj.comp AE.injective_subtype)
    have hrank := LinearMap.finrank_range_add_finrank_ker ρAE
    rw [← hrangeρAE]
    simp only [sfinrank]
    rw [hkerρAE, finrank_bot, add_zero] at hrank
    exact hrank
  have hdimX : finrank k X = finrank k E := by
    calc
      finrank k X = finrank k (ambientTensorImage P R X) :=
        (ambientTensorImageEquiv P R X).finrank_eq
      _ = finrank k X₀ := by rw [hXimage]
      _ = finrank k E := hdimX₀
  have hdimY : finrank k Y = finrank k AE := by
    calc
      finrank k Y = finrank k (ambientTensorImage P S Y) :=
        (ambientTensorImageEquiv P S Y).finrank_eq
      _ = finrank k Y₀ := by rw [hYimage]
      _ = finrank k AE := hdimY₀
  refine ⟨V, hVne, inferInstance, ?_⟩
  rw [show sfinrank k V =
      sfinrank k (coefficientDensitySubspace X t) by
        exact finrank_ambientImage R (coefficientDensitySubspace X t),
    show sfinrank k E = finrank k E from rfl,
    show sfinrank k (actionSubspace A.carrier E) = finrank k AE from rfl,
    ← hdimX, ← hdimY]
  exact hratio

set_option maxHeartbeats 800000 in
-- Scalar extension and the two ratio translations require extra elaboration time.
/-- The quotient ratio estimate over an arbitrary ground field, obtained by
splitting the acting coalgebra and descending the resulting Følner ratio. -/
theorem exists_action_ratio_le
    [Coalgebra.IsCocomm k H]
    (A : FiniteSubcoalgebra k H)
    (q : M →ₗc[k] Q)
    (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (E : Submodule k M) [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ V : Submodule k Q,
      V ≠ ⊥ ∧ FiniteDimensional k V ∧
        (sfinrank k (actionSubspace A.carrier V) : ℚ) /
            sfinrank k V ≤
          (sfinrank k (actionSubspace A.carrier E) : ℚ) /
            sfinrank k E := by
  let K := CoalgebraSplittingField (k := k) (C := A.carrier)
  obtain ⟨AK, hAK, hflag⟩ := exists_baseChange_completeSubcoalgebraFlag A
  let qK : K ⊗[k] M →ₗc[K] K ⊗[k] Q :=
    Coalgebra.TensorProduct.map (CoalgHom.id K K) q
  have hqKlinear : qK.toLinearMap = q.toLinearMap.baseChange K := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul a m => rfl
  have hqK : IsHopfModuleMap (k := K) (H := K ⊗[k] H)
      (M := K ⊗[k] M) (Q := K ⊗[k] Q) qK.toLinearMap := by
    rw [hqKlinear]
    exact hq.baseChange
  let EK : Submodule K (K ⊗[k] M) := baseChangeSubspace (k := k) K E
  let : FiniteDimensional K EK := by
    let g := E.subtype.baseChange K
    exact FiniteDimensional.of_surjective g.rangeRestrict (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)
  have hEKne : EK ≠ ⊥ := by
    intro hbot
    let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    have hEpos : 0 < finrank k E := Module.finrank_pos
    have hdim : sfinrank K EK = sfinrank k E :=
      sfinrank_baseChangeSubspace (k := k) (K := K) E
    rw [hbot] at hdim
    have hzero : finrank k E = 0 := by simpa [sfinrank] using hdim.symm
    exact (Nat.ne_of_gt hEpos) hzero
  obtain ⟨VK, hVK, hVKfd, hsplit⟩ :=
    exists_action_ratio_le_of_completeFlag
      (k := K) (H := K ⊗[k] H) (M := K ⊗[k] M) (Q := K ⊗[k] Q)
      AK hflag qK hqK EK hEKne
  let : FiniteDimensional K VK := hVKfd
  have hsplit' :
      (sfinrank K
          (actionSubspace (baseChangeSubspace (k := k) K A.carrier) VK) : ℚ) /
          sfinrank K VK ≤
        (sfinrank k (actionSubspace A.carrier E) : ℚ) / sfinrank k E := by
    have hrightAction := actionSubspace_baseChange
      (k := k) (K := K) A.carrier E
    have hrightDim := sfinrank_baseChangeSubspace (k := k) (K := K)
      (actionSubspace A.carrier E)
    have hEDim := sfinrank_baseChangeSubspace (k := k) (K := K) E
    rw [hAK] at hsplit
    rw [hrightAction, hrightDim, hEDim] at hsplit
    exact hsplit
  obtain ⟨V, hV, hVfd, hdescent⟩ :=
    exists_action_ratio_le_of_finite_extension
      (k := k) (H := H) (Q := Q) A.carrier VK hVK
  exact ⟨V, hV, hVfd, hdescent.trans hsplit'⟩

/-- **Theorem B.** Every surjective equivariant counital coalgebra quotient
of an amenable Hopf-module coalgebra is amenable. -/
theorem IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom
    [Coalgebra.IsCocomm k H]
    [IsHopfModuleCoalgebra k H Q]
    (q : M →ₗc[k] Q)
    (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (_hqsurj : Function.Surjective q)
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := Q) := by
  apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
  intro F hF ε hε
  let : FiniteDimensional k F := hF
  let F1 : Submodule k H := F ⊔ Submodule.span k {1}
  let : FiniteDimensional k F1 := by
    dsimp [F1]
    infer_instance
  obtain ⟨A, hF1A⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule F1
  have hFA : F ≤ A.carrier := le_sup_left.trans hF1A
  have h1A : (1 : H) ∈ A.carrier := by
    apply hF1A
    exact (le_sup_right : Submodule.span k {1} ≤ F1)
      (Submodule.subset_span (Set.mem_singleton 1))
  obtain ⟨E, hE, hEfd, hEfolner⟩ :=
    hM.hasActionFolnerSubspaces A.carrier inferInstance ε hε
  let : FiniteDimensional k E := hEfd
  rw [actionExpansion_eq_actionSubspace_of_one_mem h1A] at hEfolner
  obtain ⟨V, hV, hVfd, hratio⟩ := exists_action_ratio_le A q hq E hE
  let : FiniteDimensional k V := hVfd
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hEpos : (0 : ℚ) < sfinrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hVpos : (0 : ℚ) < sfinrank k V := by
    exact_mod_cast Module.finrank_pos (R := k) (M := V)
  have hsourceRatio :
      (sfinrank k (actionSubspace A.carrier E) : ℚ) / sfinrank k E ≤
        1 + ε :=
    (div_le_iff₀ hEpos).2 hEfolner
  have htargetA :
      (sfinrank k (actionSubspace A.carrier V) : ℚ) ≤
        (1 + ε) * sfinrank k V :=
    (div_le_iff₀ hVpos).1 (hratio.trans hsourceRatio)
  have htargetMono : actionExpansion F V ≤ actionSubspace A.carrier V := by
    rw [← actionExpansion_eq_actionSubspace_of_one_mem h1A]
    exact actionExpansion_mono_left hFA V
  have htargetDim :
      (sfinrank k (actionExpansion F V) : ℚ) ≤
        sfinrank k (actionSubspace A.carrier V) := by
    exact_mod_cast Submodule.finrank_mono htargetMono
  exact ⟨V, hV, inferInstance, htargetDim.trans htargetA⟩

end Coalgebra

end


end HopfAmenability
