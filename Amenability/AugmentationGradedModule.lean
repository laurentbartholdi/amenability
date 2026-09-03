/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AugmentationGradedAlgebra
import Mathlib.Algebra.Module.GradedModule

/-! # The module structure on an augmentation associated graded -/

open Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- The degree-`n` homogeneous quotient of the module augmentation
filtration. -/
abbrev AugmentationGradedModulePiece (n : ℕ) :=
  augmentationModuleFiltration (k := k) (H := H) (M := M) n ⧸
    (augmentationModuleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
      (augmentationModuleFiltration (k := k) (H := H) (M := M) n).subtype

private abbrev nextModuleFiltrationIn (n : ℕ) :
    Submodule k
      (augmentationModuleFiltration (k := k) (H := H) (M := M) n) :=
  (augmentationModuleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
    (augmentationModuleFiltration (k := k) (H := H) (M := M) n).subtype

private theorem filteredAction_mem (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i)
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) j) :
    (h : H) • (m : M) ∈
      augmentationModuleFiltration (k := k) (H := H) (M := M) (i + j) :=
  augmentationFiltration_action_le i j
    (product_mem_actionSubspace h.property m.property)

private def filteredActionLinear (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i) :
    augmentationModuleFiltration (k := k) (H := H) (M := M) j →ₗ[k]
      AugmentationGradedModulePiece (k := k) (H := H) (M := M) (i + j) where
  toFun m := Submodule.Quotient.mk ⟨(h : H) • (m : M), filteredAction_mem i j h m⟩
  map_add' m n := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r m := by
    rw [← Submodule.Quotient.mk_smul]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact smul_comm _ _ _

private theorem filteredActionLinear_vanishes_right (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i) :
    nextModuleFiltrationIn (k := k) (H := H) (M := M) j ≤
      LinearMap.ker (filteredActionLinear (k := k) (H := H) (M := M) i j h) := by
  intro m hm
  rw [LinearMap.mem_ker]
  apply (QuotientAddGroup.eq_zero_iff _).2
  change (h : H) • (m : M) ∈
    augmentationModuleFiltration (k := k) (H := H) (M := M) (i + j + 1)
  have ha := augmentationFiltration_action_le (k := k) (H := H) (M := M) i (j + 1)
    (product_mem_actionSubspace h.property hm)
  simpa [add_assoc] using ha

private def filteredActionLeft (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i) :
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) j →ₗ[k]
      AugmentationGradedModulePiece (k := k) (H := H) (M := M) (i + j) :=
  (nextModuleFiltrationIn (k := k) (H := H) (M := M) j).liftQ
    (filteredActionLinear (k := k) (H := H) (M := M) i j h)
    (filteredActionLinear_vanishes_right (k := k) (H := H) (M := M) i j h)

private def filteredActionLeftLinear (i j : ℕ) :
    augmentationFiltration (k := k) (H := H) i →ₗ[k]
      (AugmentationGradedModulePiece (k := k) (H := H) (M := M) j →ₗ[k]
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) (i + j)) where
  toFun := filteredActionLeft (k := k) (H := H) (M := M) i j
  map_add' h h' := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      simp only [filteredActionLeft, Submodule.liftQ_apply, LinearMap.add_apply,
        filteredActionLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : augmentationModuleFiltration
            (k := k) (H := H) (M := M) (i + j)) =
        Submodule.Quotient.mk (⟨_, _⟩ : augmentationModuleFiltration
          (k := k) (H := H) (M := M) (i + j)) +
        Submodule.Quotient.mk (⟨_, _⟩ : augmentationModuleFiltration
          (k := k) (H := H) (M := M) (i + j))
      rw [← Submodule.Quotient.mk_add]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact add_smul _ _ _
  map_smul' r h := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      simp only [filteredActionLeft, Submodule.liftQ_apply, LinearMap.smul_apply,
        RingHom.id_apply, filteredActionLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : augmentationModuleFiltration
            (k := k) (H := H) (M := M) (i + j)) =
        r • Submodule.Quotient.mk (⟨_, _⟩ : augmentationModuleFiltration
          (k := k) (H := H) (M := M) (i + j))
      rw [← Submodule.Quotient.mk_smul]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact smul_assoc _ _ _

private theorem filteredActionLeftLinear_vanishes (i j : ℕ) :
    (augmentationFiltration (k := k) (H := H) (i + 1)).comap
        (augmentationFiltration (k := k) (H := H) i).subtype ≤
      LinearMap.ker
        (filteredActionLeftLinear (k := k) (H := H) (M := M) i j) := by
  intro h hh
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
    apply (QuotientAddGroup.eq_zero_iff _).2
    change (h : H) • (m : M) ∈
      augmentationModuleFiltration (k := k) (H := H) (M := M) (i + j + 1)
    have ha := augmentationFiltration_action_le (k := k) (H := H) (M := M)
      (i + 1) j (product_mem_actionSubspace hh m.property)
    simpa [add_assoc, add_left_comm, add_comm] using ha

/-- Action of a homogeneous augmentation-graded Hopf piece on a homogeneous
module piece. -/
def augmentationGradedAction (i j : ℕ) :
    AugmentationGradedHopfPiece (k := k) (H := H) i →ₗ[k]
      (AugmentationGradedModulePiece (k := k) (H := H) (M := M) j →ₗ[k]
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) (i + j)) :=
  ((augmentationFiltration (k := k) (H := H) (i + 1)).comap
      (augmentationFiltration (k := k) (H := H) i).subtype).liftQ
    (filteredActionLeftLinear (k := k) (H := H) (M := M) i j)
    (filteredActionLeftLinear_vanishes (k := k) (H := H) (M := M) i j)

@[simp]
theorem augmentationGradedAction_mk (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i)
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) j) :
    augmentationGradedAction (k := k) (H := H) (M := M) i j
        (Submodule.Quotient.mk h) (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk ⟨(h : H) • (m : M), filteredAction_mem i j h m⟩ :=
  rfl

instance augmentationGradedGSMul : GradedMonoid.GSMul
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)
    (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n) where
  smul {i j} := fun h m =>
    augmentationGradedAction (k := k) (H := H) (M := M) i j h m

private theorem augmentationGradedModule_mk_heq
    {m n : ℕ} (hmn : m = n)
    (a : augmentationModuleFiltration (k := k) (H := H) (M := M) m)
    (b : augmentationModuleFiltration (k := k) (H := H) (M := M) n)
    (hab : (a : M) = b) :
    HEq (Submodule.Quotient.mk a :
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) m)
      (Submodule.Quotient.mk b :
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) n) := by
  subst n
  apply heq_of_eq
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext hab

private theorem augmentationGraded_one_smul
    (m : GradedMonoid
      (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n)) :
    (1 : GradedMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)) • m = m := by
  rcases m with ⟨j, m⟩
  apply Sigma.ext (zero_add j)
  induction m using Submodule.Quotient.induction_on with
  | _ m =>
    exact augmentationGradedModule_mk_heq (k := k) (H := H) (M := M)
      (zero_add j) _ m (one_smul _ _)

private theorem augmentationGraded_mul_smul
    (h h' : GradedMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n))
    (m : GradedMonoid
      (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n)) :
    (h * h') • m = h • h' • m := by
  rcases h with ⟨i, h⟩
  rcases h' with ⟨j, h'⟩
  rcases m with ⟨l, m⟩
  apply Sigma.ext (add_assoc i j l)
  induction h using Submodule.Quotient.induction_on with
  | _ h =>
    induction h' using Submodule.Quotient.induction_on with
    | _ h' =>
      induction m using Submodule.Quotient.induction_on with
      | _ m =>
        exact augmentationGradedModule_mk_heq (k := k) (H := H) (M := M)
          (add_assoc i j l) _ _ (mul_smul _ _ _)

instance augmentationGradedGmodule : DirectSum.Gmodule
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)
    (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n) where
  smul {i j} := fun h m =>
    augmentationGradedAction (k := k) (H := H) (M := M) i j h m
  one_smul := augmentationGraded_one_smul (k := k) (H := H) (M := M)
  mul_smul := augmentationGraded_mul_smul (k := k) (H := H) (M := M)
  smul_add := fun h => (augmentationGradedAction _ _ h).map_add
  smul_zero := fun h => (augmentationGradedAction _ _ h).map_zero
  add_smul := fun h h' m => by
    change augmentationGradedAction (k := k) (H := H) (M := M) _ _ (h + h') m = _
    change augmentationGradedAction (k := k) (H := H) (M := M) _ _ (h + h') m =
      augmentationGradedAction (k := k) (H := H) (M := M) _ _ h m +
        augmentationGradedAction (k := k) (H := H) (M := M) _ _ h' m
    rw [map_add, LinearMap.add_apply]
  zero_smul := fun m => by
    change augmentationGradedAction (k := k) (H := H) (M := M) _ _ 0 m = 0
    rw [map_zero]
    exact rfl

/-- The module structure over the concrete graded Hopf algebra. -/
noncomputable instance augmentationGradedModuleOverHopf :
    Module (AugmentationGradedHopf (k := k) (H := H))
      (AugmentationGradedModule (k := k) (H := H) (M := M)) :=
  DirectSum.Gmodule.module
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)
    (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n)

noncomputable instance augmentationGradedIsScalarTower :
    IsScalarTower k (AugmentationGradedHopf (k := k) (H := H))
      (AugmentationGradedModule (k := k) (H := H) (M := M)) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | of j q =>
      induction q using Submodule.Quotient.induction_on with
      | _ m =>
        rw [DirectSum.algebraMap_apply]
        rw [DirectSum.Gmodule.of_smul_of]
        rw [← DirectSum.of_smul]
        apply DirectSum.of_eq_of_gradedMonoid_eq
        apply Sigma.ext (zero_add j)
        apply augmentationGradedModule_mk_heq (k := k) (H := H) (M := M)
          (zero_add j)
        simp [Algebra.smul_def]

section Counit

variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

private def augmentationGradedCounitZero :
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) 0 →ₗ[k] k :=
  ((augmentationModuleFiltration (k := k) (H := H) (M := M) 1).comap
      (augmentationModuleFiltration (k := k) (H := H) (M := M) 0).subtype).liftQ
    ((Coalgebra.counit (R := k) (A := M)).comp
      (augmentationModuleFiltration (k := k) (H := H) (M := M) 0).subtype)
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact augmentationModuleFiltration_counit_one (k := k) (H := H) (M := M)
        x hx)

private def augmentationGradedCounitPiece (n : ℕ) :
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) n →ₗ[k] k :=
  match n with
  | 0 => augmentationGradedCounitZero (k := k) (H := H) (M := M)
  | _ + 1 => 0

/-- The counit induced on the augmentation associated graded module: it is
the original counit in degree zero and zero in positive degrees. -/
def augmentationGradedCounit :
    AugmentationGradedModule (k := k) (H := H) (M := M) →ₗ[k] k :=
  DirectSum.toModule k _ _ fun n =>
    augmentationGradedCounitPiece (k := k) (H := H) (M := M) n

@[simp]
theorem augmentationGradedCounit_of_zero
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) 0) :
    augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ 0 (Submodule.Quotient.mk m)) =
      Coalgebra.counit (R := k) (A := M) m := by
  rw [augmentationGradedCounit, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof]
  rfl

@[simp]
theorem augmentationGradedCounit_of_succ (n : ℕ)
    (m : AugmentationGradedModulePiece (k := k) (H := H) (M := M) (n + 1)) :
    augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ (n + 1) m) = 0 := by
  rw [augmentationGradedCounit, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof]
  rfl

@[simp]
theorem augmentationGradedCounit_of_ne_zero (n : ℕ) (hn : n ≠ 0)
    (m : AugmentationGradedModulePiece (k := k) (H := H) (M := M) n) :
    augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ n m) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact augmentationGradedCounit_of_succ (k := k) (H := H) (M := M) d m

theorem augmentationGradedCounit_of_eq_zero {n : ℕ} (hn : n = 0)
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) n) :
    augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ n (Submodule.Quotient.mk m)) =
      Coalgebra.counit (R := k) (A := M) (m : M) := by
  subst n
  exact augmentationGradedCounit_of_zero (k := k) (H := H) (M := M) m

end Counit

end


end HopfAmenability
