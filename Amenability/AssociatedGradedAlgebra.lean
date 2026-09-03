/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AugmentationFiltration
import Mathlib.Algebra.DirectSum.Algebra

/-! # The algebra structure on the augmentation associated graded -/

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]

/-- The degree-`n` homogeneous quotient of the augmentation filtration. -/
abbrev AugmentationGradedHopfPiece (n : ℕ) :=
  augmentationFiltration (k := k) (H := H) n ⧸
    (augmentationFiltration (k := k) (H := H) (n + 1)).comap
      (augmentationFiltration (k := k) (H := H) n).subtype

private abbrev nextFiltrationIn (n : ℕ) :
    Submodule k (augmentationFiltration (k := k) (H := H) n) :=
  (augmentationFiltration (k := k) (H := H) (n + 1)).comap
    (augmentationFiltration (k := k) (H := H) n).subtype

private def filteredMulLinear (i j : ℕ)
    (a : augmentationFiltration (k := k) (H := H) i) :
    augmentationFiltration (k := k) (H := H) j →ₗ[k]
      AugmentationGradedHopfPiece (k := k) (H := H) (i + j) where
  toFun b := Submodule.Quotient.mk ⟨(a : H) * b,
    augmentationFiltration_mul_le i j (Submodule.mul_mem_mul a.property b.property)⟩
  map_add' b c := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r b := by
    rw [← Submodule.Quotient.mk_smul]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact mul_smul_comm _ _ _

private theorem filteredMulLinear_vanishes_right (i j : ℕ)
    (a : augmentationFiltration (k := k) (H := H) i) :
    nextFiltrationIn (k := k) (H := H) j ≤
      LinearMap.ker (filteredMulLinear (k := k) (H := H) i j a) := by
  intro b hb
  rw [LinearMap.mem_ker]
  apply (QuotientAddGroup.eq_zero_iff _).2
  change (a : H) * (b : H) ∈
    augmentationFiltration (k := k) (H := H) (i + j + 1)
  have hmul := augmentationFiltration_mul_le i (j + 1)
    (Submodule.mul_mem_mul a.property hb)
  simpa [add_assoc] using hmul

private def filteredMulLeft (i j : ℕ)
    (a : augmentationFiltration (k := k) (H := H) i) :
    AugmentationGradedHopfPiece (k := k) (H := H) j →ₗ[k]
      AugmentationGradedHopfPiece (k := k) (H := H) (i + j) :=
  (nextFiltrationIn (k := k) (H := H) j).liftQ
    (filteredMulLinear (k := k) (H := H) i j a)
    (filteredMulLinear_vanishes_right (k := k) (H := H) i j a)

private def filteredMulLeftLinear (i j : ℕ) :
    augmentationFiltration (k := k) (H := H) i →ₗ[k]
      (AugmentationGradedHopfPiece (k := k) (H := H) j →ₗ[k]
        AugmentationGradedHopfPiece (k := k) (H := H) (i + j)) where
  toFun := filteredMulLeft (k := k) (H := H) i j
  map_add' a b := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
      simp only [filteredMulLeft, Submodule.liftQ_apply, LinearMap.add_apply,
        filteredMulLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : augmentationFiltration (k := k) (H := H) (i + j)) =
        Submodule.Quotient.mk (⟨_, _⟩ : augmentationFiltration
          (k := k) (H := H) (i + j)) +
        Submodule.Quotient.mk (⟨_, _⟩ : augmentationFiltration
          (k := k) (H := H) (i + j))
      rw [← Submodule.Quotient.mk_add]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact add_mul _ _ _
  map_smul' r a := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ b =>
      simp only [filteredMulLeft, Submodule.liftQ_apply, LinearMap.smul_apply,
        RingHom.id_apply, filteredMulLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : augmentationFiltration (k := k) (H := H) (i + j)) =
        r • Submodule.Quotient.mk (⟨_, _⟩ : augmentationFiltration
          (k := k) (H := H) (i + j))
      rw [← Submodule.Quotient.mk_smul]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact smul_mul_assoc _ _ _

private theorem filteredMulLeftLinear_vanishes (i j : ℕ) :
    nextFiltrationIn (k := k) (H := H) i ≤
      LinearMap.ker (filteredMulLeftLinear (k := k) (H := H) i j) := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ b =>
    apply (QuotientAddGroup.eq_zero_iff _).2
    change (a : H) * (b : H) ∈
      augmentationFiltration (k := k) (H := H) (i + j + 1)
    have hmul := augmentationFiltration_mul_le (i + 1) j
      (Submodule.mul_mem_mul ha b.property)
    simpa [add_assoc, add_left_comm, add_comm] using hmul

/-- Multiplication of homogeneous augmentation-graded pieces. -/
def augmentationGradedMul (i j : ℕ) :
    AugmentationGradedHopfPiece (k := k) (H := H) i →ₗ[k]
      (AugmentationGradedHopfPiece (k := k) (H := H) j →ₗ[k]
        AugmentationGradedHopfPiece (k := k) (H := H) (i + j)) :=
  (nextFiltrationIn (k := k) (H := H) i).liftQ
    (filteredMulLeftLinear (k := k) (H := H) i j)
    (filteredMulLeftLinear_vanishes (k := k) (H := H) i j)

@[simp]
theorem augmentationGradedMul_mk (i j : ℕ)
    (a : augmentationFiltration (k := k) (H := H) i)
    (b : augmentationFiltration (k := k) (H := H) j) :
    augmentationGradedMul (k := k) (H := H) i j
        (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨(a : H) * b,
        augmentationFiltration_mul_le i j
          (Submodule.mul_mem_mul a.property b.property)⟩ :=
  rfl

private def augmentationGradedOne :
    AugmentationGradedHopfPiece (k := k) (H := H) 0 :=
  Submodule.Quotient.mk ⟨1, by
    rw [augmentationFiltration_zero]
    exact Submodule.mem_top⟩

instance augmentationGradedGMul :
    GradedMonoid.GMul
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) where
  mul {i j} := fun a b =>
    augmentationGradedMul (k := k) (H := H) i j a b

instance augmentationGradedGOne :
    GradedMonoid.GOne
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) where
  one := augmentationGradedOne (k := k) (H := H)

private theorem augmentationGraded_mk_heq
    {m n : ℕ} (hmn : m = n)
    (a : augmentationFiltration (k := k) (H := H) m)
    (b : augmentationFiltration (k := k) (H := H) n)
    (hab : (a : H) = b) :
    HEq (Submodule.Quotient.mk a :
        AugmentationGradedHopfPiece (k := k) (H := H) m)
      (Submodule.Quotient.mk b :
        AugmentationGradedHopfPiece (k := k) (H := H) n) := by
  subst n
  apply heq_of_eq
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext hab

private theorem augmentationGraded_one_mul
    (a : GradedMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)) :
    1 * a = a := by
  rcases a with ⟨i, a⟩
  apply Sigma.ext (zero_add i)
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    exact augmentationGraded_mk_heq (k := k) (H := H) (zero_add i)
      _ a (one_mul _)

private theorem augmentationGraded_mul_one
    (a : GradedMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)) :
    a * 1 = a := by
  rcases a with ⟨i, a⟩
  apply Sigma.ext (add_zero i)
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    apply heq_of_eq
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact mul_one _

private theorem augmentationGraded_mul_assoc
    (a b c : GradedMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)) :
    a * b * c = a * (b * c) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨l, c⟩
  apply Sigma.ext (add_assoc i j l)
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      induction c using Submodule.Quotient.induction_on with
      | _ c =>
        exact augmentationGraded_mk_heq (k := k) (H := H)
          (add_assoc i j l) _ _ (mul_assoc _ _ _)

instance augmentationGradedGMonoid :
    GradedMonoid.GMonoid
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) where
  one_mul := augmentationGraded_one_mul (k := k) (H := H)
  mul_one := augmentationGraded_mul_one (k := k) (H := H)
  mul_assoc := augmentationGraded_mul_assoc (k := k) (H := H)

instance augmentationGradedGRing :
    DirectSum.GRing
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) where
  mul_zero := fun a => (augmentationGradedMul _ _ a).map_zero
  zero_mul := fun b => by
    change augmentationGradedMul (k := k) (H := H) _ _ 0 b = 0
    rw [map_zero]
    exact rfl
  mul_add := fun a => (augmentationGradedMul _ _ a).map_add
  add_mul := fun a b c => by
    change augmentationGradedMul (k := k) (H := H) _ _ (a + b) c = _
    change augmentationGradedMul (k := k) (H := H) _ _ (a + b) c =
      augmentationGradedMul (k := k) (H := H) _ _ a c +
        augmentationGradedMul (k := k) (H := H) _ _ b c
    rw [map_add, LinearMap.add_apply]
  natCast := fun n => n • augmentationGradedOne (k := k) (H := H)
  natCast_zero := zero_nsmul _
  natCast_succ := fun n => by
    change (n + 1) • augmentationGradedOne (k := k) (H := H) =
      n • augmentationGradedOne (k := k) (H := H) +
        augmentationGradedOne (k := k) (H := H)
    simpa [Nat.succ_eq_add_one] using
      (succ_nsmul (augmentationGradedOne (k := k) (H := H)) n)
  intCast := fun z => z • augmentationGradedOne (k := k) (H := H)
  intCast_ofNat := fun n => by simp
  intCast_negSucc_ofNat := fun n => by simp

instance augmentationGradedGSemiring :
    DirectSum.GSemiring
      (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) :=
  (augmentationGradedGRing (k := k) (H := H)).toGSemiring

/-- The ring structure on the concrete augmentation-associated graded Hopf
vector space, induced by multiplication of representatives. -/
noncomputable instance augmentationGradedRing :
    Ring (AugmentationGradedHopf (k := k) (H := H)) :=
  DirectSum.ring
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)

private def augmentationGradedScalar : k →+
    AugmentationGradedHopfPiece (k := k) (H := H) 0 where
  toFun r := r • augmentationGradedOne (k := k) (H := H)
  map_zero' := zero_smul _ _
  map_add' r s := add_smul r s _

instance augmentationGradedGAlgebra : DirectSum.GAlgebra k
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n) where
  toFun := augmentationGradedScalar (k := k) (H := H)
  map_one := by
    change (1 : k) • augmentationGradedOne (k := k) (H := H) =
      augmentationGradedOne (k := k) (H := H)
    exact one_smul _ _
  map_mul r s := by
    apply Sigma.ext (zero_add 0).symm
    apply augmentationGraded_mk_heq (k := k) (H := H) (zero_add 0).symm
    simp [Algebra.smul_def]
  commutes := fun r a => by
    rcases a with ⟨i, a⟩
    apply Sigma.ext ((zero_add i).trans (add_zero i).symm)
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      apply augmentationGraded_mk_heq (k := k) (H := H)
        ((zero_add i).trans (add_zero i).symm)
      simp [Algebra.smul_def, Algebra.commutes]
  smul_def := fun r a => by
    rcases a with ⟨i, a⟩
    apply Sigma.ext (zero_add i).symm
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      apply augmentationGraded_mk_heq (k := k) (H := H) (zero_add i).symm
      simp [Algebra.smul_def]

/-- The scalar algebra structure induced degreewise from the original Hopf
algebra. -/
noncomputable instance augmentationGradedAlgebra :
    Algebra k (AugmentationGradedHopf (k := k) (H := H)) :=
  DirectSum.instAlgebra k
    (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)

private def filteredAntipode (n : ℕ) :
    augmentationFiltration (k := k) (H := H) n →ₗ[k]
      augmentationFiltration (k := k) (H := H) n :=
  (HopfAlgebra.antipode k).domRestrict
      (augmentationFiltration (k := k) (H := H) n) |>.codRestrict
    (augmentationFiltration (k := k) (H := H) n)
    (fun x => augmentationFiltration_antipode (k := k) (H := H) n x x.property)

private theorem filteredAntipode_preserves_next (n : ℕ) :
    nextFiltrationIn (k := k) (H := H) n ≤
      (nextFiltrationIn (k := k) (H := H) n).comap
        (filteredAntipode (k := k) (H := H) n) := by
  intro x hx
  change HopfAlgebra.antipode k (x : H) ∈
    augmentationFiltration (k := k) (H := H) (n + 1)
  exact augmentationFiltration_antipode (k := k) (H := H) (n + 1) x hx

/-- Antipode induced on a homogeneous augmentation-graded piece. -/
def augmentationGradedAntipodePiece (n : ℕ) :
    AugmentationGradedHopfPiece (k := k) (H := H) n →ₗ[k]
      AugmentationGradedHopfPiece (k := k) (H := H) n :=
  (nextFiltrationIn (k := k) (H := H) n).mapQ
    (nextFiltrationIn (k := k) (H := H) n)
    (filteredAntipode (k := k) (H := H) n)
    (filteredAntipode_preserves_next (k := k) (H := H) n)

/-- The degree-preserving antipode on the augmentation associated graded
algebra. -/
def augmentationGradedAntipode :
    AugmentationGradedHopf (k := k) (H := H) →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) :=
  DirectSum.toModule k _ _ fun n =>
    (DirectSum.lof k ℕ
      (fun r => AugmentationGradedHopfPiece (k := k) (H := H) r) n).comp
        (augmentationGradedAntipodePiece (k := k) (H := H) n)

@[simp]
theorem augmentationGradedAntipode_of_mk (n : ℕ)
    (h : augmentationFiltration (k := k) (H := H) n) :
    augmentationGradedAntipode (k := k) (H := H)
        (DirectSum.of _ n (Submodule.Quotient.mk h)) =
      DirectSum.of _ n
        (Submodule.Quotient.mk
          ⟨HopfAlgebra.antipode k (h : H),
            augmentationFiltration_antipode (k := k) (H := H) n h h.property⟩) := by
  rw [augmentationGradedAntipode, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof]
  rfl

end

end HopfAmenability
