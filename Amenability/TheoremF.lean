/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.PermutationModuleAmenability

/-! # Theorem F: quotients of permutation modules -/

namespace HopfAmenability
noncomputable section
universe u v w
variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G]
local notation "kG" => MonoidAlgebra k G

section PermutationQuotient
variable {X : Type*} [MulAction G X]
variable [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]
/-- **Quotients of permutation modules.** A quotient of a
permutation module is algebraically amenable as soon as one basis point has
nonzero image and amenable orbit. -/
theorem hasActionFolnerSubspaces_of_quotient_permutationModule
    (q : MonoidAlgebra k X →ₗ[k] V)
    (_hqsurj : Function.Surjective q)
    (hq : ∀ (g : G) (x : X),
      q (pointBasis (k := k) (g • x)) =
        (MonoidAlgebra.single g (1 : k) : kG) •
          q (pointBasis (k := k) x))
    (x : X) (hqx : q (pointBasis (k := k) x) ≠ 0)
    (hx : IsAmenableOrbit (G := G) x) :
    HasActionFolnerSubspaces (k := k) (H := kG) (M := V) :=
  hasActionFolnerSubspaces_of_amenable_permutation_image q hq x hqx hx

end PermutationQuotient

section AmenableGroup
variable [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]
/-- Every nonzero module over the group
algebra of an amenable group is algebraically amenable. -/
theorem hasActionFolnerSubspaces_of_isAmenableGroup
    (hG : IsAmenableGroup (G := G)) (hV : Nontrivial V) :
    HasActionFolnerSubspaces (k := k) (H := kG) (M := V) := by
  classical
  let : MulAction G V := groupActionOfModule (k := k) (G := G) (V := V)
  let orbitOneMap : G → MulAction.orbit G (1 : G) := fun g =>
    ⟨g, MulAction.mem_orbit_iff.2 ⟨g, mul_one g⟩⟩
  have horbitSurj : Function.Surjective orbitOneMap := by
    intro y
    exact ⟨(y : G), Subtype.ext rfl⟩
  have horbitEq : ∀ (g h : G), orbitOneMap (g • h) = g • orbitOneMap h := by
    intro g h
    exact Subtype.ext rfl
  have horbit : IsAmenableOrbit (G := G) (1 : G) :=
    IsAmenableGroupAction.of_surjective_equivariant
      k orbitOneMap horbitSurj horbitEq hG
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let q : kG →ₗ[k] V := {
    toFun := fun a => a • v
    map_add' := fun a b => add_smul a b v
    map_smul' := fun c a => by
      simpa only [RingHom.id_apply] using smul_assoc c a v }
  have hq : ∀ (g x : G),
      q (pointBasis (k := k) (g • x)) =
        (MonoidAlgebra.single g (1 : k) : kG) •
          q (pointBasis (k := k) x) := by
    intro g x
    change (MonoidAlgebra.single (g * x) (1 : k) : kG) • v =
      (MonoidAlgebra.single g (1 : k) : kG) •
        ((MonoidAlgebra.single x (1 : k) : kG) • v)
    rw [← mul_smul, MonoidAlgebra.single_mul_single]
    simp
  have hqone : q (pointBasis (k := k) (1 : G)) ≠ 0 := by
    change (MonoidAlgebra.single (1 : G) (1 : k) : kG) • v ≠ 0
    rw [← MonoidAlgebra.one_def, one_smul]
    exact hv
  exact hasActionFolnerSubspaces_of_amenable_permutation_image
    q hq 1 hqone horbit

end AmenableGroup

end
end HopfAmenability
