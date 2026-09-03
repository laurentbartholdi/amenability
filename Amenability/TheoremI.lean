/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.ProfileLieExample
import Amenability.TheoremG

/-!
# Theorem I: an amenable Lie algebra of exponential growth

This file packages the explicit locally-finite-by-one construction of an
amenable finitely generated Lie algebra of exponential growth.
-/

namespace HopfAmenability

noncomputable section

universe u v

variable (k : Type u) [Field k]

/-- The collection of properties asserted of the example in Theorem I.
The quotient by `K` is the displayed one-dimensional quotient in the exact
sequence of the article. -/
structure ExponentialLocallyFiniteByOneExample where
  L : LieAlgebraObject.{u, v} k
  K : LieIdeal k L.Carrier
  finitelyGenerated : IsFinitelyGeneratedLieAlgebra (k := k) L.Carrier
  exponentialGrowth : HasExponentialLieGrowth k L.Carrier
  locallyFiniteKernel : IsLocallyFiniteDimensionalLieAlgebra k K
  quotientFiniteDimensional : FiniteDimensional k (L.Carrier ⧸ K)
  quotientFinrank : Module.finrank k (L.Carrier ⧸ K) = 1
  quotientEquiv : k ≃ₗ[k] (L.Carrier ⧸ K)
  splitting : k →ₗ[k] L.Carrier
  splitting_lie : ∀ x y, ⁅splitting x, splitting y⁆ = 0
  quotient_splitting : ∀ r,
    LieIdeal.quotientMkLieHom K (splitting r) = quotientEquiv r
  amenable : IsAmenableLieAlgebra (k := k) (L := L.Carrier)

/-- The scalar multiples of `t` split the one-dimensional quotient. -/
noncomputable def ProfileLieExample.quotientSplitting :
    k →ₗ[k] ProfileLieExample.ExampleLie k :=
  LinearMap.smulRight LinearMap.id (ProfileLieExample.tLie k)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested subtype instances in the explicit matrix quotient need extra synthesis time.
/-- The explicit profile-matrix example of Theorem I.  The larger synthesis
budget is needed for the nested subtype instances in the explicit matrix Lie
algebra and its quotient. -/
noncomputable def exponentialLocallyFiniteByOneExample :
    ExponentialLocallyFiniteByOneExample.{u, u} k where
  L := LieAlgebraObject.of k (ProfileLieExample.ExampleLie k)
  K := ProfileLieExample.exampleKernel k
  finitelyGenerated := ProfileLieExample.exampleLie_isFinitelyGenerated k
  exponentialGrowth := ProfileLieExample.exampleLie_hasExponentialGrowth k
  locallyFiniteKernel :=
    ProfileLieExample.exampleKernel_isLocallyFiniteDimensional k
  quotientFiniteDimensional := by
    change FiniteDimensional k
      (ProfileLieExample.ExampleLie k ⧸ ProfileLieExample.exampleKernel k)
    exact FiniteDimensional.of_surjective
      (ProfileLieExample.quotientLinearEquiv k).toLinearMap
      (ProfileLieExample.quotientLinearEquiv k).surjective
  quotientFinrank := by
    change Module.finrank k
      (ProfileLieExample.ExampleLie k ⧸ ProfileLieExample.exampleKernel k) = 1
    exact ProfileLieExample.quotient_finrank_eq_one k
  quotientEquiv := ProfileLieExample.quotientLinearEquiv k
  splitting := ProfileLieExample.quotientSplitting k
  splitting_lie := by
    intro x y
    change ⁅x • ProfileLieExample.tLie k,
      y • ProfileLieExample.tLie k⁆ = 0
    rw [lie_smul, smul_lie, lie_self]
    simp
  quotient_splitting := by
    intro r
    rfl
  amenable := by
    apply isAmenableLieAlgebra_extension
      (ProfileLieExample.exampleKernel k)
    · exact
        (ProfileLieExample.exampleKernel_isLocallyFiniteDimensional k).isAmenableLieAlgebra
    · let : FiniteDimensional k
          (ProfileLieExample.ExampleLie k ⧸
            ProfileLieExample.exampleKernel k) :=
        FiniteDimensional.of_surjective
          (ProfileLieExample.quotientLinearEquiv k).toLinearMap
          (ProfileLieExample.quotientLinearEquiv k).surjective
      exact isAmenableLieAlgebra_of_finiteDimensional (k := k)

/-- **Theorem I.** There exists a finitely generated amenable Lie algebra
of exponential growth which is locally finite-dimensional by
one-dimensional. -/
theorem exists_amenableLieAlgebra_exponentialGrowth_locallyFiniteByOne
 :
    Nonempty (ExponentialLocallyFiniteByOneExample.{u, u} k) :=
  ⟨exponentialLocallyFiniteByOneExample k⟩

/-- Manuscript-named alias for Theorem I. -/
theorem exists_amenable_exponentialGrowth_locallyFiniteByOne
 :
    Nonempty (ExponentialLocallyFiniteByOneExample.{u, u} k) :=
  exists_amenableLieAlgebra_exponentialGrowth_locallyFiniteByOne k

end

end HopfAmenability
