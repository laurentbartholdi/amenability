/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfActionSubspace

/-! # Morphisms of Hopf algebras -/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]

/-- A morphism of Hopf algebras, bundled from its algebra map and coalgebra
compatibility identities. -/
structure HopfAlgebraHom (K : Type w) [Ring K] [HopfAlgebra k K] where
  toAlgHom : H →ₐ[k] K
  map_counit : (Coalgebra.counit (R := k) (A := K)).comp
      toAlgHom.toLinearMap = Coalgebra.counit (R := k) (A := H)
  map_comul : (TensorProduct.map toAlgHom.toLinearMap toAlgHom.toLinearMap).comp
      (Coalgebra.comul (R := k) (A := H)) =
        (Coalgebra.comul (R := k) (A := K)).comp toAlgHom.toLinearMap

instance {K : Type w} [Ring K] [HopfAlgebra k K] : CoeFun
    (HopfAlgebraHom (k := k) (H := H) K) (fun _ => H → K) :=
  ⟨fun f => f.toAlgHom⟩

/-- Regard a Hopf-algebra morphism as a coalgebra morphism. -/
def HopfAlgebraHom.toCoalgHom {K : Type w} [Ring K] [HopfAlgebra k K]
    (f : HopfAlgebraHom (k := k) (H := H) K) : H →ₗc[k] K where
  toLinearMap := f.toAlgHom.toLinearMap
  counit_comp := f.map_counit
  map_comp_comul := f.map_comul

/-- A Hopf-subalgebra presentation is an injective Hopf morphism. -/
structure HopfSubalgebraEmbedding (K : Type w) [Ring K] [HopfAlgebra k K]
    extends HopfAlgebraHom (k := k) (H := K) H where
  injective : Function.Injective toAlgHom

end

end HopfAmenability
