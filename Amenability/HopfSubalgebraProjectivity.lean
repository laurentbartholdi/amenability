/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAlgebraHom

/-! # Projectivity over Hopf subalgebras -/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]

/-- Restriction of the regular action along a Hopf-subalgebra embedding. -/
@[instance_reducible]
noncomputable def hopfSubalgebraRestrictionModule
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K) : Module K H :=
  Module.compHom H i.toAlgHom.toRingHom

/-- The sole external project input: Takeuchi--Wigner projectivity. -/
axiom takeuchiWigner_projective_left
    [Coalgebra.IsCocomm k H]
    {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (_hcomm : Coalgebra.IsCocomm k H)
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K) :
    letI := hopfSubalgebraRestrictionModule i
    Module.Projective K H

end

end HopfAmenability
