/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremG
import Amenability.WittAlgebra
import Amenability.ElementaryLieAlgebra
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Theorem H: elementary and subexponential amenability differ

This file proves the separation results of Theorem H using the reusable Witt-algebra construction.
-/

namespace HopfAmenability

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The class of Lie algebras not isomorphic to the Witt algebra.  This is
the separating closed class used in the elementary-amenability argument. -/
def IsNotLieEquivWitt (A : LieAlgebraObject k) : Prop :=
  ¬ Nonempty (LieEquiv k A.Carrier (WittAlgebra k))

theorem isNotLieEquivWitt_of_finiteDimensional [CharZero k]
    (A : LieAlgebraObject k) (hA : FiniteDimensional k A.Carrier) :
    IsNotLieEquivWitt k A := by
  rintro ⟨e⟩
  let _ : FiniteDimensional k A.Carrier := hA
  have hW : FiniteDimensional k (WittAlgebra k) :=
    e.toLinearEquiv.finiteDimensional
  exact wittAlgebra_not_finiteDimensional k hW

theorem isNotLieEquivWitt_of_abelian [CharZero k]
    (A : LieAlgebraObject k) (hA : IsLieAbelian A.Carrier) :
    IsNotLieEquivWitt k A := by
  rintro ⟨e⟩
  let x : A.Carrier := e.symm (wittBasisVector k 0)
  let y : A.Carrier := e.symm (wittBasisVector k 1)
  have hzero := hA.trivial x y
  have himage := congrArg e hzero
  have heq :
      wittBracketBilinear k (wittBasisVector k 0)
        (wittBasisVector k 1) = 0 := by
    rw [e.map_lie] at himage
    simpa [x, y] using himage
  rw [← witt_bracket_eq, witt_bracket_basis] at heq
  have hone : wittBasisVector k 1 ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h 1
    simp [wittBasisVector] at this
  exact hone (by simpa using heq)

theorem isNotLieEquivWitt_extension [CharZero k]
    (A : LieAlgebraObject k) (I : LieIdeal k A.Carrier)
    (hI : IsNotLieEquivWitt k (A.ofIdeal I))
    (hQ : IsNotLieEquivWitt k (A.quotient I)) :
    IsNotLieEquivWitt k A := by
  rintro ⟨e⟩
  let J : LieIdeal k (WittAlgebra k) :=
    LieIdeal.comap e.symm.toLieHom I
  let _ : LieAlgebra.IsSimple k (WittAlgebra k) := wittAlgebra_isSimple k
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top J with hJ | hJ
  · have hIbot : I = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hxJ : e x ∈ J := by
          change e.symm (e x) ∈ I
          simpa using hx
        rw [hJ] at hxJ
        change e x = 0 at hxJ
        change x = 0
        exact e.injective (by simpa using hxJ)
      · exact bot_le
    exact hQ ⟨(LieIdeal.quotientEquivOfEqBot I hIbot).trans e⟩
  · let f : LieHom k I (WittAlgebra k) :=
      e.toLieHom.comp (LieSubalgebra.incl (I : LieSubalgebra k A.Carrier))
    have hf_injective : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact e.injective hxy
    have hf_surjective : Function.Surjective f := by
      intro y
      have hyJ : y ∈ J := by rw [hJ]; trivial
      change e.symm y ∈ I at hyJ
      refine ⟨⟨e.symm y, hyJ⟩, ?_⟩
      change e (e.symm y) = y
      exact e.apply_symm_apply y
    exact hI ⟨LieEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩⟩

theorem isNotLieEquivWitt_directedUnion [CharZero k]
    (A : LieAlgebraObject k) (ι : Type u) [Nonempty ι]
    (S : ι → LieSubalgebra k A.Carrier)
    (hdir : Directed (· ≤ ·) S) (hsup : iSup S = ⊤)
    (hS : ∀ i, IsNotLieEquivWitt k (A.ofSubalgebra (S i))) :
    IsNotLieEquivWitt k A := by
  classical
  rintro ⟨e⟩
  let emb : WittAlgebra k ↪ A.Carrier :=
    e.symm.toLinearEquiv.toEquiv.toEmbedding
  let s : Finset A.Carrier := (wittGeneratingFinset k).map emb
  have hs_member (x : A.Carrier) (hx : x ∈ s) : ∃ i, x ∈ S i := by
    have hxSup : x ∈ iSup S := by rw [hsup]; trivial
    exact (LieSubalgebra.mem_iSup_of_directed (k := k) S hdir).mp hxSup
  obtain ⟨i, hi⟩ := exists_directed_member_containing_finset
    (k := k) (L := A.Carrier) (ι := ι) S hdir s hs_member
  have hgen (j : WittAlgebra k) (hj : j ∈ wittGeneratingSet k) :
      e.symm j ∈ S i := by
    apply hi (e.symm j)
    change e.symm j ∈ (wittGeneratingFinset k).map emb
    rw [Finset.mem_map]
    refine ⟨j, ?_, rfl⟩
    change j ∈ (wittGeneratingFinset k : Set (WittAlgebra k))
    rw [coe_wittGeneratingFinset]
    exact hj
  have htop : S i = ⊤ := by
    let T : LieSubalgebra k (WittAlgebra k) := (S i).map e.toLieHom
    have hspan : LieSubalgebra.lieSpan k (WittAlgebra k)
        (wittGeneratingSet k) ≤ T := by
      apply LieSubalgebra.lieSpan_le.mpr
      intro y hy
      dsimp [T]
      exact (LieSubalgebra.mem_map (f := e.toLieHom) (K := S i) y).2
        ⟨e.symm y, hgen y hy, e.apply_symm_apply y⟩
    have hT : T = ⊤ := by
      rw [witt_lieSpan_generators_eq_top] at hspan
      exact top_unique hspan
    apply top_unique
    intro x hx
    have hex : e x ∈ T := by rw [hT]; trivial
    dsimp [T] at hex
    obtain ⟨y, hy, hey⟩ :=
      (LieSubalgebra.mem_map (f := e.toLieHom) (K := S i) (e x)).1 hex
    have hyx : y = x := e.injective hey
    simpa [hyx] using hy
  let f : LieHom k (S i) (WittAlgebra k) :=
    e.toLieHom.comp (LieSubalgebra.incl (S i))
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact e.injective hxy
  have hf_surjective : Function.Surjective f := by
    intro y
    let x : A.Carrier := e.symm y
    have hx : x ∈ S i := by rw [htop]; trivial
    refine ⟨⟨x, hx⟩, ?_⟩
    change e x = y
    exact e.apply_symm_apply y
  exact hS i ⟨LieEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩⟩

/-- The closed class separating the Witt algebra from the elementary
hierarchy. -/
noncomputable def notLieEquivWittClosedClass [CharZero k] :
    ElementaryClosedLieClass (k := k) where
  universeWitness := WittAlgebra k
  mem := IsNotLieEquivWitt k
  finiteDimensional_mem := isNotLieEquivWitt_of_finiteDimensional k
  abelian_mem := isNotLieEquivWitt_of_abelian k
  extension_mem := isNotLieEquivWitt_extension k
  directedUnion_mem := isNotLieEquivWitt_directedUnion k

/-- The characteristic-zero Witt algebra is not elementarily amenable. -/
theorem wittAlgebra_not_elementarilyAmenable [CharZero k] :
    ¬ IsElementarilyAmenableLieAlgebra (k := k) (WittAlgebra k) := by
  intro hW
  have hsep := IsElementaryLieObject.mem_closedClass
    (notLieEquivWittClosedClass k) hW
  exact hsep ⟨(LieEquiv.refl :
    LieEquiv k (WittAlgebra k) (WittAlgebra k))⟩

/-- The class `SL`: the closure of subexponential-growth Lie algebras under
extensions and directed unions.  As for `EL`, subalgebra and quotient
closure is a derived property of this hierarchy. -/
inductive IsSubexponentiallyAmenableLieObject : LieAlgebraObject k → Prop
  | subexponential (A : LieAlgebraObject k)
      (hA : HasSubexponentialLieGrowth k A.Carrier) :
      IsSubexponentiallyAmenableLieObject A
  | extension (A : LieAlgebraObject k) (I : LieIdeal k A.Carrier)
      (hI : IsSubexponentiallyAmenableLieObject (A.ofIdeal I))
      (hQ : IsSubexponentiallyAmenableLieObject (A.quotient I)) :
      IsSubexponentiallyAmenableLieObject A
  | directedUnion (A : LieAlgebraObject k) (ι : Type u) [Nonempty ι]
      (S : ι → LieSubalgebra k A.Carrier)
      (hdir : Directed (· ≤ ·) S) (hsup : iSup S = ⊤)
      (hS : ∀ i,
        IsSubexponentiallyAmenableLieObject (A.ofSubalgebra (S i))) :
      IsSubexponentiallyAmenableLieObject A

/-- The manuscript inclusion `SL ⊆ AL`. -/
theorem IsSubexponentiallyAmenableLieObject.isAmenable
    {A : LieAlgebraObject k}
    (hA : IsSubexponentiallyAmenableLieObject (k := k) A) :
    IsAmenableLieAlgebra (k := k) (L := A.Carrier) := by
  induction hA with
  | subexponential A hgrowth =>
      exact isAmenableLieAlgebra_of_hasSubexponentialLieGrowth (k := k) hgrowth
  | extension A I _ _ hI hQ =>
      exact isAmenableLieAlgebra_extension I hI hQ
  | directedUnion A ι S hdir hsup _ hS =>
      exact isAmenableLieAlgebra_directedUnion S hdir hsup hS

/-- Finite-dimensional Lie algebras lie in `SL`. -/
theorem isSubexponentiallyAmenableLieObject_of_finiteDimensional
    (A : LieAlgebraObject k) [FiniteDimensional k A.Carrier] :
    IsSubexponentiallyAmenableLieObject (k := k) A :=
  IsSubexponentiallyAmenableLieObject.subexponential A
    (hasSubexponentialLieGrowth_of_finiteDimensional k)

/-- Abelian Lie algebras lie in `SL`, as directed unions of their
finite-generated (hence finite-dimensional) Lie subalgebras. -/
theorem isSubexponentiallyAmenableLieObject_of_isLieAbelian
    (A : LieAlgebraObject.{u, u} k) (hA : IsLieAbelian A.Carrier) :
    IsSubexponentiallyAmenableLieObject (k := k) A := by
  classical
  let S : Finset A.Carrier → LieSubalgebra k A.Carrier :=
    fun s => LieSubalgebra.lieSpan k A.Carrier (s : Set A.Carrier)
  apply IsSubexponentiallyAmenableLieObject.directedUnion A
    (Finset A.Carrier) S
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact LieSubalgebra.lieSpan_mono Finset.subset_union_left
    · exact LieSubalgebra.lieSpan_mono Finset.subset_union_right
  · apply top_unique
    intro x _hx
    exact (le_iSup S {x})
      (LieSubalgebra.subset_lieSpan (by simp))
  · intro s
    let _ : FiniteDimensional k (A.ofSubalgebra (S s)).Carrier := by
      change FiniteDimensional k (S s)
      dsimp [S]
      exact finiteDimensional_lieSpan_finset_of_isLieAbelian k hA s
    exact isSubexponentiallyAmenableLieObject_of_finiteDimensional k
      (A.ofSubalgebra (S s))

/-- The manuscript inclusion `EL ⊆ SL`. -/
theorem IsElementaryLieObject.isSubexponentiallyAmenable
    {A : LieAlgebraObject.{u, u} k}
    (hA : IsElementaryLieObject.{u, u, u} A) :
    IsSubexponentiallyAmenableLieObject (k := k) A := by
  induction hA with
  | finiteDimensional A hfd =>
      let _ : FiniteDimensional k A.Carrier := hfd
      exact isSubexponentiallyAmenableLieObject_of_finiteDimensional k A
  | abelian A hAb =>
      exact isSubexponentiallyAmenableLieObject_of_isLieAbelian k A hAb
  | extension A I _ _ hI hQ =>
      exact IsSubexponentiallyAmenableLieObject.extension A I hI hQ
  | directedUnion A ι S hdir hsup _ hS =>
      exact IsSubexponentiallyAmenableLieObject.directedUnion
        A ι S hdir hsup hS

/-- Unbundled membership in `SL`. -/
def IsSubexponentiallyAmenableLieAlgebra (L : Type u)
    [LieRing L] [LieAlgebra k L] : Prop :=
  IsSubexponentiallyAmenableLieObject (k := k) (LieAlgebraObject.of k L)

theorem wittAlgebra_subexponentiallyAmenable [CharZero k] :
    IsSubexponentiallyAmenableLieAlgebra (k := k) (WittAlgebra k) :=
  IsSubexponentiallyAmenableLieObject.subexponential
    (LieAlgebraObject.of k (WittAlgebra k))
    (wittAlgebra_hasSubexponentialLieGrowth k)

/-- Theorem H, characteristic-zero witness form: `SL` contains the Witt
algebra whereas `EL` does not. -/
theorem exists_subexponentiallyAmenable_not_elementarilyAmenable
    [CharZero k] :
    ∃ L : LieAlgebraObject k,
      IsSubexponentiallyAmenableLieObject (k := k) L ∧
        ¬ IsElementaryLieObject.{u, u, u} L := by
  refine ⟨LieAlgebraObject.of k (WittAlgebra k),
    wittAlgebra_subexponentiallyAmenable k, ?_⟩
  exact wittAlgebra_not_elementarilyAmenable k

/-- Theorem H: the elementary and subexponentially amenable classes are
distinct. -/
theorem elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras
    [CharZero k] :
    (∃ L : LieAlgebraObject k,
      IsSubexponentiallyAmenableLieObject (k := k) L ∧
        ¬ IsElementaryLieObject.{u, u, u} L) :=
  exists_subexponentiallyAmenable_not_elementarilyAmenable k

/-!
## The positive-characteristic input

The construction of the self-similar Petrogradsky--Shestakov--Zelmanov
algebra, and the structural results about it used in the article, are taken
from reference [3].  We deliberately isolate that external input here rather
than introducing a partial formalization of self-similar Lie algebras.
-/

set_option warningAsError false in
/-- Reference [3], packaged in precisely the form needed for Theorem H: over
a field of prime positive characteristic there is a subexponential-growth
Lie algebra outside the elementary hierarchy.

This is the sole admitted input concerning the self-similar
Petrogradsky--Shestakov--Zelmanov construction. -/
theorem exists_psz_subexponential_not_elementary
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ L : LieAlgebraObject k,
      IsSubexponentiallyAmenableLieObject (k := k) L ∧
        ¬ IsElementaryLieObject.{u, u, u} L := by
  sorry

/-- The positive-characteristic case of Theorem H, deduced directly from
the cited PSZ input. -/
theorem exists_subexponentiallyAmenable_not_elementarilyAmenable_of_charP
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ L : LieAlgebraObject k,
      IsSubexponentiallyAmenableLieObject (k := k) L ∧
        ¬ IsElementaryLieObject.{u, u, u} L :=
  exists_psz_subexponential_not_elementary k p

/-- Theorem H over an arbitrary field: `EL` and `SL` are distinct.  The
characteristic-zero branch is the proved Witt-algebra construction; the
positive-characteristic branch invokes the isolated result from reference
[3]. -/
theorem elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras_general :
    ∃ L : LieAlgebraObject k,
      IsSubexponentiallyAmenableLieObject (k := k) L ∧
        ¬ IsElementaryLieObject.{u, u, u} L := by
  let p := ringChar k
  let : CharP k p := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k p with hp | hp
  · let : Fact p.Prime := ⟨hp⟩
    exact exists_psz_subexponential_not_elementary k p
  · let : CharP k 0 := CharP.congr p hp
    let : CharZero k := CharP.charP_to_charZero k
    exact exists_subexponentiallyAmenable_not_elementarilyAmenable k

end

end HopfAmenability
