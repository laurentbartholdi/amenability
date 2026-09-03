# Coalgebraic rounding theorem — Lean handoff

## Current public architecture

`HopfAmenability.lean` is now the common specialization layer for amenable
cocommutative Hopf algebras.  It defines `IsAmenableHopfAlgebra`, bundles the
Hopf morphisms needed to state Hopf-subalgebra and cleft-extension permanence,
and exposes the augmentation-associated-graded amenability interface.
`LieAmenability.lean` and `GroupAmenability.lean` import this common layer.
Theorem D packages the PBW inclusion and quotient maps into these Hopf
interfaces for its subalgebra and extension clauses.

The main proof now works directly for a cocommutative Hopf algebra acting on
an arbitrary Hopf-module coalgebra.  Its public endpoint is
`HopfAmenability.exists_finiteSubcoalgebra_action_ratio_le` in
`HopfModuleCoalgebraRounding.lean`.  The regular action on the Hopf algebra is
the short corollary `HopfAmenability.exists_finiteSubcoalgebra_ratio_le` in
`CoalgebraRounding.lean`.

The two opt-in specializations are deliberately outside the generic import
chain:

- `LieAmenability.lean` supplies the universal-enveloping-algebra action and
  proves `isAmenableLieModule_iff_hasFolnerSubspaces`;
- `GroupAmenability.lean` supplies the linearized group action and proves
  `isAmenableGroupAction_iff_hasFolnerSubspaces`, whose group-specific linear
  condition is named `HasGroupFolnerSubspaces` in parallel with
  `HasLieFolnerSubspaces`.

The augmentation-associated-graded endpoint is unconditional.
`AssociatedGradedHopf.lean` and `AssociatedGradedHopfModule.lean` install the
actual Hopf and Hopf-module-coalgebra structures. `FilteredInitial.lean`
constructs homogeneous lifts and proves the finite-dimensional telescoping
formula for initial forms. `AugmentationAssociatedGraded.lean` applies this
to the separated augmentation quotient and proves compatibility with action
expansion. Consequently `TheoremJ.lean` no longer takes an
`AugmentationAssociatedGradedData` argument.

The standard coalgebra, cocommutativity, bialgebra, and Hopf instances for a
universal enveloping algebra are isolated in
`UniversalEnvelopingCoalgebra.lean`, under `namespace Coalgebra`, so that the
file can serve as a future Mathlib contribution.  Generic tensor helpers live
in `TensorProductMap.lean` and `TensorContraction.lean` under the appropriate
generic namespaces.

The sections below document the older dual proof and remain useful as
historical implementation notes.  That proof is retained under
`Amenability/Dead` and is not part of the current main dependency chain.

## Namespace convention

Generic coalgebra, comodule, and subcoalgebra infrastructure belongs in
`Coalgebra`; density filtrations, Hopf and Lie actions, rounding, and
amenability belong in `HopfAmenability`.

TODO for a separate namespace refactor: the generic declarations
`IsSubcoalgebra`, `FiniteSubcoalgebra`, `range_mapIncl_self_eq_inf`,
`tensorSquareIntersectionProperty`, and the subcoalgebra ambient-image
infrastructure still live in `HopfAmenability`. They are intentionally not
moved as part of the Lie-rounding cleanup because that change has a large
dependency footprint.

## 1. Goal

We are formalizing a coalgebraic version of the Følner/rounding argument.

Let `k` be a field, `H` a cocommutative Hopf algebra over `k`, and
`F ⊆ H` a finite-dimensional subcoalgebra. For a finite-dimensional
subspace `E ⊆ H`, write

\[
E^+ := F E.
\]

The target rounding statement is:

> For every nonzero finite-dimensional subspace `E ⊆ H`, there exists a
> nonzero finite-dimensional subcoalgebra `C ⊆ H` such that
> \[
> \frac{\dim F C}{\dim C}
> \le
> \frac{\dim F E}{\dim E}.
> \]

The transfer theorem currently uses the split-dual hypothesis:

> Every simple module over `F*` is one-dimensional over `k`.

Equivalently, `F*` has a composition series by ideals with one-dimensional
successive quotients. Equivalently for finite-dimensional coalgebras, `F`
is pointed.

Over an algebraically closed field every finite-dimensional
cocommutative coalgebra is pointed, so the split condition is automatic.

Do not revive the old notation `T_F(C)`. Use only `E^+`, `C^+`, etc.

---

## 2. Mathematical proof architecture

### 2.1 Density filtration

For a finite-dimensional subspace `X` in a finite-dimensional ambient
coalgebra and a subcoalgebra `C`, define

\[
r_X(C)=\dim(X\cap C),
\qquad
\Phi_{X,t}(C)=r_X(C)-t\dim C.
\]

Let `C_t(X)` be the unique largest maximizer of `Φ_{X,t}`.

Established facts:

1. Supermodularity:
   \[
   r_X(C)+r_X(D)
   \le
   r_X(C+D)+r_X(C\cap D).
   \]

2. Dimension modularity.

3. The largest maximizer exists and is unique.

4. Antitonicity:
   \[
   0<s<t \implies C_t(X)\subseteq C_s(X).
   \]

5. For sufficiently small positive `t`,
   `C_t(X)` is the smallest subcoalgebra containing `X`.

6. For `t > 1`, `C_t(X)=0`.

7. The filtration takes finitely many values.

8. Mass identity:
   \[
   \int_0^1 \dim C_t(X)\,dt = \dim X.
   \]

9. Semistability. If `C=C_t(X)` and `U=X∩C`, then for every subcoalgebra
   `B⊆C`,
   \[
   \dim U-\dim(U\cap B)
   \ge
   t(\dim C-\dim B).
   \tag{S}
   \]

The density code works in a finite-dimensional ambient subcoalgebra `G`.

---

### 2.2 Dual form of semistability

Let

\[
A=C^*,
\qquad
K=U^\perp\subseteq A.
\]

For a subcoalgebra `B⊆C`, let `I=B^\perp`. Then

\[
\dim I=\dim C-\dim B
\]

and

\[
I\cap K=(B+U)^\perp,
\]

so

\[
\dim I/(I\cap K)
=
\dim U-\dim(U\cap B).
\]

Thus (S) becomes

\[
\boxed{
\dim I/(I\cap K)\ge t\dim I
\quad\text{for every ideal }I\triangleleft A.
}
\tag{A}
\]

Important: `K` is only a vector subspace, not generally an ideal.

A remaining ingredient needed by the formal transfer theorem is the
finite-dimensional converse:

> Every ideal subspace of the convolution dual `C*` is the annihilator of
> a subcoalgebra of `C`.

This is implemented in the newer `IdealCoannihilator.lean` file and must
be compiled/verified.

---

### 2.3 Split transfer

Let

\[
R=F^*.
\]

Choose an ideal filtration

\[
0=R_0\subset R_1\subset\cdots\subset R_n=R
\]

with each quotient `R_i/R_{i-1}` one-dimensional.

Let

\[
Q=(FC)^*.
\]

Multiplication `F⊗C → FC` is a surjective coalgebra morphism, hence dual
multiplication gives an injective algebra map

\[
Q\hookrightarrow R\otimes A.
\]

For each layer choose the corresponding character

\[
\chi_i:R\to k.
\]

Define

\[
\rho_i:Q\to A,
\qquad
\rho_i=(\chi_i\otimes\mathrm{id})|_Q.
\]

Concretely, if `g_i∈F` represents `χ_i`, then

\[
\rho_i(\varphi)(c)=\varphi(g_i c).
\]

Since `χ_i` is an algebra character, `g_i` is group-like. In a Hopf
algebra, multiplication by a group-like element is injective, using the
antipode. Duality therefore makes `ρ_i` surjective.

For a subcoalgebra `D⊆FC`, let

\[
J=D^\perp\triangleleft Q.
\]

Filter

\[
Q_i=Q\cap(R_i\otimes A),
\qquad
J_i=J\cap Q_i.
\]

The coefficient map on the `i`-th layer induces

\[
J_i/J_{i-1}\hookrightarrow A
\]

with ideal image `M_i`.

Let

\[
N=J\cap(R\otimes K).
\]

Then the image of the `i`-th layer of `N` lies in `M_i∩K`.

Summing the semistability inequalities gives

\[
\dim J/N
\ge
\sum_i\dim M_i/(M_i\cap K)
\ge
t\sum_i\dim M_i
=
t\dim J.
\]

Translating annihilator dimensions yields the transfer inequality

\[
\boxed{
\dim FU-\dim(FU\cap D)
\ge
t(\dim FC-\dim D).
}
\tag{T}
\]

This is the main algebraic engine.

---

### 2.4 Pointwise density functoriality

Apply (T) with

\[
C=C_t(E),
\qquad
U=E\cap C.
\]

Let `D=C_t(FE)`. By maximality of `D` and the transfer inequality one
obtains

\[
\boxed{
F C_t(E)\subseteq C_t(FE).
}
\]

A generic density lemma proving this implication has already been written
as `DensityTransfer.lean`, and its coalgebra wrapper as
`CoalgebraDensityTransfer.lean`.

`CoalgebraDensityTransfer.lean` has now been corrected and compiles.

The key corrected proof avoids introducing a second
`SubcoalgebraInfClosed` proof term. It uses one local admissible family

```lean
let 𝓛 :=
  subcoalgebraAdmissibleFamily G
    (subcoalgebraInfClosed (k := k) (H := H) G)
```

then `change`s both the transfer hypothesis and target to use exactly this
`𝓛`.

---

### 2.5 Averaging

From the pointwise inclusion,

\[
\dim F C_t(E)\le \dim C_t(FE)
\]

for all `t`.

Using the mass identity,

\[
\int_0^1 \dim F C_t(E)\,dt
\le
\dim FE,
\qquad
\int_0^1 \dim C_t(E)\,dt
=
\dim E.
\]

Set

\[
\alpha=\frac{\dim FE}{\dim E}.
\]

If every nonzero `C_t(E)` had
`dim F C_t(E) > α dim C_t(E)`, integrating would contradict the two mass
identities. Hence for some `t` with `C_t(E)≠0`,

\[
\dim F C_t(E)\le \alpha\dim C_t(E).
\]

That `C_t(E)` is the required rounded subcoalgebra.

The Lean implementation should probably avoid measure theory: the density
filtration has finitely many values, so use its finite jump/step
description and a finite weighted-average lemma already present in
`RoundingCore.lean`.

---

## 3. Lean conventions discovered during development

### 3.1 Exact source banner

Every new `.lean` file must begin exactly:

```lean
/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
```

### 3.2 Imports

Local imports are qualified:

```lean
import Amenability.DensityFiltration
import Amenability.FiniteSubcoalgebra
```

Mathlib imports are normal.

Recent missing imports that mattered:

```lean
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
```

### 3.3 `omit`

Use Lean's `omit [...] in` form when assumptions are genuinely unused.

Example:

```lean
omit [CoalgebraStruct k C] [Coalgebra k H] in
theorem tensorSquare_injective ... := by
  ...
```

Do not omit assumptions required merely to form a statement type.

### 3.4 Coalgebra pullback constructor

`CoalgebraInjective.lean` is user-validated.

The important constructor is

```lean
@[instance_reducible]
noncomputable def coalgebraOfInjectiveCoalgHom
    (f : C →ₗc[k] H)
    (hf : Function.Injective f) :
    Coalgebra k C := by
  ...
```

`@[instance_reducible]` is intentional. It is useful for instance-producing
definitions used via

```lean
letI := coalgebraOfInjectiveCoalgHom f hf
```

without making them globally reducible.

### 3.5 Bundled coalgebra morphisms and tensor products

Avoid rewrites that rely on coercions such as

```lean
rw [CoalgHomClass.map_comp_comul_apply]
```

when the target contains `TensorProduct.map f.toLinearMap f.toLinearMap`.

Safer pattern:

```lean
change ...
calc
  _ = TensorProduct.map f.toLinearMap f.toLinearMap (...) := by ...
  _ = ... := by
    exact CoalgHomClass.map_comp_comul_apply f x
```

A structural tensor coalgebra morphism was introduced:

```lean
CoalgHom.tensorMapStruct
```

Use it rather than coercion-sensitive tensor coalgebra maps when possible.

### 3.6 Tensor induction

Do not write

```lean
apply WithConv.ext
ext z
induction z using TensorProduct.induction_on
```

because `ext` may decompose the tensor and bind `z` at the wrong type.

Use:

```lean
apply WithConv.ext
apply LinearMap.ext
intro z
induction z using TensorProduct.induction_on with
```

### 3.7 Implicit parameters

Several newer tensor definitions infer the algebra/module type parameter.
Calls such as

```lean
S.tensorFiltration A j
```

may be parsed as passing `A` in the index position.

Use:

```lean
S.tensorFiltration (A := A) j
S.tensorFiltrationEquiv (A := A) j
S.tensorCoeff (A := A) i
S.tensorLayerCoeff (A := A) i
```

throughout.

### 3.8 Proof irrelevance in dependent structures

Do not casually introduce

```lean
let hInf : SubcoalgebraInfClosed ... := ...
```

if the definition being unfolded contains its own proof of the same
proposition.

Even though proofs are propositionally irrelevant, dependent data such as

```lean
subcoalgebraAdmissibleFamily G hInf
```

may fail to unify definitionally with the same construction built from a
different proof term.

Prefer reusing the exact proof term occurring in the definition and use
`change`.

---

## 4. Existing project files and status

The repository contains the original 24-file development plus the newer
12-file continuation.

### 4.1 Earlier baseline

The following files form the established base. The user has already
corrected the 24-file batch locally; do not replace them with older
generated versions.

1. `RoundingCore.lean`
   - `exists_ratio_le_of_weighted_average`
   - `layer_transfer`
   - `RoundingCertificate`
   - `LayerCertificate`

2. `DensityLattice.lean`
   - admissible-family density lattice
   - supermodularity
   - largest maximizer
   - semistability
   - jump identity

3. `DensityExistence.lean`
   - finite numerical profiles
   - construction of `densitySubspace`

4. `DensityFiltration.lean`
   - score nonnegative
   - bot for `t>1`
   - antitone
   - semistable
   - jump identity

5. `SubcoalgebraBasic.lean`
   - custom predicate:
     ```lean
     def IsSubcoalgebra (C : Submodule k H) : Prop :=
       ∀ ⦃x : H⦄, x ∈ C →
         Coalgebra.comul (R := k) x ∈
           LinearMap.range (TensorProduct.mapIncl C C)
     ```
   - no bundled mathlib `Subcoalgebra`

6. `CoalgebraDensity.lean`
   - finite ambient `G`
   - `subcoalgebraAdmissibleFamily`
   - coalgebra density wrappers

7. `SubcoalgebraIntersectionReduction.lean`

8. `TensorSquareIntersection.lean`

9. `CoalgebraDensityClosed.lean`

10. `BialgebraSubcoalgebra.lean`

11. `FiniteSubcoalgebraProduct.lean`

12. `DualSemistability.lean`

13. `SubcoalgebraCoalgebraStruct.lean`

14. `CoalgebraInjective.lean`
   - user-validated

15. `SubcoalgebraCoalgebra.lean`

16. `FiniteSubcoalgebra.lean`

17. `SubcoalgebraCoalgHom.lean`

18. `FiniteSubcoalgebraMul.lean`

19. `CoalgHomDual.lean`

20. `DualTensorAlgebra.lean`

21. `FiniteSubcoalgebraDualEmbedding.lean`

22. `SplitDual.lean`

23. `TransferData.lean`

24. `TransferDimensions.lean`

`TransferDimensions.lean` has a user-saved corrected version.

25. `TransferInequality.lean`
   - added after the original 24
   - user corrected missing imports / `open Module`
   - use the repository version as authoritative
   - proves telescoping and
     ```lean
     FilteredTransferData.filtered_transfer_finrank
     ```

### 4.2 New proof continuation

The continuation batch contains:

- `SplitTensorFiltration.lean`
- `PullbackTransferData.lean`
- `DensityTransfer.lean`
- `CoalgebraDensityTransfer.lean`
- `SplitTensorTransferData.lean`
- `ConvolutionAnnihilator.lean`
- `IdealCoannihilator.lean`
- `CoalgebraTransferAbstract.lean`
- `SplitDualRepresentatives.lean`
- `CharacterRepresentativeGroupLike.lean`
- `FiniteSubcoalgebraTransferEvaluation.lean`
- `FiniteSubcoalgebraTransfer.lean`

These were generated to continue the proof and are **not all validated**.

Current status:

#### Validated through the algebraic transfer theorem (2026-08-22)

The dependency chain from `SplitTensorFiltration.lean` through
`FiniteSubcoalgebraTransfer.lean` has now been compiled successfully against
the current mathlib.  In particular, the following all compile:

- `SplitTensorFiltration.lean`
- `SplitTensorTransferData.lean`
- `PullbackTransferData.lean`
- `ConvolutionAnnihilator.lean`
- `IdealCoannihilator.lean`
- `CoalgebraTransferAbstract.lean`
- `SplitDualRepresentatives.lean`
- `CharacterRepresentativeGroupLike.lean`
- `FiniteSubcoalgebraTransferEvaluation.lean`
- `FiniteSubcoalgebraTransfer.lean`
- `CoalgebraDensityTransfer.lean`

The interface of `finiteSubcoalgebra_transfer` explicitly includes the split
filtration parameter `S`; this is required because `S` occurs only in the
proof, not in the displayed inequality.

Current mathlib exposes `dualTensorHom` and
`dualTensorHom_bijective` in the root namespace (not under
`TensorProduct`).  `Subspace.dualLift` should likewise be called with its
namespace explicit when the subspace is represented by `Submodule` notation.

At that validation point, the next missing source-level bridge was to combine
`finiteSubcoalgebra_transfer` with
`le_subcoalgebraDensitySubspace_of_transfer` to prove the pointwise inclusion
`F C_t(E) ≤ C_t(FE)`.  After that, a new finite step/jump construction must
package the density mass identities into `RoundingCertificate`; no existing
file then performed either step.  The bridge has since been implemented as
recorded below.

#### Ambient transfer and pointwise product inclusion (2026-08-22)

The ambient bridge has now been implemented and compiled in three new files:

- `SubcoalgebraAmbient.lean` provides `ambientImageEquiv`,
  `finrank_ambientImage`, `ambientImage_comap_eq_of_le`,
  `isSubcoalgebra_ambientImage_iff`, and
  `finiteSubcoalgebraOfAmbientImage`.
- `FiniteSubcoalgebraTransferAmbient.lean` provides
  `SplitDualFiltration.ambientImage_leftProductSubspace` and
  `SplitDualFiltration.finiteSubcoalgebra_transfer_ambient`.
- `DensityProductTransfer.lean` provides
  `mul_subcoalgebraDensitySubspace_le`, the pointwise inclusion from the
  source ambient `G` to the target ambient `F.carrier * G`.

Thus the next missing part is now only the finite step/jump construction and
the packaging of the two density mass identities into `RoundingCertificate`.

#### `CoalgebraDensityTransfer.lean`

Corrected by the user/ChatGPT iteration and now confirmed to compile.

#### `SplitTensorFiltration.lean`

Currently the next file being compiled.

Previously reported errors:

- `A : Type w` was being read as a `Fin (...)` argument in calls such as
  `S.tensorFiltration A`.
- same issue for:
  - `tensorFiltrationMap_injective`
  - `tensorFiltrationEquiv`
  - `tensorCoeff`
  - `tensorLayerCoeff`
- missing theorem due missing import:
  ```lean
  TensorProduct.rTensor_exact
  ```
- import needed:
  ```lean
  import Mathlib.LinearAlgebra.TensorProduct.RightExactness
  ```
- fragile `simp [tensorCoeff, hzker]` produced semilinear metavariables.

Required coding pattern:

```lean
S.tensorFiltration (A := A) j
S.tensorFiltrationEquiv (A := A) j
S.tensorCoeff (A := A) i
S.tensorLayerCoeff (A := A) i
```

For the kernel proof, prefer an explicit `change` followed by `rw [hzker]`
rather than unfolding everything with `simp`.

The current repository version may already contain some of these repairs.
Compile it before making further changes.

---

## 5. New-file intended interfaces

### 5.1 `SplitTensorFiltration.lean`

Purpose:

Given `S : SplitDualFiltration k R` and a `k`-algebra `A`, construct

\[
S_i\otimes A\subseteq R\otimes A
\]

and prove the kernel identity for the layer coefficient.

Use tensor exactness, not a hand-written tensor-kernel proof.

Relevant theorem from mathlib:

```lean
TensorProduct.rTensor_exact
```

exposed by:

```lean
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
```

### 5.2 `SplitTensorTransferData.lean`

Purpose:

Turn the tensor filtration into

```lean
FilteredTransferData k (R ⊗[k] A) A
```

with

\[
\rho_i(r\otimes a)=\chi_i(r)\,a.
\]

Be careful: `χ_i : R →ₐ[k] k`, so when constructing an algebra map to
`A`, compose with the scalar algebra map `k →ₐ[k] A`.

### 5.3 `PullbackTransferData.lean`

Purpose:

Pull filtered transfer data back along an injective algebra map

```lean
Q →ₐ[k] B
```

assuming the restricted `rho_i : Q → A` remain surjective.

This should isolate all `Q_i = Q ∩ filtration_i` bookkeeping.

### 5.4 `ConvolutionAnnihilator.lean`

Purpose:

Bridge ordinary dual annihilators and the convolution-dual type synonym

```lean
WithConv (Module.Dual k C)
```

Definitions include the intended ideas:

```lean
convDualAnnihilator
convUnderlying
convDualCoannihilator
```

and dimension identities.

### 5.5 `IdealCoannihilator.lean`

Purpose:

Prove that the coannihilator of an ideal subspace of the finite
convolution dual is a subcoalgebra.

Conceptual proof:

- Let `M ≤ C*` be an ideal.
- Let `B=M^⊥`.
- Show `Δ(B) ⊆ B⊗C` using convolution:
  for `c∈B`, `φ∈M`, `ψ∈C*`,
  \[
  (\phi\psi)(c)=0
  \]
  because `φψ∈M`.
- By cocommutativity also `Δ(B)⊆C⊗B`.
- Intersect:
  \[
  (B\otimes C)\cap(C\otimes B)=B\otimes B.
  \]

Existing tensor-square intersection lemmas should be reused.

### 5.6 `CoalgebraTransferAbstract.lean`

Purpose:

Combine annihilator dimensions with

```lean
FilteredTransferData.filtered_transfer_finrank
```

to prove the abstract transfer inequality.

Once `IdealCoannihilator.lean` compiles, remove any temporary hypothesis
saying that ideal coannihilators are subcoalgebras and use the actual
theorem.

### 5.7 `SplitDualRepresentatives.lean`

Purpose:

Represent:

- a split-filtration character `χ_i` by `g_i∈F`;
- the layer coefficient by an element `f_i∈F`.

Use finite-dimensional reflexivity / `Module.evalEquiv`.

### 5.8 `CharacterRepresentativeGroupLike.lean`

Purpose:

Prove that the representative `g_i` of an algebra character on `F*` is
group-like.

Then its ambient image in `H` is group-like.

### 5.9 `FiniteSubcoalgebraTransferEvaluation.lean`

Purpose:

For

\[
(FC)^*\hookrightarrow F^*\otimes C^*
\]

show:

\[
\rho_i(q)(c)=q(g_i c)
\]

and

\[
\operatorname{coeff}_i(q)(c)=q(f_i c).
\]

Use group-likeness and the Hopf antipode to prove multiplication by `g_i`
is injective, hence `rho_i` is surjective by duality.

### 5.10 `FiniteSubcoalgebraTransfer.lean`

Purpose:

Define the subspace `FU≤FC` and instantiate the abstract transfer theorem:

\[
t(\dim FC-\dim D)
\le
\dim FU-\dim(FU\cap D)
\]

for every subcoalgebra `D≤FC`.

This is the last algebraic theorem needed before the density argument.

---

## 6. Current compile order

Work in this order:

```text
SplitTensorFiltration
    ↓
SplitTensorTransferData
    ↓
PullbackTransferData
    ↓
ConvolutionAnnihilator
    ↓
IdealCoannihilator
    ↓
CoalgebraTransferAbstract
    ↓
SplitDualRepresentatives
    ↓
CharacterRepresentativeGroupLike
    ↓
FiniteSubcoalgebraTransferEvaluation
    ↓
FiniteSubcoalgebraTransfer
    ↓
CoalgebraDensityTransfer   (already compiling)
    ↓
pointwise FC_t(E) ≤ C_t(FE)
    ↓
finite weighted-average / mass argument
    ↓
main rounding theorem
```

`DensityTransfer.lean` is independent enough that it may already compile;
do not block the algebraic chain on it unnecessarily.

---

## 7. Mathlib APIs already confirmed useful

- `LinearMap.codRestrictOfInjective`
- `LinearEquiv.ofInjective`
- field flatness setup:
  ```lean
  attribute [local instance 1100]
    Module.Free.of_divisionRing Module.Flat.of_free
  ```
- `TensorProduct.map_injective_of_flat_flat`
- `Module.Flat.tensorProduct_mapIncl_injective_of_right`
- `Module.Flat.tensorProduct_mapIncl_injective_of_left`
- `TensorProduct.map_map`
- `TensorProduct.assoc`
- `LinearMap.rTensor_def`
- `LinearMap.lTensor_def`
- `TensorProduct.rTensor_exact`
- `LinearMap.rTensor_surjective`
- `LinearMap.lTensor_surjective`
- `TensorProduct.dualDistribEquiv`
- `Module.evalEquiv`
- `Subspace.dualAnnihilator_dualCoannihilator_eq`
- finite-dimensional annihilator dimension formulas
- `Bialgebra.mulCoalgHom`
- `CoalgHom.dualAlgHom`
- `WithConv.linearEquiv`
- `Algebra.TensorProduct.lid`
- `Algebra.TensorProduct.lift`

There is no bundled mathlib `Subcoalgebra`; this project deliberately uses
the predicate `IsSubcoalgebra`.

---

## 8. Known delicate points

### 8.1 Convolution dual types

`WithConv (Module.Dual k C)` is a type synonym carrying convolution
multiplication. Be explicit when crossing between it and ordinary
`Module.Dual k C`.

### 8.2 `TensorProduct.map`

`TensorProduct.map φ ψ` lands in `k⊗k`, not directly in `k`. Evaluation
of tensor-product duals requires the canonical `lid`.

This caused earlier errors in `DualTensorAlgebra.lean`.

### 8.3 Extensionality

Generic `ext` can choose tensor extensionality unexpectedly. Use explicit
`LinearMap.ext` when the domain is a tensor product.

### 8.4 `simp` and convolution

Avoid large

```lean
simp [definition1, definition2, ...]
```

calls through convolution/tensor definitions. They can destroy induction
hypothesis shapes or generate semilinear metavariables.

Prefer small `rw`, `change`, `simpa only`, and named intermediate lemmas.

### 8.5 Proposition proof parameters

Repeated proof terms inside data constructors can cause apparent type
mismatches. This happened in `CoalgebraDensityTransfer.lean`.

Reuse one exact proof term.

---

## 9. Final theorem packaging

After the finite-ambient theorem is complete, there may still be a wrapper
needed to place an arbitrary finite-dimensional `E⊆H` inside a
finite-dimensional subcoalgebra.

Structurally separate:

1. a theorem inside a finite-dimensional ambient subcoalgebra containing
   `E`;
2. a final theorem using the fundamental theorem of coalgebras to obtain
   such an ambient subcoalgebra.

Do not entangle this ambient-existence API with the transfer proof.

---

## 10. Recommended Codex workflow

For each file:

1. Read the file and its immediate imports.
2. Run Lean on that file.
3. Fix the **first real error**, not downstream cascades.
4. Recompile.
5. Once clean, move to the immediate dependent.
6. Preserve theorem names/interfaces when possible.
7. If an interface must change, update dependent files immediately.
8. Update this document only for material architectural/API changes.

The project owner is actively compiling locally, so small compile-clean
increments are preferable to speculative large rewrites.

---

## 11. Post-audit Lie/PBW and augmentation work

The public `IsAmenableLieAlgebra` now states the manuscript condition on
finite-dimensional subspaces of the Lie algebra and finite subcoalgebras of
its UEA.  `Amenability/LieGeneratorTest.lean` proves its equivalence with
`IsAlgebraicallyAmenableLieAlgebra`, the regular-action Følner predicate.

The ordered PBW basis is now characteristic-free.  Its independence proof
uses `pbwNormalFormRepresentation` and the left inverse
`pbwNormalFormMap`, avoiding the old factorial-valued convolution diagonal.
Consequently the public PBW basis, relative PBW basis, Theorem G permanence
maps, and the explicit Theorem I construction elaborate over an arbitrary
field.

`Amenability/LieGrowth.lean` contains the genuine constant-bearing
`IsSubexponentialSequence`, `HasSubexponentialLieGrowth`, and
`HasLocallySubexponentialGrowth`; the former unit-coefficient UEA condition
has been retained only under the truthful auxiliary name
`HasUnitCoefficientUEAGrowth`.

The Smith implication used by Theorem G is now formalized rather than
assumed.  `AscendingFiltrationBasis.lean` splits successive finite Lie-ball
layers and produces a basis indexed by first filtration degree.
`WeightedPBW.lean` proves that PBW straightening respects the resulting
positive weights, and `WeightedPBWGrowth.lean` proves the weighted-word
generating-function estimate.  `LieGrowth.lean` combines these results,
including fixed-dilation stability of subexponential sequences, to prove
`isAmenableLieAlgebra_of_locallySubexponentialGrowth`.  Theorem H then proves
both hierarchy inclusions `EL ⊆ SL` and `SL ⊆ AL` before separating the first
two classes.

For Theorem J, new concrete filtration lemmas live in
`Amenability/AugmentationFiltration.lean`.  Multiplication, action, the
degree-one coproduct estimate, tensor-filtration multiplication, and the
full augmentation-filtration coproduct estimate are proved there.  Continue
constructing the actual graded operations rather than adding fields to
`AugmentationAssociatedGradedData`.
