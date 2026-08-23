# Codex instructions for the Amenability Lean project

This repository contains a Lean 4 / current-mathlib formalization of a
coalgebraic rounding theorem.

Before substantial work, read:

    docs/LEAN_ROUNDING_PROOF.md

That file is the authoritative handoff from the preceding ChatGPT
development session. Inspect the existing `.lean` files before changing
them: many delicate API/coercion issues have already been resolved.

## Working rules

- Lean 4, current mathlib.
- Local project imports are qualified, e.g.
  ```lean
  import Amenability.DensityFiltration
  import Amenability.FiniteSubcoalgebra
  ```
- Every new Lean source begins exactly with:
  ```lean
  /-
  Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
  -/
  ```
- Do not use `sorry`.
- Compile modified files. Fix all errors before moving to dependent files.
- Prefer small, dependency-ordered changes. Do not rewrite already-working
  proofs merely for style.
- Use `omit [...] in` systematically when ambient section assumptions or
  typeclasses are genuinely unused.
- Avoid bare `ext x` on tensor-product domains when `x` is subsequently
  used for tensor induction. Prefer:
  ```lean
  apply LinearMap.ext
  intro x
  ```
- Avoid coercion-sensitive rewriting with bundled coalgebra morphisms.
  Prefer `change`, explicit `.toLinearMap`, and `calc`.
- When a construction parameter is inferred implicitly, use named arguments
  such as `(A := A)` rather than relying on positional argument order.
- Proposition-valued declarations should normally be `theorem`, not `def`.
- If a typeclass hypothesis is only needed by one or two declarations, put
  it on those declarations rather than at section level.
- Use `push Not`, not `push_neg`.
- Do not introduce duplicate proof terms for structural propositions when
  they occur inside data-dependent definitions. Reuse the exact proof term
  used by the definition when possible; this avoids proof-irrelevance
  elaboration mismatches.

## Current task

Continue proving the main coalgebraic rounding theorem.

The existing baseline files are already in the repository. The newer proof
files are being compiled one by one.

Current known state:

- `CoalgebraDensityTransfer.lean` has been corrected and compiles.
- `TransferDimensions.lean` and `TransferInequality.lean` have user-corrected
  compiled versions in the repository.
- `SplitTensorFiltration.lean` is the next file being checked. Previous
  errors were caused by:
  - passing `A` positionally where Lean inferred it implicitly;
  - a missing
    `Mathlib.LinearAlgebra.TensorProduct.RightExactness` import;
  - fragile simplification in the kernel proof.
  Use named arguments such as `(A := A)` throughout.
- The remaining new files depend on this one; compile them in dependency
  order rather than debugging several simultaneously.

When a file compiles, proceed to its immediate dependent and keep
`docs/LEAN_ROUNDING_PROOF.md` up to date if theorem names or interfaces
change materially.
