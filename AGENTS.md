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
- Do not use `sorry`, except for the single designated theorem
  `exists_psz_subexponential_not_elementary` implementing the external
  positive-characteristic PSZ construction.
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

## Stable architecture and assumptions

Follow `docs/ARCHITECTURE.md`: structural algebra, coalgebra, filtration, and
PBW code precedes amenability definitions; Theorems A--J then follow in
manuscript dependency order. Run `scripts/check_architecture.sh` after moves.

The only project-local assumptions are `takeuchiWigner_projective_left` and
the designated positive-characteristic PSZ proof. No other axiom, `sorry`,
`admit`, or conclusion-bearing proof package is permitted. Keep
`docs/LEAN_ROUNDING_PROOF.md` current when interfaces change materially.
