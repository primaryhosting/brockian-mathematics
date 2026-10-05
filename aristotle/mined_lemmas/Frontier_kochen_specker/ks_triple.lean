/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated verbatim as a module docstring just below the import
line, because Lean 4 does not allow a module docstring to precede import commands.
-/

import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

We work in the three–dimensional real Hilbert space `EuclideanSpace ℝ (Fin 3)`.
A *noncontextual hidden–variable assignment* for quantum mechanics in dimension `3`
is a function `f` which assigns to every (nonzero) vector `u` — i.e. to every rank–one
projection `|u⟩⟨u|` — a definite truth value `f u : Bool`, in such a way that for every
orthogonal triple of nonzero vectors (equivalently, for every orthogonal resolution of the
identity into three rank–one projections) *exactly one* of the three values is `true`.
The value assigned to a projection is required to depend only on the projection itself and
not on the orthogonal triple ("context") in which it is measured — this is exactly what
noncontextuality means, and it is built into the statement by letting `f` be a function of
the vector alone.

The Kochen–Specker theorem states that no such `f` exists.
-/

/-- The three–dimensional real Hilbert space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The vector of `E3` with coordinates `a`, `b`, `c`. -/

theorem ks_triple {f : E3 → Bool} (hf : IsKSColoring f) {u v w : E3}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0)
    (h1 : f u = false) (h2 : f v = false) (h3 : f w = false) : False := by
  rcases hf u v w hu hv hw huv huw hvw with ⟨k, -, -⟩ | ⟨-, k, -⟩ | ⟨-, -, k⟩ <;>
    simp [h1, h2, h3] at k

/-!
## The Peres configuration of 33 rays

The following 33 vectors have coordinates in `{0, ±1, ±√2}`; among them there are 16
orthogonal triples and 72 orthogonal pairs.  This configuration admits no
Kochen–Specker colouring.
-/

