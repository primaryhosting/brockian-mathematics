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

theorem kvec_ne_zero (a1 b1 a2 b2 a3 b3 : ℤ)
    (h : ¬ (a1 = 0 ∧ b1 = 0) ∨ ¬ (a2 = 0 ∧ b2 = 0) ∨ ¬ (a3 = 0 ∧ b3 = 0)) :
    kvec a1 b1 a2 b2 a3 b3 ≠ 0 := by
  intro hc
  rcases h with h | h | h
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 0 = 0 := by rw [hc]; rfl
    simpa [kvec] using this
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 1 = 0 := by rw [hc]; rfl
    simpa [kvec] using this
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 2 = 0 := by rw [hc]; rfl
    simpa [kvec] using this

