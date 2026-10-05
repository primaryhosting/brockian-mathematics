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

theorem cross3_ne_zero (u v : E3) (hu : u ≠ 0) (hv : v ≠ 0) (h : ⟪u, v⟫ = 0) :
    cross3 u v ≠ 0 := by
  intro hc
  have e0 : (cross3 u v) 0 = 0 := by rw [hc]; rfl
  have e1 : (cross3 u v) 1 = 0 := by rw [hc]; rfl
  have e2 : (cross3 u v) 2 = 0 := by rw [hc]; rfl
  simp only [cross3, mk3_apply0, mk3_apply1, mk3_apply2] at e0 e1 e2
  rw [inner_expand] at h
  have key : (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) = 0 := by
    nlinarith [e0, e1, e2, h]
  rcases mul_eq_zero.1 key with hk | hk
  · exact hu (eq_zero_of_coords u
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)])
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)])
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]))
  · exact hv (eq_zero_of_coords v
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]))

/-!
## Vectors with coordinates in `ℤ[√2]`

The Kochen–Specker configuration we use (the 33 rays of Peres) has all coordinates in
`{0, ±1, ±√2}`, so we set up a small amount of exact arithmetic in `ℤ[√2]`.
-/

/-- The real number `a + b √2`. -/
