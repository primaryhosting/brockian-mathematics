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

theorem inner_kvec_eq_zero (a1 b1 a2 b2 a3 b3 c1 d1 c2 d2 c3 d3 : ℤ)
    (hA : a1 * c1 + 2 * b1 * d1 + (a2 * c2 + 2 * b2 * d2) + (a3 * c3 + 2 * b3 * d3) = 0)
    (hB : a1 * d1 + b1 * c1 + (a2 * d2 + b2 * c2) + (a3 * d3 + b3 * c3) = 0) :
    ⟪kvec a1 b1 a2 b2 a3 b3, kvec c1 d1 c2 d2 c3 d3⟫ = 0 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hA' : ((a1 : ℝ) * c1 + 2 * b1 * d1 + (a2 * c2 + 2 * b2 * d2) + (a3 * c3 + 2 * b3 * d3)) = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hA
  have hB' : ((a1 : ℝ) * d1 + b1 * c1 + (a2 * d2 + b2 * c2) + (a3 * d3 + b3 * c3)) = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hB
  rw [inner_expand]
  simp only [kvec, mk3_apply0, mk3_apply1, mk3_apply2, qv]
  linear_combination hA' + Real.sqrt 2 * hB' + ((b1 : ℝ) * d1 + (b2 : ℝ) * d2 + (b3 : ℝ) * d3) * hs

/-!
## The Kochen–Specker colouring condition
-/

/-- A *noncontextual hidden–variable assignment* (Kochen–Specker colouring) in dimension 3:
a `Bool`-valued function on nonzero vectors of `E3` such that for every orthogonal triple of
nonzero vectors exactly one of the three values is `true`. -/
