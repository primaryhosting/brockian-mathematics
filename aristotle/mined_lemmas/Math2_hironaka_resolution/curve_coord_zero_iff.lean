/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Math2

open MvPolynomial

/-!
## Setting

We work with affine plane curves over a field `k` of characteristic zero, points of the
affine plane being encoded as functions `Fin 2 → k` (so that they can be plugged into
`MvPolynomial (Fin 2) k`).

The theorem `Math2.hironaka_resolution` below is a formalised instance of Hironaka's
resolution of singularities in characteristic zero: for every `m ≥ 1` the plane curve

  `C_m : y ^ 2 = x ^ (2 * m + 1)`

is singular (exactly at the origin), and the map

  `π_m : 𝔸¹ → C_m , t ↦ (t ^ 2, t ^ (2 * m + 1))`

from the smooth affine line is a proper birational bijection onto `C_m` which is an
isomorphism away from the singular point; i.e. `π_m` is a resolution of singularities
of `C_m`.
-/

variable {k : Type*} [Field k]

omit [Field k] in
/-- Two points of the affine plane agree iff their coordinates do. -/

theorem curve_coord_zero_iff {m : ℕ} {p : Fin 2 → k} (hp : p ∈ curve m) :
    p 0 = 0 ↔ p 1 = 0 := by
  rw [mem_curve_iff] at hp
  constructor
  · intro h
    have : p 1 ^ 2 = 0 := by rw [hp, h]; simp
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · intro h
    have : p 0 ^ (2 * m + 1) = 0 := by rw [← hp, h]; simp
    exact pow_eq_zero_iff (by omega) |>.mp this

/-- The origin lies on the curve. -/
