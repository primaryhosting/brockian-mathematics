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

theorem param_paramInv (m : ℕ) {p : Fin 2 → k} (hp : p ∈ curve m) (h0 : p 0 ≠ 0) :
    param m (paramInv m p) = p := by
  have : p ∈ Set.range (param (k := k) m) := by rw [range_param]; exact hp
  obtain ⟨t, rfl⟩ := this
  have ht : t ≠ 0 := by
    intro h; apply h0; simp [h]
  rw [paramInv_param m ht]

/--
**Hironaka resolution of singularities (characteristic zero), formalised instance.**

Let `k` be a field of characteristic zero and `m ≥ 1`.  The affine plane curve
`C_m : y ^ 2 = x ^ (2 * m + 1)` is singular at the origin, and the origin is its only
singular point.  The map `π_m (t) = (t ^ 2, t ^ (2 * m + 1))` from the smooth affine line
`𝔸¹` is a bijection onto `C_m`, and it restricts to an isomorphism between
`𝔸¹ \ {0}` and `C_m` minus its singular point, with inverse `(x, y) ↦ y / x ^ m`.
Thus `π_m` is a resolution of singularities of `C_m`.
-/
