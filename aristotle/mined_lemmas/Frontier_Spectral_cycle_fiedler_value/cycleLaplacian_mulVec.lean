import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma cycleLaplacian_mulVec (h3 : 3 ≤ n) (v : ZMod n → ℝ) (i : ZMod n) :
    (cycleLaplacian n).mulVec v i = 2 * v i - v (i + 1) - v (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd one_pos h; omega
    simpa using this
  have h2 : (2 : ZMod n) ≠ 0 := by
    have : ((2 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd two_pos h; omega
    simpa using this
  have key : ∀ j : ZMod n, cycleLaplacian n i j * v j =
      (if j = i then 2 * v j else 0) + (if j = i + 1 then -v j else 0) +
        (if j = i - 1 then -v j else 0) := by
    intro j
    unfold cycleLaplacian
    by_cases hji : j = i
    · subst hji
      have e1 : j ≠ j + 1 := by intro h; exact h1 (by linear_combination -h)
      have e2 : j ≠ j - 1 := by intro h; exact h1 (by linear_combination h)
      simp [e1, e2]
    · have hij : i ≠ j := Ne.symm hji
      by_cases hj1 : j = i + 1
      · subst hj1
        have e2 : i + 1 ≠ i - 1 := by intro h; exact h2 (by linear_combination h)
        simp [hji, e2, hij]
      · by_cases hj2 : j = i - 1
        · subst hj2; simp [hji, hj1, hij]
        · simp [hji, hj1, hj2, hij]
  rw [Matrix.mulVec, dotProduct]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

omit [NeZero n] in
/-- The cycle Laplacian is a symmetric matrix. -/
