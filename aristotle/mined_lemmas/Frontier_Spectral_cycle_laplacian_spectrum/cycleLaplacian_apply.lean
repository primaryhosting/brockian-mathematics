import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

open Matrix Finset

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix (indexed by
`ZMod n`) with diagonal entries `2` and `-1` on the two cyclic off-diagonals. -/

lemma cycleLaplacian_apply (hn : 3 ≤ n) (i j : ZMod n) :
    cycleLaplacian n i j =
      2 * (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0)
        - (if j = i - 1 then 1 else 0) := by
  have h1 := one_ne_zero_zmod hn
  have h2 := two_ne_zero_zmod hn
  have hA : ∀ x : ZMod n, x ≠ x + 1 := fun x h => h1 (by linear_combination -h)
  have hB : ∀ x : ZMod n, x ≠ x - 1 := fun x h => h1 (by linear_combination h)
  have hC : ∀ x : ZMod n, x + 1 ≠ x - 1 := fun x h => h2 (by linear_combination h)
  have c2 : (i = j + 1) ↔ (j = i - 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  have c3 : (i = j - 1) ↔ (j = i + 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  simp only [cycleLaplacian, eq_comm (a := i) (b := j), c2, c3]
  by_cases hji : j = i
  · subst hji
    simp [hA j, hB j]
  · by_cases hj1 : j = i + 1
    · subst hj1
      simp [hji, hC i]
    · by_cases hj2 : j = i - 1
      · subst hj2
        simp [hji, hj1]
      · simp [hji, hj1, hj2]

/-- Multiplying a row of the Laplacian against an arbitrary vector. -/
