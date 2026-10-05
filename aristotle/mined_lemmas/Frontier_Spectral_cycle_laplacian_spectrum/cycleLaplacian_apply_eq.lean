/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

We model the cycle graph `C n` on the vertex set `ZMod n` and its graph Laplacian as the circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals.  Conjugating by the
discrete Fourier matrix `F j k = exp (2 π i j k / n)` diagonalises it, which identifies the spectrum
as `{2 - 2 cos (2 π k / n) : k ∈ range n}`.
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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`, indexed by `ZMod n`:
the circulant matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/

theorem cycleLaplacian_apply_eq (hn : 3 ≤ n) (j m : ZMod n) :
    cycleLaplacian n j m =
      2 * (if m = j then 1 else 0) - (if m = j + 1 then 1 else 0)
        - (if m = j - 1 then 1 else 0) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  have h2 : (2 : ZMod n) ≠ 0 := by
    have : ((2 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  have hA : (j - m = 1) ↔ m = j - 1 := by
    constructor <;> intro h <;> linear_combination -h
  have hB : (m - j = 1) ↔ m = j + 1 := by
    constructor <;> intro h <;> linear_combination h
  have e3 : ¬ (j + 1 = j - 1) := fun h => h2 (by linear_combination h)
  have e4 : ¬ (j - 1 = j + 1) := fun h => h2 (by linear_combination -h)
  have e5 : ¬ (j = j - 1) := fun h => h1 (by linear_combination h)
  unfold cycleLaplacian
  simp only [hA, hB]
  by_cases hjm : m = j
  · subst hjm
    have e1 : ¬ (m = m + 1) := fun h => h1 (by linear_combination -h)
    have e2 : ¬ (m = m - 1) := fun h => h1 (by linear_combination h)
    simp [e1, e2]
  · have hjm' : ¬ (j = m) := fun h => hjm h.symm
    by_cases hp : m = j + 1
    · simp [hp, e3, h1]
    · by_cases hq : m = j - 1
      · simp [hq, e4, e5, h1]
      · simp [hjm, hjm', hp, hq]

