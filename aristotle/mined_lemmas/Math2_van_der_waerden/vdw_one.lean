/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/

theorem vdw_one : VDW 1 := by
  intro L _
  refine ⟨1, fun c => ⟨0, 1, one_pos, by omega, ?_⟩⟩
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- The color-focusing induction: assuming van der Waerden for length `k`, for every `s` there
is a bound `N` such that every coloring either has a monochromatic AP of length `k+1` or
`s` focused monochromatic APs of length `k` with distinct colors. -/
