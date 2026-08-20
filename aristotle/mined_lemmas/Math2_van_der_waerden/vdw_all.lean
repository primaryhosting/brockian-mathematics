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

theorem vdw_all (k : ℕ) : VDW k := by
  induction k with
  | zero =>
    intro L _
    exact ⟨1, fun c => ⟨0, 1, one_pos, by omega, fun i hi => absurd hi (by omega)⟩⟩
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact vdw_one
    · exact vdw_step hk ih

/-- **Van der Waerden's theorem.**  For any coloring of `ℕ` by finitely many colors and any
`k`, there is a monochromatic arithmetic progression of length `k` with positive common
difference. -/
