import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

theorem localFactor_pos_five (p : ℕ) :
    0 < localFactor ({0, 2, 6, 8, 12} : Finset ℕ) p := by
  apply localFactor_pos_of_small_primes
  intro q hq hle
  have hle5 : q ≤ 5 := by
    have hc : ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 := by decide
    omega
  interval_cases q <;> revert hq <;> simp [nu] <;> decide

/-- Positivity for a second admissible 5-tuple `{0,4,6,10,12}`. -/
