import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

theorem localFactor_pos_six (p : ℕ) :
    0 < localFactor ({0, 4, 6, 10, 12, 16} : Finset ℕ) p := by
  apply localFactor_pos_of_small_primes
  intro q hq hle
  have hle6 : q ≤ 6 := by
    have hc : ({0, 4, 6, 10, 12, 16} : Finset ℕ).card = 6 := by decide
    omega
  interval_cases q <;> revert hq <;> simp [nu] <;> decide

end BrockianFrontier.SieveK5

