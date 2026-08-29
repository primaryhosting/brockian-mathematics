import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem zumkeller_5391411025 : Zumkeller 5391411025 := by
  refine ⟨{1, 23, 391, 135575, 8107385, 5391411025}, ?_, ?_⟩
  · intro d hd
    rw [Nat.mem_divisors]
    refine ⟨?_, by norm_num⟩
    fin_cases hd <;> norm_num
  · rw [sum_divisors_5391411025]
    decide

/-- `5391411025` is odd. -/
