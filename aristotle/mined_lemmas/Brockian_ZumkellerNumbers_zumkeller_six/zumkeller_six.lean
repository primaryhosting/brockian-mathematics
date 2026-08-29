import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem zumkeller_six : Zumkeller 6 := by
  refine ⟨{1, 2, 3}, ?_, ?_⟩ <;> decide

end Brockian.ZumkellerNumbers

