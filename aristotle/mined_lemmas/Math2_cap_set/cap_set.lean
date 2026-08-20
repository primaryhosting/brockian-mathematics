import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Filter Finset

/-- The *cap set number* `capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ`
containing no non-trivial three-term arithmetic progression (a *cap set*).

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, and `ThreeAPFree` is Mathlib's predicate saying
that `a + c = b + b` with `a, b, c` in the set forces `a = b` (hence `a = b = c`). -/

theorem cap_set :
    (fun n : ℕ ↦ (capSetNumber n : ℝ)) =o[atTop] (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (cornersTheoremBound ε)] with n hn
  have hpow : cornersTheoremBound ε ≤ 3 ^ n :=
    hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  have h := capSetNumber_le_of_le hε hpow
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h

end Math2

