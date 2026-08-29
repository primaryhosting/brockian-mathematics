import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma rounds_le (ℓ : ℕ) : rounds ℓ ≤ Nat.log 2 ℓ + 1 := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · simp [rounds_zero]
    · rw [rounds_of_pos hpos]
      rcases Nat.lt_or_ge ℓ 2 with h2 | h2
      · interval_cases ℓ
        · simp [rounds_zero]
      · have hdiv : ℓ / 2 < ℓ := Nat.div_lt_self hpos (by norm_num)
        have := ih (ℓ / 2) hdiv
        have hlog : Nat.log 2 (ℓ / 2) + 1 = Nat.log 2 ℓ := by
          rw [Nat.log_div_base]
          have : 1 ≤ Nat.log 2 ℓ := Nat.log_pos (by norm_num) h2
          omega
        omega

/-- **Main induction** (Park–Pham iteration). For an `ℓ`-bounded hypergraph `H`, if `c` is a
lower bound for the cost of every cover of `H`, then `c` times the probability that the
`rounds ℓ`-round process fails to cover `H` is at most `1/30`. -/
