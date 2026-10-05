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

def rounds : ℕ → ℕ
  | 0 => 0
  | (n + 1) => rounds ((n + 1) / 2) + 1
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

