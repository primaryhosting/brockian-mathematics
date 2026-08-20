import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma gauss_sum_mul_conj (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) *
        (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) = (p : ℂ) := by
  rw [sum_mul_conj_sum]
  simp_rw [sum_shift p hp]
  simp

/-- The quadratic Gauss sum has magnitude √p: for an odd prime p,
    |∑_{k ∈ ℤ/p} exp(2πi k²/p)|² = p.

    (`Complex.abs` no longer exists in current Mathlib; the norm `‖·‖` on `ℂ` is the
    same function.) -/
