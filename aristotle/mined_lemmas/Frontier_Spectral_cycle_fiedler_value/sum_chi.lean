/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma sum_chi [NeZero N] (t : ZMod N) :
    ∑ k : ZMod N, chi N (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht, chi_zero, Finset.card_univ, ZMod.card]
  · have key : chi N t * ∑ k : ZMod N, chi N (t * k) = ∑ k : ZMod N, chi N (t * k) := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _
        (fun k => by simp only [Equiv.coe_addRight, mul_add, mul_one, chi_add]; ring)
    have h2 : (chi N t - 1) * ∑ k : ZMod N, chi N (t * k) = 0 := by linear_combination key
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (by linear_combination h) (chi_ne_one ht)
    · exact h

/-- Parseval's identity for the discrete Fourier transform on `ZMod N`. -/
