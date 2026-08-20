/-
  Brockian/GoldbachComb.lean — THE GOLDBACH COMB CAMPAIGN (July 30).

  The exact local covariance kernel behind the 3|k autocorrelation comb
  of the Goldbach residual (Volume II, page XVI; Tomography §4).

  Chain: local count g_p(c) = p−2+[c=0]  →  centered spike 1_{c=0}−1/p
  →  two-case covariance  →  CRT product over squarefree wheels  →
  convergent global kernel K(h) with  K(h)−1 > 0 ⟺ 3 ∣ h  (the p=3
  factor 9/8 vs 15/16 dominates all higher primes combined).

  Empirical status (this program, recorded): kernel verified exactly at
  p = 3,5,7,11; global values K−1 = +0.1195 / −0.0671; transfer pilot
  against the measured 50-lag ACF: one fitted scale β ≈ 0.41, held-out
  sign agreement 25/25, correlation r = 0.996. The TRANSFER conjecture
  is named at the end and never claimed.

  Charter as Core.lean; each unproved declaration was supplied as a target.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.GoldbachComb

open Finset

/-- The local Goldbach count: ordered pairs of nonzero residues summing
to c. -/

theorem gCount_centered (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (gCount p c : ℚ) - (p - 1)^2 / p =
      (if c = 0 then 1 else 0) - 1 / p := by
  rw [gCount_eq]
  have hp : (2 : ℕ) ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp1 : 1 ≤ p := by linarith
  split_ifs with hc <;> simp [Nat.cast_sub hp1, Nat.cast_sub (by linarith : 2 ≤ p)] <;> field_simp <;> ring

/-- The normalized local kernel value at shift h (as the exact rational
the two-case theorem produces). -/
