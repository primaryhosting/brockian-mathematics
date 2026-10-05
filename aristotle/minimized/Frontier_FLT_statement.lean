/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `Frontier.FLTFor n` says that the Fermat equation `x ^ n + y ^ n = z ^ n` has no solution
in positive integers. -/

def FLTFor (n : ℕ) : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- `Frontier.FLT` is the statement of Fermat's Last Theorem: for every exponent `n > 2`,
the equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers. -/

def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

lemma FLTFor_iff (n : ℕ) : FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h x y z hx hy hz
    exact h x y z (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- Fermat's Last Theorem for exponent `3` (base case). -/

theorem FLT_statement :
    (∀ p : ℕ, p.Prime → 5 ≤ p → FLTFor p) ↔ FLT := by
  constructor
  · intro h
    have key : FermatLastTheorem := by
      refine FermatLastTheorem.of_odd_primes fun p hp hodd => ?_
      rcases eq_or_ne p 3 with rfl | hp3
      · exact fermatLastTheoremThree
      · have h2 : 2 ≤ p := hp.two_le
        have h5 : 5 ≤ p := by
          obtain ⟨k, hk⟩ := hodd
          omega
        exact (FLTFor_iff p).1 (h p hp h5)
    intro n hn
    exact (FLTFor_iff n).2 (key n hn)
  · intro h p _ hp5
    exact h p (by omega)

end Frontier
