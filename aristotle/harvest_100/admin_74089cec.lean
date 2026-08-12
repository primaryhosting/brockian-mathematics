/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The *partner* (or quasi-aliquot) function: `partner n = σ₁(n) - n - 1`, the sum of the
proper divisors of `n` other than `1`.  Subtraction is truncated natural subtraction. -/
def partner (n : ℕ) : ℕ := (sigma 1) n - n - 1

/-- `(m, n)` is a *betrothed* (quasi-amicable) pair when `m` and `n` are distinct positive
integers with `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ (sigma 1) m = m + n + 1 ∧ (sigma 1) n = m + n + 1

namespace Dynamics

/-- Basic rewriting of `partner`. -/
lemma partner_eq (n : ℕ) : partner n = (sigma 1) n - (n + 1) := by
  simp [partner, Nat.sub_sub]

/-- If `σ₁(n) = n + 1 + k` then `partner n = k`. -/
lemma partner_eq_of_sigma_eq {n k : ℕ} (h : (sigma 1) n = n + 1 + k) : partner n = k := by
  simp [partner_eq, h]

/-- Conversely, a *positive* value of `partner` determines `σ₁`. -/
lemma sigma_eq_of_partner_eq {n k : ℕ} (hk : 0 < k) (h : partner n = k) :
    (sigma 1) n = n + 1 + k := by
  rw [partner_eq] at h
  omega

/-- **Characterization of betrothed pairs as nontrivial positive `2`-cycles of `partner`.**

A pair `(m, n)` is a betrothed pair exactly when `m` and `n` are distinct positive naturals
with `partner m = n` and `partner n = m`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩
    · exact partner_eq_of_sigma_eq (by omega)
    · exact partner_eq_of_sigma_eq (by omega)
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩
    · have := sigma_eq_of_partner_eq hn hpm
      omega
    · have := sigma_eq_of_partner_eq hm hpn
      omega

/-- Sanity check: `(48, 75)` is the smallest betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · rw [ArithmeticFunction.sigma_one_apply]
      decide

end Dynamics

end BetrothedNumbers

end Brockian

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

