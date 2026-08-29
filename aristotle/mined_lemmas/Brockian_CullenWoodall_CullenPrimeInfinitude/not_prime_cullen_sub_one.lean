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

/-
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem not_prime_cullen_sub_one (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ (cullen (p - 1)).Prime := by
  have hodd : p ≠ 2 := by omega
  have hdvd : p ∣ cullen (p - 1) := prime_dvd_cullen_sub_one p hp hodd
  intro hprime
  have hle : p = cullen (p - 1) ∨ p = 1 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
    · exact Or.inr h
    · exact Or.inl h.symm
  -- but `C (p-1) = (p-1) * 2^(p-1) + 1 > p`
  have hgrow : p < cullen (p - 1) := by
    have h1 : p ≤ 2 ^ (p - 1) := by
      calc p ≤ 2 ^ p := Nat.le_of_lt (Nat.lt_two_pow_self)
        _ ≤ 2 ^ (p - 1) * 2 := by
            rw [← pow_succ]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ (p - 1) * 2 := le_rfl
      -- refine below
    have h2 : 2 ≤ p - 1 := by omega
    have h3 : p < (p - 1) * 2 ^ (p - 1) := by
      have : 2 * p ≤ (p - 1) * 2 ^ (p-1) := by
        have hb : 2 ≤ 2 ^ (p - 1) := by
          calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 * p ≤ 2 * (2 ^ (p-1)) := by omega
          _ ≤ (p - 1) * 2 ^ (p - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold cullen; omega
  omega

/-- **Infinitely many Cullen numbers are composite.** -/
