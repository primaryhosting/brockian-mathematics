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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

theorem key_bound (hOpp : OppermannConjecture) (n : ℕ) :
    (nthPrime (n + 1) : ℝ) < (Real.sqrt (nthPrime n) + 1) ^ 2 := by
  set P := nthPrime n with hPdef
  set k := Nat.sqrt P with hkdef
  have hP2 : 2 ≤ P := two_le_nthPrime n
  have hk1 : 1 ≤ k := by
    have := Nat.sqrt_le_sqrt (show 1 ≤ P from le_trans (by norm_num) hP2)
    simpa using this
  have hkk : k ^ 2 ≤ P := by
    have := Nat.sqrt_le' P
    simpa [pow_two, hkdef] using this
  have hPk : P < (k + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' P
    simpa [pow_two, hkdef] using this
  have hsqrtP : (k : ℝ) ≤ Real.sqrt P := by
    rw [show (k : ℝ) = Real.sqrt ((k : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hkk)
  have hsq : Real.sqrt (P : ℝ) ^ 2 = (P : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hm2 : 2 ≤ k + 1 := by omega
  rcases lt_or_ge P (k ^ 2 + k) with hcase | hcase
  · -- `P` lies in the lower half of `[k², (k+1)²)`
    obtain ⟨q, hq, hq1, hq2⟩ := (hOpp (k + 1) hm2).1
    have hlow : (k + 1) ^ 2 - (k + 1) = k ^ 2 + k := by ring_nf; omega
    rw [hlow] at hq1
    have hPq : P < q := lt_trans hcase hq1
    have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hPq
    have hub : nthPrime (n + 1) ≤ k ^ 2 + 2 * k := by
      have : q < k ^ 2 + 2 * k + 1 := by
        have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
        omega
      omega
    have h1 : (nthPrime (n + 1) : ℝ) ≤ (k : ℝ) ^ 2 + 2 * k := by
      exact_mod_cast (by exact_mod_cast hub : (nthPrime (n + 1) : ℝ) ≤ ((k ^ 2 + 2 * k : ℕ) : ℝ))
    have h2 : ((k : ℝ)) ^ 2 ≤ (P : ℝ) := by exact_mod_cast hkk
    nlinarith [hsqrtP, hsq, h1, h2]
  · -- `P` lies in the upper half
    obtain ⟨q, hq, hq1, hq2⟩ := (hOpp (k + 1) hm2).2
    have hPq : P < q := lt_trans hPk hq1
    have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hPq
    have hub : nthPrime (n + 1) ≤ k ^ 2 + 3 * k + 1 := by
      have hexp : (k + 1) ^ 2 + (k + 1) = k ^ 2 + 3 * k + 2 := by ring
      omega
    have h1 : (nthPrime (n + 1) : ℝ) ≤ (k : ℝ) ^ 2 + 3 * k + 1 := by
      exact_mod_cast (by exact_mod_cast hub :
        (nthPrime (n + 1) : ℝ) ≤ ((k ^ 2 + 3 * k + 1 : ℕ) : ℝ))
    have hstrict : (k : ℝ) < Real.sqrt P := by
      have hlt : ((k : ℝ)) ^ 2 < (P : ℝ) := by
        have : k ^ 2 < P := by nlinarith [hk1, hcase]
        exact_mod_cast this
      nlinarith [hsqrtP, hsq, Real.sqrt_nonneg (P : ℝ)]
    have h2 : ((k : ℝ)) ^ 2 + k ≤ (P : ℝ) := by exact_mod_cast hcase
    nlinarith [hstrict, hsq, h1, h2]

/-- **Andrica's conjecture, conditional on Oppermann's conjecture.**
If between `m² - m` and `m²`, and between `m²` and `m² + m`, there is always a prime
(for `m ≥ 2`), then for all `n`, `√p_{n+1} - √p_n < 1`. -/
