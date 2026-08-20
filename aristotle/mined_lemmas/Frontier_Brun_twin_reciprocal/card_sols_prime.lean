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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma card_sols_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (sols p).card = 2 := by
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases eq_or_lt_of_le h2 with h | h
    · exact absurd h.symm hp2
    · omega
  have hset : sols p = {0, p - 2} := by
    ext r
    rw [mem_sols, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hdvd⟩
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact Or.inl (Nat.eq_zero_of_dvd_of_lt h1 hr)
      · right
        obtain ⟨c, hc⟩ := h1
        have hc1 : c = 1 := by nlinarith
        subst hc1
        omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, by simp⟩
      · refine ⟨by omega, ?_⟩
        have hpp : p - 2 + 2 = p := by omega
        rw [hpp]
        exact dvd_mul_left p (p - 2)
  rw [hset, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

