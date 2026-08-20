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

lemma solCount_mult : solCount.IsMultiplicative := by
  constructor
  · rw [solCount_apply]
    have : sols 1 = {0} := by
      ext r
      rw [mem_sols, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, -⟩; omega
      · rintro rfl; exact ⟨by omega, one_dvd _⟩
    rw [this, Finset.card_singleton]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [solCount_apply, sols]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [solCount_apply, sols]
    simp only [solCount_apply]
    exact card_sols_mul hm hn hmn

/-- For odd squarefree `d`, the congruence `r(r+2) ≡ 0 (mod d)` has `2 ^ ω(d)` solutions. -/
