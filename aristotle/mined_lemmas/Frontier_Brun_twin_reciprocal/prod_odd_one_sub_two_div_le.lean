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

theorem prod_odd_one_sub_two_div_le (z : ℕ) (hz : 3 ≤ z) :
    ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - 2 / (p : ℝ)) ≤ 4 / (Real.log z) ^ 2 := by
  have hmem : ∀ p ∈ (z + 1).primesBelow.erase 2, p.Prime ∧ p ≠ 2 := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_erase hp),
      Finset.ne_of_mem_erase hp⟩
  have h3 : ∀ p ∈ (z + 1).primesBelow.erase 2, (3:ℝ) ≤ p := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := hmem p hp
    have := hpp.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  -- factorwise bound `1 - 2/p ≤ (1 - 1/p)^2`
  have hstep : ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p : ℝ)⁻¹) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := h3 p hp
      have h2 : 2 / (p:ℝ) ≤ 2/3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
      linarith
    · have hp3 := h3 p hp
      have hppos : (0:ℝ) < p := by linarith
      have hexp : (1 - (p : ℝ)⁻¹) ^ 2 = 1 - 2 / p + ((p : ℝ)⁻¹) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  refine hstep.trans ?_
  have h2mem : 2 ∈ (z + 1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hpos : ∀ p ∈ (z + 1).primesBelow, (0:ℝ) < 1 - (p:ℝ)⁻¹ :=
    fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primesBelow hp)
  have hepos : (0:ℝ) < ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) :=
    Finset.prod_pos fun p hp => hpos p (Finset.mem_of_mem_erase hp)
  have hsplit : ∏ p ∈ (z + 1).primesBelow, (1 - (p:ℝ)⁻¹)
      = (1/2) * ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) := by
    rw [← Finset.prod_erase_mul _ _ h2mem]
    norm_num
    ring
  have hle := prod_one_sub_inv_le z hz
  rw [hsplit] at hle
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have h2 : ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) ≤ 2 / Real.log z := by
    have h22 : (2:ℝ) / Real.log z = 2 * (1 / Real.log z) := by ring
    rw [h22]
    linarith
  rw [Finset.prod_pow]
  calc (∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹)) ^ 2 ≤ (2 / Real.log z) ^ 2 :=
        pow_le_pow_left₀ hepos.le h2 2
    _ = 4 / (Real.log z) ^ 2 := by rw [div_pow]; norm_num

/-- Chebyshev's bound `primorial n ≤ 4 ^ n` gives that the number of primes in the dyadic block
`[2^j, 2^(j+1))` is at most `2^(j+2)/j`. -/
