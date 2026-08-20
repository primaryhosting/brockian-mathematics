import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma sum_inv_primesBelow_pow_two_step (q : ℕ) (hq : 1 ≤ q) :
    ∑ p ∈ Nat.primesBelow (2 ^ (q + 1) + 1), (1 / (p : ℝ))
      ≤ (∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ))) + 4 / q := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Nat.primesBelow (2 ^ (q + 1) + 1))
    (fun p => p ≤ 2 ^ q) (fun p => (1 / (p : ℝ)))
  have hlow : (Nat.primesBelow (2 ^ (q + 1) + 1)).filter (fun p => p ≤ 2 ^ q)
      = Nat.primesBelow (2 ^ q + 1) := by
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hp⟩, hle⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩
      have : 2 ^ q ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hhigh : (Nat.primesBelow (2 ^ (q + 1) + 1)).filter (fun p => ¬ p ≤ 2 ^ q)
      = (range (2 ^ (q + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ q < p) := by
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, not_le]
    tauto
  rw [hlow, hhigh] at hsplit
  have hblock := sum_inv_primes_block_le hq
  linarith

/-- `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`. -/
