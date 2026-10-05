/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

lemma sqrt_bound {n d : ℕ} (h : 2 ^ n ≤ d ^ 2 + 2) : 2 ^ (n / 2) ≤ d + 2 := by
  by_contra hc
  push_neg at hc
  have h1 : (2 : ℕ) ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (d + 2) * (d + 2) < 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_lt_mul_of_lt_of_lt hc hc
  nlinarith [h, h1, h2]

/-- **Simon's problem.**

1. *(Quantum, interference)* For an `s`-periodic oracle every measurement outcome `y` of the
   Hadamard–oracle–Hadamard subroutine satisfies `⟪y, s⟫ = 0`: the signed sum giving the
   amplitude of any `y` with `⟪y, s⟫ ≠ 0` cancels exactly.
2. *(Quantum, `O(n)` queries suffice)* For every nonzero `s` there are `n` such outcomes that
   determine `s` uniquely among nonzero vectors.
3. *(Classical, `Ω(2 ^ (n / 2))` queries needed)* Every deterministic classical decision tree
   of depth `d` that solves Simon's problem obeys `2 ^ n ≤ d ^ 2 + 2`, and hence
   `2 ^ (n / 2) ≤ d + 2`.
-/
