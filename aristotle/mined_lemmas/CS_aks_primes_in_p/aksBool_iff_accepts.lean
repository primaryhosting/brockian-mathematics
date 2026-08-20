/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.AKS.Algorithm
import RequestProject.AKS.Cost

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000

namespace CS

/-- **PRIMES is in P** (Agrawal–Kayal–Saxena).

`AKS.aksBool : ℕ → Bool` is an explicit, fully computable implementation of the AKS primality
test.  On input `n` it checks that `n ≥ 2`, that `n` is not a perfect power, that no `a ≤ r`
shares a nontrivial factor with `n`, and — unless `n ≤ r` — that the congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X]/(X^r - 1)` for all `1 ≤ a ≤ ℓ`, where `r = AKS.rAlg n`
is the least modulus for which the multiplicative order of `n` exceeds `(bit length)^4` and
`ℓ = AKS.ellAlg n`.  The congruences are evaluated by repeated squaring in a computable
coefficient-vector model of the quotient ring.

`AKS.aksI : ℕ → Bool × ℕ` is the same algorithm instrumented with a counter: it is a structural
copy of every function involved, threading a count of the primitive operations performed
(see `RequestProject/AKS/Cost.lean` for the cost assigned to each leaf primitive: `r * r`
coefficient multiplications for one cyclic convolution, `bits n` for one `Nat.gcd`, and so on).
Costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits, not in
bit operations.

The statement below records:

* **the instrumented algorithm computes the same answer** as the plain one;
* **correctness**: `AKS.aksBool` decides primality exactly;
* **polynomial running time**: on every input `n ≥ 2` the algorithm performs at most
  `(bit length of n) ^ 45` primitive operations;
* **polynomial size of the parameters**: `r ≤ 2 · (bit length)^12` and `ℓ ≤ 4 · (bit length)^7 + 2`.
-/

theorem aksBool_iff_accepts (n : ℕ) : aksBool n = true ↔ AKSAccepts n := by
  rw [aksBool]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.or_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h2, hpp⟩, hgcd⟩, hlast⟩
    have hr0 : rOf n ≠ 0 := by have := one_le_rOf h2; omega
    rw [rAlg_eq h2] at hgcd hlast
    rw [ellAlg_eq h2] at hlast
    refine ⟨h2, ?_, ?_, ?_⟩
    · intro a b hb hcon
      have hT : isPerfectPower n = true := (isPerfectPower_iff h2).mpr ⟨a, b, hb, hcon⟩
      rw [hpp] at hT
      exact Bool.noConfusion hT
    · intro a ha1 har
      rcases hgcd a (by omega) with (h | h) | h
      · omega
      · exact Or.inl h
      · exact Or.inr h
    · rcases hlast with hle | hall
      · exact Or.inl hle
      · refine Or.inr ?_
        intro a ha1 hae
        rcases hall a (by omega) with h | h
        · omega
        · exact (polyTest_iff (n := n) (r := rOf n) hr0 (by omega) a).mp h
  · rintro ⟨h2, hpp, hgcd, hlast⟩
    have hr0 : rOf n ≠ 0 := by have := one_le_rOf h2; omega
    rw [rAlg_eq h2, ellAlg_eq h2]
    refine ⟨⟨⟨h2, ?_⟩, ?_⟩, ?_⟩
    · rcases Bool.eq_false_or_eq_true (isPerfectPower n) with h | h
      · obtain ⟨a, b, hb, heq⟩ := (isPerfectPower_iff h2).mp h
        exact absurd heq (hpp a b hb)
      · exact h
    · intro a ha
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · exact Or.inl (Or.inl rfl)
      · rcases hgcd a hapos (by omega) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rcases hlast with hle | hall
      · exact Or.inl hle
      · refine Or.inr ?_
        intro a ha
        rcases Nat.eq_zero_or_pos a with rfl | hapos
        · exact Or.inl rfl
        · exact Or.inr ((polyTest_iff (n := n) (r := rOf n) hr0 (by omega) a).mpr
            (hall a hapos (by omega)))

/-- **Correctness of the AKS algorithm**: the computable test `aksBool` decides primality. -/
