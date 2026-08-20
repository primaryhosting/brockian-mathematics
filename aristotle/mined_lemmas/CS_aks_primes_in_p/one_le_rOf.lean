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

theorem one_le_rOf {n : ℕ} (hn : 2 ≤ n) : 1 ≤ rOf n := by
  rcases Nat.eq_zero_or_pos (rOf n) with h0 | h
  · exfalso
    have hmem := thr_lt_orderOf n hn
    rw [h0] at hmem
    have hz : orderOf ((n : ZMod 0)) = 0 := by
      rw [orderOf_eq_zero_iff]
      intro hfin
      obtain ⟨k, hk, hk1⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
      have hcast : ((n ^ k : ℕ) : ℤ) = 1 := by push_cast; exact_mod_cast hk1
      have hnk : n ^ k = 1 := by exact_mod_cast hcast
      have h2 : (2:ℕ) ^ k ≤ n ^ k := Nat.pow_le_pow_left hn k
      have h3 : (2:ℕ) ≤ 2 ^ k := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      omega
    omega
  · exact h

/-- Linear search for the least modulus with large multiplicative order. -/
