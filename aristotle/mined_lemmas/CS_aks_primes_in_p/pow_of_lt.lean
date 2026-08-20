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

theorem pow_of_lt {p n i j i' j' : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hjj : j' < j)
    (heq : p ^ i * n ^ j = p ^ i' * n ^ j') : ∃ e, n = p ^ e := by
  have h1 : n ^ j = n ^ j' * n ^ (j - j') := by
    rw [← pow_add, Nat.add_sub_cancel' hjj.le]
  rw [h1] at heq
  have hpos : 0 < n ^ j' := Nat.pow_pos (by omega)
  have h2 : p ^ i * n ^ (j - j') = p ^ i' := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc n ^ j' * (p ^ i * n ^ (j - j')) = p ^ i * (n ^ j' * n ^ (j - j')) := by ring
      _ = p ^ i' * n ^ j' := heq
      _ = n ^ j' * p ^ i' := by ring
  have hne0 : j - j' ≠ 0 := by omega
  have h3 : n ∣ p ^ i' := by
    rw [← h2]
    exact Dvd.dvd.mul_left (dvd_pow_self n hne0) _
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp h3
  exact ⟨e, he⟩

/-- If two distinct pairs of exponents give the same number, `n` is a power of `p`. -/
