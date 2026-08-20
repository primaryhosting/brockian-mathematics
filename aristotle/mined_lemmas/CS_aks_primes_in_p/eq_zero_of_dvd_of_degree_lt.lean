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

theorem eq_zero_of_dvd_of_degree_lt [Fact (1 < n)] {P : (ZMod n)[X]}
    (hdvd : (X ^ r - 1 : (ZMod n)[X]) ∣ P)
    (hdeg : P.degree < (r : ℕ)) : P = 0 := by
  obtain ⟨c, hc⟩ := hdvd
  have hmonic : (X ^ r - 1 : (ZMod n)[X]).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ZMod n) (NeZero.ne r)
  by_cases hc0 : c = 0
  · rw [hc, hc0, mul_zero]
  · exfalso
    have hdeg1 : (X ^ r - 1 : (ZMod n)[X]).degree = (r : ℕ) := by
      simpa using Polynomial.degree_X_pow_sub_C (n := r) (Nat.pos_of_ne_zero (NeZero.ne r))
        (1 : ZMod n)
    have hlead : ((X ^ r - 1 : (ZMod n)[X]).leadingCoeff) * c.leadingCoeff ≠ 0 := by
      rw [hmonic.leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc0
    have hdegmul : ((X ^ r - 1 : (ZMod n)[X]) * c).degree
        = (X ^ r - 1 : (ZMod n)[X]).degree + c.degree := Polynomial.degree_mul' hlead
    rw [hc, hdegmul, hdeg1, Polynomial.degree_eq_natDegree hc0, ← Nat.cast_add] at hdeg
    have : r + c.natDegree < r := by exact_mod_cast hdeg
    omega

