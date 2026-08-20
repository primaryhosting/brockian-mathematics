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

theorem four_pow_lt_mul_lcmUpTo {q : ℕ} (hq : 4 ≤ q) : 4 ^ q < q * lcmUpTo (2 * q) := by
  have h1 : 4 ^ q < q * Nat.centralBinom q := Nat.four_pow_lt_mul_centralBinom q hq
  have h2 : Nat.centralBinom q ≤ lcmUpTo (2 * q) :=
    Nat.le_of_dvd (lcmUpTo_pos _) (centralBinom_dvd_lcmUpTo (by omega))
  calc 4 ^ q < q * Nat.centralBinom q := h1
    _ ≤ q * lcmUpTo (2 * q) := Nat.mul_le_mul_left q h2

end AKS

/-
The polynomial bound on the AKS modulus `r`.
-/
import RequestProject.AKS.Defs
import RequestProject.AKS.Lcm

namespace AKS

/-- Every `r ≤ B` divides `n ^ c * ∏_{i ≤ s} (n^i - 1)`, provided no `r ≤ B` has
multiplicative order of `n` exceeding `s` and `c` is large enough. -/
