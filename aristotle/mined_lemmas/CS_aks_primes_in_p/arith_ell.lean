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

theorem arith_ell {k t rr : ℕ} (hk : 3 ≤ k) (ht : k ^ 4 < t)
    (htr : t ≤ Nat.totient rr) (hlt : Nat.totient rr < rr) :
    2 * Nat.sqrt (Nat.totient rr) * k + 2 < rr := by
  have h1 : k ^ 2 ≤ Nat.sqrt (Nat.totient rr) := sq_le_sqrt (lt_of_lt_of_le ht htr)
  have h2 := mul_bound hk h1
  have h3 : Nat.sqrt (Nat.totient rr) ^ 2 ≤ Nat.totient rr := Nat.sqrt_le' _
  nlinarith

end AKS

/-
The hard direction of the AKS criterion: an accepted number is prime.
-/
import RequestProject.AKS.Counting
import RequestProject.AKS.Arith
import RequestProject.AKS.Sound

open Polynomial

namespace AKS

/-- If `p ^ i * n ^ j = p ^ i' * n ^ j'` with `j' < j` then `n` is a power of `p`. -/
