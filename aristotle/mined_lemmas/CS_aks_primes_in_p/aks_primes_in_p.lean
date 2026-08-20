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

theorem aks_primes_in_p :
    (∀ n : ℕ, (AKS.aksI n).1 = AKS.aksBool n) ∧
    (∀ n : ℕ, AKS.aksBool n = true ↔ Nat.Prime n) ∧
    (∀ n : ℕ, 2 ≤ n → (AKS.aksI n).2 ≤ AKS.bits n ^ 45) ∧
    (∀ n : ℕ, 2 ≤ n → AKS.rAlg n ≤ 2 * AKS.bits n ^ 12) ∧
    (∀ n : ℕ, 2 ≤ n → AKS.ellAlg n ≤ 4 * AKS.bits n ^ 7 + 2) := by
  refine ⟨AKS.aksI_fst, AKS.aksBool_iff_prime, fun n hn => AKS.aksI_snd_le hn, ?_,
    fun n hn => AKS.ellAlg_le hn⟩
  intro n hn
  rw [AKS.rAlg_eq hn]
  exact AKS.rOf_le n hn

end CS

/-
A computable model of the ring `(ZMod n)[X] / (X^r - 1)`: coefficient vectors indexed by
`ZMod r`, with cyclic convolution as multiplication.
-/
import Mathlib

open Polynomial

namespace AKS

/-- Coefficient vectors: `f : ZMod r → ZMod n` represents `∑ i, f i * X ^ i.val`. -/
abbrev Vec (n r : ℕ) := ZMod r → ZMod n

variable {n r : ℕ}

/-- The polynomial represented by a coefficient vector. -/
