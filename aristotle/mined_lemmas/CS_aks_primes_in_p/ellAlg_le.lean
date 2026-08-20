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

theorem ellAlg_le {n : ℕ} (hn : 2 ≤ n) : ellAlg n ≤ 4 * bits n ^ 7 + 2 := by
  have hr : rAlg n ≤ 2 * bits n ^ 12 := by
    rw [rAlg_eq hn]; exact rOf_le n hn
  have htot : Nat.totient (rAlg n) ≤ 2 * bits n ^ 12 :=
    le_trans (Nat.totient_le _) hr
  have hsq : Nat.sqrt (Nat.totient (rAlg n)) ≤ 2 * bits n ^ 6 := by
    have hle : Nat.totient (rAlg n) ≤ (2 * bits n ^ 6) * (2 * bits n ^ 6) := by
      refine le_trans htot ?_
      have : 2 * bits n ^ 12 ≤ 4 * bits n ^ 12 := by omega
      calc 2 * bits n ^ 12 ≤ 4 * bits n ^ 12 := this
        _ = (2 * bits n ^ 6) * (2 * bits n ^ 6) := by ring
    calc Nat.sqrt (Nat.totient (rAlg n)) ≤ Nat.sqrt ((2 * bits n ^ 6) * (2 * bits n ^ 6)) :=
          Nat.sqrt_le_sqrt hle
      _ = 2 * bits n ^ 6 := Nat.sqrt_eq _
  calc ellAlg n = 2 * Nat.sqrt (Nat.totient (rAlg n)) * bits n + 2 := rfl
    _ ≤ 2 * (2 * bits n ^ 6) * bits n + 2 := by
        have := Nat.mul_le_mul_right (bits n) (Nat.mul_le_mul_left 2 hsq)
        omega
    _ = 4 * bits n ^ 7 + 2 := by ring

/-! ### The polynomial congruence test -/

/-- The test `(X + a)^n = X^n + a` in the computable model of `(ZMod n)[X]/(X^r-1)`. -/
