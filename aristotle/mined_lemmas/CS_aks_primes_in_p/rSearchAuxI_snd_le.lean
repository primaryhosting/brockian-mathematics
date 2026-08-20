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

theorem rSearchAuxI_snd_le (n : ℕ) :
    ∀ (fuel r B : ℕ), r + fuel ≤ B → (rSearchAuxI n fuel r).2 ≤ fuel * (B + 1) + B + 1 := by
  intro fuel
  induction fuel with
  | zero => intro r B _; simp [rSearchAuxI]
  | succ fuel ih =>
      intro r B hB
      rw [rSearchAuxI]
      by_cases h : thr n < ordMod n r
      · simp only [h, if_true]
        have : r ≤ B := by omega
        calc r + 1 ≤ B + 1 := by omega
          _ ≤ (fuel + 1) * (B + 1) + B + 1 := by nlinarith
      · simp only [h, if_false]
        have hrec := ih (r + 1) B (by omega)
        have hrB : r ≤ B := by omega
        calc (rSearchAuxI n fuel (r + 1)).2 + r + 1
            ≤ (fuel * (B + 1) + B + 1) + B + 1 := by omega
          _ ≤ (fuel + 1) * (B + 1) + B + 1 := by nlinarith

/-- Instrumented version of `rAlg`. -/
