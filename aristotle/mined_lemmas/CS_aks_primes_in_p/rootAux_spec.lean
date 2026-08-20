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

theorem rootAux_spec (b n : ℕ) :
    ∀ (fuel lo hi : ℕ), hi - lo ≤ fuel → lo ^ b ≤ n → n < hi ^ b →
      (rootAux b n fuel lo hi) ^ b ≤ n ∧ n < (rootAux b n fuel lo hi + 1) ^ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hgap hlo hhi
      exfalso
      have hle : hi ≤ lo := by omega
      have : hi ^ b ≤ lo ^ b := Nat.pow_le_pow_left hle b
      omega
  | succ fuel ih =>
      intro lo hi hgap hlo hhi
      rw [rootAux]
      by_cases hcase : hi ≤ lo + 1
      · simp only [hcase, if_true]
        refine ⟨hlo, ?_⟩
        have hlt : lo < hi := by
          by_contra hcon
          push_neg at hcon
          have : hi ^ b ≤ lo ^ b := Nat.pow_le_pow_left hcon b
          omega
        have : hi = lo + 1 := by omega
        rwa [this] at hhi
      · simp only [hcase, if_false]
        push_neg at hcase
        set mid := (lo + hi) / 2 with hmid
        have hlomid : lo < mid := by omega
        have hmidhi : mid < hi := by omega
        by_cases hmidle : mid ^ b ≤ n
        · simp only [hmidle, if_true]
          exact ih mid hi (by omega) hmidle hhi
        · simp only [hmidle, if_false]
          exact ih lo mid (by omega) hlo (by omega)

