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

theorem cpowI_snd_le [NeZero r] (f : Vec n r) (m : ℕ) :
    (cpowI f m).2 ≤ 2 * bits m * (r * r) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [cpowI]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have hh := ih (m / 2) (by omega)
      have hb := bits_div_two_succ_le hm
      have hmono : 2 * bits (m / 2) * (r * r) + 2 * (r * r) ≤ 2 * bits m * (r * r) := by
        have : (2 * bits (m / 2) + 2) * (r * r) ≤ (2 * bits m) * (r * r) :=
          Nat.mul_le_mul_right _ (by omega)
        calc 2 * bits (m / 2) * (r * r) + 2 * (r * r)
            = (2 * bits (m / 2) + 2) * (r * r) := by ring
          _ ≤ (2 * bits m) * (r * r) := this
      by_cases hpar : m % 2 = 1 <;> simp only [hpar, if_true, if_false] <;> omega

/-! ### Instrumented polynomial congruence test -/

/-- Instrumented version of `polyTestC`. -/
