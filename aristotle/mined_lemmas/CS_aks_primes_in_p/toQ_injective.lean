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

theorem toQ_injective [Fact (1 < n)] : Function.Injective (toQ (n := n) (r := r)) := by
  intro f g hfg
  have hdvd : (X ^ r - 1 : (ZMod n)[X]) ∣ toPoly f - toPoly g :=
    (mkQ_eq_iff _ _).mp hfg
  have hdeg : (toPoly f - toPoly g).degree < (r : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (degree_toPoly_lt f) (degree_toPoly_lt g))
  have hzero : toPoly f - toPoly g = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  funext i
  have := congrArg (fun P => Polynomial.coeff P (ZMod.val i)) hzero
  simp only [Polynomial.coeff_sub, Polynomial.coeff_zero, coeff_toPoly] at this
  linear_combination this

end Lemmas

end AKS

/-
Elementary numerical estimates used in the AKS proof.
-/
import Mathlib

namespace AKS

