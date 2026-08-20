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

theorem Intro.aeval {F : Type*} [CommRing F] [Algebra (ZMod p) F] {ζ : F} (hζ : ζ ^ r = 1)
    {m : ℕ} {f : (ZMod p)[X]} (h : Intro p r m f) :
    (Polynomial.aeval ζ f) ^ m = Polynomial.aeval (ζ ^ m) f := by
  obtain ⟨c, hc⟩ := h
  have h0 : Polynomial.aeval ζ ((X : (ZMod p)[X]) ^ r - 1) = 0 := by
    simp [hζ]
  have hexp : Polynomial.aeval ζ (expand (ZMod p) m f) = Polynomial.aeval (ζ ^ m) f := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_expand,
      Polynomial.expand_eval]
  have := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_mul, map_pow, h0, zero_mul, hexp] at this
  linear_combination this

end AKS

/-
An instrumented (step-counting) version of the AKS algorithm.

Every function below returns, besides its value, a count of the primitive operations performed.
The counting is *derived*: each instrumented function is a structural copy of the corresponding
function of `RequestProject.AKS.Algorithm`, carrying an extra counter, and we prove that its value
component is literally the value computed by the original function.  Only the *leaf* primitives
are assigned a cost by fiat (a primitive cannot have its cost derived):

* a cyclic convolution `cmul` of two coefficient vectors of length `r` costs `r * r`
  (one coefficient multiplication in `ZMod n` per pair of coefficients);
* an addition `cadd` of two such vectors, and a test of equality between two such vectors,
  cost `r` each;
* one step of the search for `r` (computing `ordMod n r`) costs `r`;
* one `Nat.gcd a n` costs `bits n`;
* the perfect-power test costs `(bits n) ^ 4`;
* every iteration of a loop costs one extra unit of bookkeeping.

All costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits.
-/
import Mathlib
import RequestProject.AKS.Algorithm

open Polynomial

namespace AKS

/-! ### Bit lengths -/

