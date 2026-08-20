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

theorem toQ_cmul (f g : Vec n r) : toQ (cmul f g) = toQ f * toQ g := by
  classical
  have hprod : toPoly f * toPoly g
      = ∑ i : ZMod r, ∑ j : ZMod r, C (f i * g j) * X ^ (ZMod.val i + ZMod.val j) := by
    rw [toPoly, toPoly, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [C_mul, pow_add]
    ring
  have hlhs : toQ (cmul f g)
      = ∑ kk : ZMod r, ∑ i : ZMod r, mkQ n r (C (f i * g (kk - i)) * X ^ (ZMod.val kk)) := by
    simp only [toQ, toPoly, cmul]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun kk _ => ?_)
    rw [← map_sum, ← Finset.sum_mul, ← map_sum]
  have hrhs : toQ f * toQ g
      = ∑ i : ZMod r, ∑ j : ZMod r, mkQ n r (C (f i * g j) * X ^ (ZMod.val (i + j))) := by
    rw [toQ, toQ, ← map_mul, hprod, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_mul]
    congr 1
    refine mkQ_X_pow_congr ?_
    rw [ZMod.val_add, Nat.mod_mod]
  rw [hlhs, hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Fintype.sum_equiv (Equiv.subRight i) _ _ (fun kk => ?_)
  simp only [Equiv.subRight_apply]
  have hkk : i + (kk - i) = kk := by ring
  rw [hkk]

