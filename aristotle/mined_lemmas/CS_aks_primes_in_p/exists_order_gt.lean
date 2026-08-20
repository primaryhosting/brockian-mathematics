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

theorem exists_order_gt (n s : ℕ) (hn : 2 ≤ n) : ∃ r : ℕ, s < orderOf ((n : ZMod r)) := by
  set N : ℕ := n * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
  have h2 : ∀ i, 1 ≤ i → 2 ≤ n ^ i := by
    intro i hi
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi)
  have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have := h2 i hi.1
    omega
  have hNpos : 0 < N := Nat.mul_pos (by omega) hprodpos
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + 1)
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨q, ?_⟩
  by_contra hle
  push_neg at hle
  set d := orderOf ((n : ZMod q)) with hd
  have hqn : ¬ (q ∣ n) := by
    intro h
    have h1 : q ≤ n := Nat.le_of_dvd (by omega) h
    have h2 : n ≤ N := Nat.le_mul_of_pos_right _ hprodpos
    omega
  have hunit : (n : ZMod q) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hqn
  have hdpos : 0 < d := by
    rw [hd, orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨q - 1, by have := hq.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hunit⟩
  have hpow : ((n : ZMod q)) ^ d = 1 := pow_orderOf_eq_one _
  have hmod : (n ^ d : ℕ) ≡ 1 [MOD q] := by
    have : ((n ^ d : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using hpow
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hdvd : q ∣ n ^ d - 1 := (Nat.modEq_iff_dvd' (by have := h2 d hdpos; omega)).mp hmod.symm
  have hqNdvd : q ∣ N := hdvd.trans (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (by
    simp only [Finset.mem_Icc]; omega)) n)
  have := Nat.le_of_dvd hNpos hqNdvd
  omega

