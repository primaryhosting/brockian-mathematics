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

theorem exists_r_le (n : ℕ) (hn : 2 ≤ n) :
    ∃ r : ℕ, r ≤ 2 * (bits n) ^ 12 ∧ thr n < orderOf ((n : ZMod r)) := by
  classical
  set k := bits n with hk
  have hk2 : 2 ≤ k := by
    rw [hk, bits]
    by_contra hcon
    push_neg at hcon
    have h1 : Nat.size n ≤ 1 := by omega
    rw [Nat.size_le] at h1
    omega
  have hnk : n < 2 ^ k := Nat.lt_size_self n
  set s := thr n with hs
  have hsk : s = k ^ 4 := rfl
  set q := k ^ 12 with hq
  set B := 2 * q with hB
  by_contra hcon
  push_neg at hcon
  have H : ∀ r : ℕ, r ≤ B → orderOf ((n : ZMod r)) ≤ s := fun r hr => hcon r hr
  -- every `r ≤ B` divides `N`
  set c := 13 * k with hc
  have hcbound : ∀ e : ℕ, 2 ^ e ≤ B → e ≤ c := by
    intro e he
    have h1 : B ≤ 2 ^ c := by
      calc B = 2 * k ^ 12 := rfl
        _ ≤ 2 * 2 ^ (12 * k) := by
            exact Nat.mul_le_mul_left 2 (pow_twelve_le k)
        _ = 2 ^ (12 * k + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := le_trans he h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  set N := n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
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
  have hNpos : 0 < N := Nat.mul_pos (Nat.pow_pos (by omega)) hprodpos
  have hlcm_dvd : lcmUpTo B ∣ N := by
    rw [lcmUpTo]
    refine Finset.lcm_dvd ?_
    intro r hr
    simp only [Finset.mem_Icc] at hr
    exact dvd_prod_of_no_large_order hn H hcbound hr.1 hr.2
  have hlcm_le : lcmUpTo B ≤ N := Nat.le_of_dvd hNpos hlcm_dvd
  -- lower bound
  have hq4 : 4 ≤ q := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 12 := by norm_num
      _ ≤ k ^ 12 := Nat.pow_le_pow_left hk2 12
  have hlow : 4 ^ q < q * N := lt_of_lt_of_le (four_pow_lt_mul_lcmUpTo hq4)
    (Nat.mul_le_mul_left q hlcm_le)
  -- upper bound on `N`
  have hsum : ∑ i ∈ Finset.Icc 1 s, i ≤ s * s := by
    calc ∑ i ∈ Finset.Icc 1 s, i ≤ ∑ _i ∈ Finset.Icc 1 s, s := by
          refine Finset.sum_le_sum ?_
          intro i hi
          simp only [Finset.mem_Icc] at hi
          exact hi.2
      _ = (Finset.Icc 1 s).card * s := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ s * s := by rw [Nat.card_Icc]; exact Nat.mul_le_mul_right s (by omega)
  have hprodle : (∏ i ∈ Finset.Icc 1 s, (n ^ i - 1)) ≤ n ^ (s * s) := by
    calc (∏ i ∈ Finset.Icc 1 s, (n ^ i - 1)) ≤ ∏ i ∈ Finset.Icc 1 s, n ^ i := by
          refine Finset.prod_le_prod' ?_
          intro i
          omega
      _ = n ^ (∑ i ∈ Finset.Icc 1 s, i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ n ^ (s * s) := Nat.pow_le_pow_right (by omega) hsum
  have hNle : N ≤ n ^ (c + s * s) := by
    rw [hN, pow_add]
    exact Nat.mul_le_mul_left _ hprodle
  have hNle2 : N < 2 ^ (k * (c + s * s)) := by
    calc N ≤ n ^ (c + s * s) := hNle
      _ < (2 ^ k) ^ (c + s * s) := by
          refine Nat.pow_lt_pow_left hnk ?_
          have : 0 < c := by omega
          omega
      _ = 2 ^ (k * (c + s * s)) := by rw [← pow_mul]
  -- combine
  have hqle : q ≤ 2 ^ (12 * k) := pow_twelve_le k
  have h4q : (4:ℕ) ^ q = 2 ^ (2 * q) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hfinal : (2:ℕ) ^ (2 * q) < 2 ^ (12 * k + k * (c + s * s)) := by
    calc (2:ℕ) ^ (2 * q) = 4 ^ q := h4q.symm
      _ < q * N := hlow
      _ < 2 ^ (12 * k) * 2 ^ (k * (c + s * s)) :=
          Nat.mul_lt_mul_of_le_of_lt hqle hNle2 (Nat.pow_pos (by norm_num))
      _ = 2 ^ (12 * k + k * (c + s * s)) := by rw [← pow_add]
  have hexp : 2 * q < 12 * k + k * (c + s * s) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hfinal
  -- but this is false
  rw [hq, hc, hsk] at hexp
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have hkeq : k = 2 := by omega
    rw [hkeq] at hexp
    norm_num at hexp
  · have h8 : (12:ℕ) ≤ k ^ 8 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 8)
    have h7 : (13:ℕ) ≤ k ^ 7 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 7)
    have h3 : (27:ℕ) ≤ k ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 3)
    have key : 12 * k + k * (13 * k + k ^ 4 * k ^ 4) ≤ 2 * k ^ 12 := by
      calc 12 * k + k * (13 * k + k ^ 4 * k ^ 4) = 12 * k + 13 * k ^ 2 + k ^ 9 := by ring
        _ ≤ k ^ 8 * k + k ^ 7 * k ^ 2 + k ^ 9 := by gcongr
        _ = 3 * k ^ 9 := by ring
        _ ≤ (2 * k ^ 3) * k ^ 9 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * k ^ 12 := by ring
    omega

/-- The AKS modulus is polynomially bounded: `rOf n ≤ 2 * (bits n) ^ 12`. -/
