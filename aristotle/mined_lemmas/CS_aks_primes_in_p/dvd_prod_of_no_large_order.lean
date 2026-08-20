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

theorem dvd_prod_of_no_large_order {n s c B : ℕ} (hn : 2 ≤ n)
    (H : ∀ r : ℕ, r ≤ B → orderOf ((n : ZMod r)) ≤ s)
    (hc : ∀ e : ℕ, 2 ^ e ≤ B → e ≤ c)
    {r : ℕ} (hr1 : 1 ≤ r) (hrB : r ≤ B) :
    r ∣ n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
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
  set N := n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.pow_pos (by omega)) hprodpos
  rw [← Nat.factorization_le_iff_dvd (by omega) hNpos.ne']
  intro P
  by_cases hP : P.Prime
  · set e := r.factorization P with he
    by_cases he0 : e = 0
    · simp [he0]
    · haveI : Fact P.Prime := ⟨hP⟩
      have hPe_dvd_r : P ^ e ∣ r := Nat.ordProj_dvd r P
      have hPeB : P ^ e ≤ B := le_trans (Nat.le_of_dvd (by omega) hPe_dvd_r) hrB
      have hPe2 : (2:ℕ) ^ e ≤ P ^ e := Nat.pow_le_pow_left hP.two_le e
      have hec : e ≤ c := hc e (le_trans hPe2 hPeB)
      have hdvdN : P ^ e ∣ N := by
        by_cases hPn : P ∣ n
        · have h1 : P ^ e ∣ n ^ e := pow_dvd_pow_of_dvd hPn e
          have h2' : n ^ e ∣ n ^ c := pow_dvd_pow n hec
          exact Dvd.dvd.mul_right (h1.trans h2') _
        · have hPe_pos : 0 < P ^ e := Nat.pow_pos hP.pos
          have hPege : 2 ≤ P ^ e := by
            calc 2 ≤ 2 ^ e := by
                  have : 1 ≤ e := by omega
                  calc (2:ℕ) = 2 ^ 1 := by norm_num
                    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) this
              _ ≤ P ^ e := hPe2
          haveI : NeZero (P ^ e) := ⟨by omega⟩
          have hcop : Nat.Coprime n (P ^ e) :=
            (((hP.coprime_iff_not_dvd).mpr hPn).symm).pow_right e
          have hunit : IsUnit ((n : ZMod (P ^ e))) := (ZMod.isUnit_iff_coprime n _).mpr hcop
          set d := orderOf ((n : ZMod (P ^ e))) with hd
          have hdpos : 0 < d := by
            rw [hd, orderOf_pos_iff]
            obtain ⟨u, hu⟩ := hunit
            refine isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf u, ?_, ?_⟩
            · exact orderOf_pos u
            · rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
          have hds : d ≤ s := H (P ^ e) hPeB
          have hpow : ((n : ZMod (P ^ e))) ^ d = 1 := pow_orderOf_eq_one _
          have hmod : (n ^ d : ℕ) ≡ 1 [MOD P ^ e] := by
            have : ((n ^ d : ℕ) : ZMod (P ^ e)) = ((1 : ℕ) : ZMod (P ^ e)) := by
              push_cast; simpa using hpow
            exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
          have hdvd1 : P ^ e ∣ n ^ d - 1 :=
            (Nat.modEq_iff_dvd' (by have := h2 d hdpos; omega)).mp hmod.symm
          refine hdvd1.trans (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ ?_) _)
          simp only [Finset.mem_Icc]
          omega
      exact (hP.pow_dvd_iff_le_factorization hNpos.ne').mp hdvdN
  · simp [Nat.factorization_eq_zero_of_not_prime _ hP]

/-- Key estimate: `k ^ 12 ≤ 2 ^ (12 * k)`. -/
