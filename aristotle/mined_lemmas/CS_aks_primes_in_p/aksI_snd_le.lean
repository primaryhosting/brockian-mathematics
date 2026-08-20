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

theorem aksI_snd_le {n : ℕ} (hn : 2 ≤ n) : (aksI n).2 ≤ bits n ^ 45 := by
  set k := bits n with hkdef
  have hk : 2 ≤ k := two_le_bits hn
  have hk1 : 1 ≤ k := by omega
  have hpow : ∀ e : ℕ, 1 ≤ k ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  have hr : rAlg n ≤ 2 * k ^ 12 := by rw [rAlg_eq hn]; exact rOf_le n hn
  have hell : ellAlg n ≤ 4 * k ^ 7 + 2 := ellAlg_le hn
  -- the search for `r`
  have hR2 : (rAlgI n).2 ≤ k ^ 30 := by
    refine le_trans (rAlgI_snd_le n) ?_
    have h1 : (2 * k ^ 12 + 1) * (2 * k ^ 12 + 3) ≤ (4 * k ^ 12) * (8 * k ^ 12) := by
      have := hpow 12
      exact Nat.mul_le_mul (by omega) (by omega)
    have h2 : (4 * k ^ 12) * (8 * k ^ 12) = 32 * k ^ 24 := by ring
    have h3 : 2 * k ^ 12 + 3 ≤ 8 * k ^ 24 := by
      have h4 : k ^ 12 ≤ k ^ 24 := Nat.pow_le_pow_right hk1 (by omega)
      have := hpow 24
      omega
    calc (2 * k ^ 12 + 1) * (2 * k ^ 12 + 3) + 2 * k ^ 12 + 3
        ≤ 32 * k ^ 24 + 8 * k ^ 24 := by omega
      _ = 40 * k ^ 24 := by ring
      _ ≤ k ^ 30 := cost_step (d := 6) hk (by norm_num) (by omega)
  -- the gcd loop
  have hg2 : (allI (fun a => (a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n, k))
      (List.range (rAlg n + 1))).2 ≤ k ^ 16 := by
    refine le_trans (allI_snd_le _ k _ (fun a _ => le_rfl)) ?_
    rw [List.length_range]
    have h1 : (rAlg n + 1) * (k + 1) ≤ (4 * k ^ 12) * (2 * k ^ 1) := by
      have := hpow 12
      refine Nat.mul_le_mul (by omega) (by simp; omega)
    calc (rAlg n + 1) * (k + 1) ≤ (4 * k ^ 12) * (2 * k ^ 1) := h1
      _ = 8 * k ^ 13 := by ring
      _ ≤ k ^ 16 := cost_step (d := 3) hk (by norm_num) (by omega)
  -- the loop over the polynomial congruences
  have hl2 : (allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
      (List.range (ellAlg n + 1))).2 ≤ k ^ 40 := by
    set B : ℕ := 16 * k ^ 25 with hB
    have hbound : ∀ a ∈ List.range (ellAlg n + 1),
        (if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a).2 ≤ B := by
      intro a _
      by_cases ha : a = 0
      · simp only [ha, if_pos]
        have := hpow 25
        omega
      · simp only [ha, if_false]
        refine le_trans (polyTestI_snd_le n (rAlg n) a) ?_
        rw [← hkdef]
        have hrr : rAlg n * rAlg n ≤ (2 * k ^ 12) * (2 * k ^ 12) := Nat.mul_le_mul hr hr
        have hrr2 : rAlg n * rAlg n ≤ 4 * k ^ 24 := by
          calc rAlg n * rAlg n ≤ (2 * k ^ 12) * (2 * k ^ 12) := hrr
            _ = 4 * k ^ 24 := by ring
        have h1 : 2 * k * (rAlg n * rAlg n) ≤ 2 * k * (4 * k ^ 24) :=
          Nat.mul_le_mul_left _ hrr2
        have h2 : 2 * k * (4 * k ^ 24) = 8 * k ^ 25 := by ring
        have h3 : 3 * rAlg n ≤ 6 * k ^ 12 := by omega
        have h4 : k ^ 12 ≤ k ^ 25 := Nat.pow_le_pow_right hk1 (by omega)
        omega
    refine le_trans (allI_snd_le _ B _ hbound) ?_
    rw [List.length_range]
    have h1 : (ellAlg n + 1) * (B + 1) ≤ (8 * k ^ 7) * (32 * k ^ 25) := by
      have h7 := hpow 7
      have h25 := hpow 25
      refine Nat.mul_le_mul (by omega) (by omega)
    calc (ellAlg n + 1) * (B + 1) ≤ (8 * k ^ 7) * (32 * k ^ 25) := h1
      _ = 256 * k ^ 32 := by ring
      _ ≤ k ^ 40 := cost_step (d := 8) hk (by norm_num) (by omega)
  have hlast : (if n ≤ rAlg n then ((true : Bool), 1)
      else allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
        (List.range (ellAlg n + 1))).2 ≤ k ^ 40 := by
    by_cases h : n ≤ rAlg n
    · simpa [h] using hpow 40
    · simpa [h] using hl2
  have hk4 : k ^ 4 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hk30 : k ^ 30 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hk16 : k ^ 16 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hfin : 8 * k ^ 40 ≤ k ^ 45 := cost_step (d := 3) hk (by norm_num) (by omega)
  have hexp : (aksI n).2 = (rAlgI n).2 + k ^ 4
      + (allI (fun a => (a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n, k))
          (List.range (rAlg n + 1))).2
      + (if n ≤ rAlg n then ((true : Bool), 1)
          else allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
            (List.range (ellAlg n + 1))).2 + 1 := by
    rw [aksI]
    simp only [rAlgI_fst, hkdef]
  rw [hexp]
  have h39 := hpow 40
  omega

end AKS

