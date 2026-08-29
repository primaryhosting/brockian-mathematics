import Mathlib
/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- For a prime `p`, `σ(p^k) ≤ p^k * p/(p-1)`, since `σ(p^k) = (p^{k+1}-1)/(p-1)`. -/
lemma sigma_primePow_le (p k : ℕ) (hp : p.Prime) :
    ((sigma 1 (p ^ k) : ℕ) : ℚ) ≤ (p : ℚ) ^ k * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hpm : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  push_cast
  have hgeom : ∑ x ∈ Finset.range (k + 1), (p : ℚ) ^ x
      = ((p : ℚ) ^ (k + 1) - 1) / ((p : ℚ) - 1) := by
    rw [geom_sum_eq]; linarith
  have hr : (p : ℚ) ^ k * ((p : ℚ) / ((p : ℚ) - 1)) = ((p : ℚ) ^ (k + 1)) / ((p : ℚ) - 1) := by
    field_simp; ring
  rw [hgeom, hr]
  gcongr
  linarith

/-- The abundancy of `N` is bounded by the Euler product `∏_{p ∣ N} p/(p-1)`. -/
lemma sigma_le_mul_prod {N : ℕ} (hN : N ≠ 0) :
    ((sigma 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have h1 : ((sigma 1 N : ℕ) : ℚ)
      = ∏ p ∈ N.primeFactors, ((sigma 1 (p ^ N.factorization p) : ℕ) : ℚ) := by
    conv_lhs => rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have h2 : (N : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) ^ N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_primePow_le p _ (Nat.prime_of_mem_primeFactors hp)

/-- Elementary bounds on the local Euler factor `p/(p-1)` of a prime `p`. -/
lemma g_bounds {p : ℕ} (hp : p.Prime) :
    1 ≤ (p : ℚ) / ((p : ℚ) - 1) ∧ (p : ℚ) / ((p : ℚ) - 1) ≤ 2 ∧
      (p ≠ 2 → (p : ℚ) / ((p : ℚ) - 1) ≤ 3 / 2) ∧
      (p ≠ 2 → p ≠ 3 → (p : ℚ) / ((p : ℚ) - 1) ≤ 5 / 4) := by
  have h2 := hp.two_le
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h2
  have hpm : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  refine ⟨by rw [le_div_iff₀ hpm]; linarith, by rw [div_le_iff₀ hpm]; linarith, ?_, ?_⟩
  · intro h
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 3 ≤ p)
    rw [div_le_iff₀ hpm]; linarith
  · intro h h3
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have h5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 5 ≤ p)
    rw [div_le_iff₀ hpm]; linarith

private lemma prod3_le {x y z X Y Z : ℚ} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hx : x ≤ X) (hy : y ≤ Y) (hz : z ≤ Z) : x * y * z ≤ X * Y * Z := by
  have h1 : x * y ≤ X * Y := mul_le_mul hx hy (by linarith) (by linarith)
  exact mul_le_mul h1 hz (by linarith) (by nlinarith)

/-- For three distinct primes, `∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4`. -/
lemma three_primes_prod_le {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a : ℚ) / ((a : ℚ) - 1) * ((b : ℚ) / ((b : ℚ) - 1)) * ((c : ℚ) / ((c : ℚ) - 1)) ≤ 15 / 4 := by
  obtain ⟨ha1, ha2, ha3, ha5⟩ := g_bounds ha
  obtain ⟨hb1, hb2, hb3, hb5⟩ := g_bounds hb
  obtain ⟨hc1, hc2, hc3, hc5⟩ := g_bounds hc
  rcases eq_or_ne a 2 with rfl | ha'
  · rcases eq_or_ne b 3 with rfl | hb'
    · have := prod3_le ha1 hb1 hc1 ha2 (hb3 (by norm_num)) (hc5 (Ne.symm hac) (Ne.symm hbc))
      linarith
    · rcases eq_or_ne c 3 with rfl | hc'
      · have := prod3_le ha1 hb1 hc1 ha2 (hb5 (Ne.symm hab) hb') (hc3 (by norm_num))
        linarith
      · have := prod3_le ha1 hb1 hc1 ha2 (hb5 (Ne.symm hab) hb') (hc5 (Ne.symm hac) hc')
        linarith
  · rcases eq_or_ne b 2 with rfl | hb'
    · rcases eq_or_ne a 3 with rfl | ha''
      · have := prod3_le ha1 hb1 hc1 (ha3 ha') hb2 (hc5 (Ne.symm hbc) (Ne.symm hac))
        linarith
      · have := prod3_le ha1 hb1 hc1 (ha5 ha' ha'') hb2 (hc3 (Ne.symm hbc))
        linarith
    · rcases eq_or_ne c 2 with rfl | hc'
      · rcases eq_or_ne a 3 with rfl | ha''
        · have := prod3_le ha1 hb1 hc1 (ha3 ha') (hb5 hb' (Ne.symm hab)) hc2
          linarith
        · have := prod3_le ha1 hb1 hc1 (ha5 ha' ha'') (hb3 hb') hc2
          linarith
      · have := prod3_le ha1 hb1 hc1 (ha3 ha') (hb3 hb') (hc3 hc')
        linarith

/-- A set of at most three primes has Euler product at most `15/4`. -/
lemma prod_primes_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, ((p : ℚ) / ((p : ℚ) - 1)) ≤ 15 / 4 := by
  have h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases h with h | h | h | h
  · rw [Finset.card_eq_zero] at h; subst h; norm_num
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have := (g_bounds (hS a (by simp))).2.1
    simp only [Finset.prod_singleton]
    linarith
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha := g_bounds (hS a (by simp))
    have hb := g_bounds (hS b (by simp))
    rw [Finset.prod_insert (by simpa using hab), Finset.prod_singleton]
    rcases eq_or_ne a 2 with rfl | ha'
    · nlinarith [ha.2.1, hb.2.2.1 (Ne.symm hab), ha.1, hb.1]
    · nlinarith [ha.2.2.1 ha', hb.2.1, ha.1, hb.1]
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simpa using hbc),
      Finset.prod_singleton, ← mul_assoc]
    exact three_primes_prod_le (hS a (by simp)) (hS b (by simp)) (hS c (by simp)) hab hac hbc

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed (quasi-amicable)
numbers, then `m * n` has at least four distinct prime factors.

The proof: by multiplicativity of `σ` on coprime arguments,
`σ(mn) = σ(m)σ(n) = (m+n+1)^2 > (m+n)^2 ≥ 4mn`, so the abundancy `σ(mn)/(mn)` exceeds `4`.
On the other hand, if `mn` had at most three distinct prime factors then
`σ(mn)/(mn) ≤ ∏_{p ∣ mn} p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`, a contradiction. -/
theorem coprime_pair_four_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hmn : Nat.Coprime m n) :
    4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  by_contra hcon
  push_neg at hcon
  have hN : m * n ≠ 0 := by positivity
  have hsig : sigma 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hmn, hsm, hsn]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hgt : 4 * ((m : ℚ) * n) < ((sigma 1 (m * n) : ℕ) : ℚ) := by
    rw [hsig]
    push_cast
    nlinarith [sq_nonneg ((m : ℚ) - n)]
  have hle := sigma_le_mul_prod hN
  have hP := prod_primes_le (S := (m * n).primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (by omega)
  have hNq : (0 : ℚ) < ((m * n : ℕ) : ℚ) := by push_cast; positivity
  have hfin : ((m * n : ℕ) : ℚ) * ∏ p ∈ (m * n).primeFactors, ((p : ℚ) / ((p : ℚ) - 1))
      ≤ ((m * n : ℕ) : ℚ) * (15 / 4) :=
    mul_le_mul_of_nonneg_left hP (le_of_lt hNq)
  push_cast at hfin hle hgt
  linarith

end BetrothedNumbers
end Brockian

