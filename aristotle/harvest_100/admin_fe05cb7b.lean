import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-! ### The rational abundancy bound `σ₁(N)/N ≤ ∏_{p ∣ N} p/(p-1)` -/

/-- For a prime power, `σ₁(p ^ a) ≤ p ^ a * p / (p - 1)`. -/
lemma sigma_one_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((σ 1 (p ^ a) : ℕ) : ℚ) ≤ (p : ℚ) ^ a * ((p : ℚ) / (p - 1)) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  have hgeom : (∑ k ∈ Finset.range (a + 1), (p : ℚ) ^ k) * ((p : ℚ) - 1)
      = (p : ℚ) ^ (a + 1) - 1 := by
    have := geom_sum_mul (x := (p : ℚ)) (n := a + 1)
    linarith [this]
  rw [mul_div_assoc']
  rw [le_div_iff₀ (by linarith), hgeom]
  have hpow : (p : ℚ) ^ a * p = (p : ℚ) ^ (a + 1) := by ring
  linarith [hpow]

/-- The abundancy `σ₁(N)/N` is bounded by `∏_{p ∣ N} p/(p-1)` (in multiplied-out form). -/
lemma sigma_one_le_mul_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    ((σ 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1) := by
  have hfac : ((N : ℕ) : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p)) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod]
    push_cast [Nat.support_factorization]
    rfl
  have hsig : ((σ 1 N : ℕ) : ℚ)
      = ∏ p ∈ N.primeFactors, ((σ 1 (p ^ (N.factorization p)) : ℕ) : ℚ) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN]
    push_cast [Nat.support_factorization]
    rfl
  rw [hsig, hfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) ?_
  intro p hp
  exact sigma_one_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _

/-! ### Bounding `∏ p/(p-1)` over a set of at most twenty odd primes -/

/-- If there is no prime strictly between `a` and `b`, then every prime above `a` is `≥ b`. -/
lemma le_of_prime_gt_of_no_prime_between {a b : ℕ} (p : ℕ) (hp : p.Prime) (hap : a < p)
    (h : ∀ x < b, a < x → ¬ Nat.Prime x) : b ≤ p := by
  by_contra hc
  exact h p (not_le.mp hc) hap hp

/-- The map `x ↦ x/(x-1)` is antitone on integers `≥ 2`. -/
lemma ratio_antitone {a m : ℕ} (ha : 2 ≤ a) (ham : a ≤ m) :
    (m : ℚ) / (m - 1) ≤ (a : ℚ) / (a - 1) := by
  have ha' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have ham' : (a : ℚ) ≤ (m : ℚ) := by exact_mod_cast ham
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Comparison of `∏_{p ∈ S} p/(p-1)` against a list `L` of increasing integers `≥ 2`
having no primes in the gaps: if `S` consists of primes bounded below by the head of `L`
and `#S ≤ L.length`, then the product over `S` is at most the product over `L`. -/
lemma prod_ratio_le_list :
    ∀ (L : List ℕ), List.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) L →
      (∀ a ∈ L, 2 ≤ a) →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        (∀ a, L.head? = some a → ∀ p ∈ S, a ≤ p) → S.card ≤ L.length →
        ∏ p ∈ S, (p : ℚ) / (p - 1) ≤ (L.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
  intro L
  induction L with
  | nil =>
    intro _ _ S _ _ hcard
    simp only [List.length_nil, Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard]
  | cons a T ih =>
    intro hchain hge2 S hSp hSge hcard
    have ha2 : 2 ≤ a := hge2 a (by simp)
    have ha2' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha2
    have hTnonneg : (0 : ℚ) ≤ (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hge2 q (by simp [hq])
      exact le_of_lt (div_pos (by linarith) (by linarith))
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · simp only [Finset.prod_empty]
      refine List.one_le_prod ?_
      intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hge2 q hq
      rw [le_div_iff₀ (by linarith)]
      linarith
    · set m := S.min' hne with hm
      have hmS : m ∈ S := S.min'_mem hne
      have ham : a ≤ m := hSge a (by simp) m hmS
      have hm2 : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast le_trans ha2 ham
      have hprod : ∏ p ∈ S, (p : ℚ) / (p - 1)
          = ((m : ℚ) / (m - 1)) * ∏ p ∈ S.erase m, (p : ℚ) / (p - 1) :=
        (Finset.mul_prod_erase S _ hmS).symm
      have hIH : ∏ p ∈ S.erase m, (p : ℚ) / (p - 1)
          ≤ (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
        refine ih (List.IsChain.tail hchain) (fun x hx => hge2 x (by simp [hx])) _
          (fun p hp => hSp p (Finset.mem_of_mem_erase hp)) ?_ ?_
        · intro b hb p hp
          have hpS : p ∈ S := Finset.mem_of_mem_erase hp
          have hpm : m < p :=
            lt_of_le_of_ne (S.min'_le p hpS) (Ne.symm (Finset.ne_of_mem_erase hp))
          exact (List.isChain_cons.mp hchain).1 b hb p (hSp p hpS) (lt_of_le_of_lt ham hpm)
        · have hcard' := Finset.card_erase_of_mem hmS
          have hc : S.card ≤ T.length + 1 := by simpa using hcard
          omega
      have hmono : (m : ℚ) / (m - 1) ≤ (a : ℚ) / (a - 1) := ratio_antitone ha2 ham
      have hmpos : (0 : ℚ) ≤ (m : ℚ) / (m - 1) := le_of_lt (div_pos (by linarith) (by linarith))
      simp only [List.map_cons, List.prod_cons]
      rw [hprod]
      calc ((m : ℚ) / (m - 1)) * ∏ p ∈ S.erase m, (p : ℚ) / (p - 1)
          ≤ ((m : ℚ) / (m - 1)) * (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod :=
            mul_le_mul_of_nonneg_left hIH hmpos
        _ ≤ ((a : ℚ) / (a - 1)) * (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod :=
            mul_le_mul_of_nonneg_right hmono hTnonneg

/-- The first twenty odd primes. -/
def oddPrimes20 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

lemma chain_oddPrimes20 :
    List.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) oddPrimes20 := by
  simp only [oddPrimes20, List.isChain_cons, List.isChain_nil, List.head?_cons,
    Option.mem_def, Option.some.injEq, forall_eq', and_true, List.head?_nil,
    IsEmpty.forall_iff, reduceCtorEq, implies_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact fun p hp hap => le_of_prime_gt_of_no_prime_between p hp hap (by decide)

lemma prod_oddPrimes20_lt_four :
    (oddPrimes20.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod < 4 := by
  simp only [oddPrimes20, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- A set of at most twenty odd primes satisfies `∏ p/(p-1) < 4`. -/
lemma prod_ratio_lt_four_of_card_le_twenty {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) < 4 := by
  refine lt_of_le_of_lt ?_ prod_oddPrimes20_lt_four
  refine prod_ratio_le_list oddPrimes20 chain_oddPrimes20 (by decide) S
    (fun p hp => (hS p hp).1) ?_ (by simpa [oddPrimes20] using hcard)
  intro a ha p hp
  have ha3 : a = 3 := by simpa [oddPrimes20] using ha.symm
  subst ha3
  obtain ⟨hpp, hp2⟩ := hS p hp
  have := hpp.two_le
  omega

/-! ### The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If a betrothed (quasi-amicable) pair
`(m, n)` is coprime and its two members have the same parity, then both members are odd
and the product `m * n` has at least twenty-one distinct prime factors.

The proof is exact: coprimality forces `σ₁(m * n) = σ₁(m) σ₁(n) = (m + n + 1)^2 > 4 m n`,
i.e. `m * n` is an odd number of abundancy greater than `4`, while the product
`∏_{p ∣ m n} p/(p-1)` taken over at most twenty odd primes is smaller than `4`. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  -- Coprimality plus equal parity forces both members to be odd.
  have hmodd : m % 2 = 1 := by
    by_contra hc
    have hm2 : (2 : ℕ) ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have hn2 : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hdvd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hm2 hn2
    rw [Nat.Coprime] at hcop
    omega
  have hnodd : n % 2 = 1 := by omega
  refine ⟨Nat.odd_iff.mpr hmodd, Nat.odd_iff.mpr hnodd, ?_⟩
  by_contra hcontra
  push_neg at hcontra
  have hcard : (m * n).primeFactors.card ≤ 20 := by omega
  have hN0 : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- every prime factor of `m * n` is odd
  have hodd : ∀ p ∈ (m * n).primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have hdvd : (2 : ℕ) ∣ m * n := Nat.dvd_of_mem_primeFactors hp
    have : (m * n) % 2 = 1 := by
      rw [Nat.mul_mod, hmodd, hnodd]
    omega
  -- the sum of divisors of the product
  have hmul : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have hbound := sigma_one_le_mul_prod_primeFactors (N := m * n) hN0
  have hlt := prod_ratio_lt_four_of_card_le_twenty hodd hcard
  rw [hmul] at hbound
  have hmnpos : (0 : ℚ) < (m : ℚ) * n := by
    have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm0
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
    positivity
  have hupper : ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) < 4 * ((m : ℚ) * n) := by
    have hcast : (((m + n + 1) * (m + n + 1) : ℕ) : ℚ)
        = ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) := by push_cast; ring
    have h1 : ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1)
        ≤ ((m * n : ℕ) : ℚ) * ∏ p ∈ (m * n).primeFactors, (p : ℚ) / (p - 1) := by
      rw [← hcast]; exact hbound
    have h2 : ((m * n : ℕ) : ℚ) * ∏ p ∈ (m * n).primeFactors, (p : ℚ) / (p - 1)
        < ((m * n : ℕ) : ℚ) * 4 := by
      refine mul_lt_mul_of_pos_left hlt ?_
      push_cast
      exact hmnpos
    push_cast at h1 h2 ⊢
    linarith
  -- but `(m + n + 1)^2 > (m + n)^2 ≥ 4 m n`
  have hAMGM : 4 * ((m : ℚ) * n) ≤ ((m : ℚ) + n) * ((m : ℚ) + n) := by nlinarith [sq_nonneg ((m : ℚ) - n)]
  have hmnn : (0 : ℚ) ≤ (m : ℚ) + n := by positivity
  nlinarith

/-! ### Historical computational lower bounds (not formalized)

The theorem above is the *exact* statement proved here.  It should be distinguished from
the purely computational statements found in the literature on betrothed (quasi-amicable)
numbers, such as the assertions that exhaustive searches have found no same-parity
betrothed pair below various explicit search limits.  Those assertions rest on machine
computations over enormous ranges; none of them is formalized in this file, and nothing
below or above depends on them. -/

end Brockian.BetrothedNumbers

