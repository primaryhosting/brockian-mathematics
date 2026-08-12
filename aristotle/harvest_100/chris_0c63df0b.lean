import Mathlib

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

/-
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1)

/-- A Carmichael number is a Fermat pseudoprime to every base: this is the "easy"
direction of Korselt's criterion, justifying the definition above. -/
theorem isCarmichael_fermat {n : ℕ} (hn : IsCarmichael n) (a : ℕ) :
    a ^ n ≡ a [MOD n] := by
  obtain ⟨h1, -, hsq, hkor⟩ := hn
  have hpos : 0 < n := lt_trans Nat.zero_lt_one h1
  -- for each prime factor `p` of `n`, `p ∣ a ^ n - a`
  have key : ∀ p ∈ n.primeFactors, p ∣ a ^ n - a := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle : a ≤ a ^ n := Nat.le_self_pow hpos.ne' a
    have hmod : a ≡ a ^ n [MOD p] := by
      by_cases hdvd : p ∣ a
      · have h1' : a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
        have h2' : a ^ n ≡ 0 ^ n [MOD p] := h1'.pow n
        rw [zero_pow hpos.ne'] at h2'
        exact h1'.trans h2'.symm
      · have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hdvd).symm
        obtain ⟨m, hm⟩ := hkor p hp
        have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
          have := Nat.ModEq.pow_totient hcop
          rwa [Nat.totient_prime hpp] at this
        have hpow : a ^ (n - 1) ≡ 1 [MOD p] := by
          have : a ^ (n - 1) = (a ^ (p - 1)) ^ m := by rw [← pow_mul, ← hm]
          rw [this]
          simpa using hfermat.pow m
        have : a ^ (n - 1) * a ≡ 1 * a [MOD p] := hpow.mul_right a
        have heq : a ^ (n - 1) * a = a ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        rw [heq, one_mul] at this
        exact this.symm
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  have hprod : ∏ p ∈ n.primeFactors, p ∣ a ^ n - a :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => key p hp)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hprod
  have hle : a ≤ a ^ n := Nat.le_self_pow hpos.ne' a
  exact ((Nat.modEq_iff_dvd' hle).mpr hprod).symm

/-- If `n > 1` is a Fermat pseudoprime to every base, then `n` is squarefree. -/
theorem squarefree_of_fermat {n : ℕ} (hn : 1 < n) (h : ∀ a : ℕ, a ^ n ≡ a [MOD n]) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hdvd
  have hx2 : 2 ≤ x := hx.two_le
  have hle : x ≤ x ^ n := Nat.le_self_pow (by omega) x
  have hn' : n ∣ x ^ n - x := (Nat.modEq_iff_dvd' hle).mp (h x).symm
  have hxx : x * x ∣ x ^ n - x := dvd_trans hdvd hn'
  have hxxn : x * x ∣ x ^ n := by
    refine ⟨x ^ (n - 2), ?_⟩
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  have hdvdx : x * x ∣ x := by
    have := Nat.dvd_sub hxxn hxx
    simpa [Nat.sub_sub_self hle] using this
  have := Nat.le_of_dvd (by omega) hdvdx
  nlinarith

/-- If `n > 1` is a Fermat pseudoprime to every base, then `p - 1 ∣ n - 1` for every prime
factor `p` of `n`.  The proof uses a primitive root modulo `p`. -/
theorem korselt_of_fermat {n : ℕ} (hn : 1 < n) (h : ∀ a : ℕ, a ^ n ≡ a [MOD n])
    {p : ℕ} (hp : p ∈ n.primeFactors) : (p - 1) ∣ (n - 1) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := ((g : ZMod p)).val with ha
  have hcast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha, ZMod.natCast_val, ZMod.cast_id]
  have hmod : a ^ n ≡ a [MOD p] := Nat.ModEq.of_dvd hpn (h a)
  have hz : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at this
    exact this
  rw [hcast] at hz
  have hgn : g ^ n = g := by
    ext
    push_cast
    exact hz
  have hone : g ^ (n - 1) = 1 := by
    have h2 : g ^ (n - 1) * g = 1 * g := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
      exact hgn
    exact mul_right_cancel h2
  have hdvd := orderOf_dvd_of_pow_eq_one hone
  rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hpp] at hdvd

/-- **Korselt's criterion**: a composite `n` is a Fermat pseudoprime to every base if and
only if it is squarefree and `p - 1 ∣ n - 1` for every prime factor `p`.  This shows that
`IsCarmichael` agrees with the classical definition of a Carmichael number. -/
theorem isCarmichael_iff_fermat {n : ℕ} :
    IsCarmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n] := by
  constructor
  · rintro hC
    exact ⟨hC.1, hC.2.1, fun a => isCarmichael_fermat hC a⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, squarefree_of_fermat h1 h3, fun p hp => korselt_of_fermat h1 h3 hp⟩

section Chernick

variable {k : ℕ}

/-- Chernick's identity: `(6k+1)(12k+1)(18k+1) = 36k(36k² + 11k + 1) + 1`. -/
theorem chernick_expand (k : ℕ) :
    (6 * k + 1) * (12 * k + 1) * (18 * k + 1) = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by
  ring

/-- The prime factors of a product of three distinct primes. -/
theorem primeFactors_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    (p * q * r).primeFactors = {p, q, r} := by
  rw [Nat.primeFactors_mul (Nat.mul_ne_zero hp.pos.ne' hq.pos.ne') hr.pos.ne',
    Nat.primeFactors_mul hp.pos.ne' hq.pos.ne',
    hp.primeFactors, hq.primeFactors, hr.primeFactors]
  ext x
  simp

/-- A product of three pairwise distinct primes is squarefree. -/
theorem squarefree_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Squarefree (p * q * r) := by
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  rw [Nat.squarefree_mul (Nat.Coprime.mul_left hcpr hcqr), Nat.squarefree_mul hcpq]
  exact ⟨⟨hp.squarefree, hq.squarefree⟩, hr.squarefree⟩

/-- General criterion for a product of three distinct primes to be Carmichael:
it suffices that `p - 1`, `q - 1` and `r - 1` each divide `pqr - 1`. -/
theorem isCarmichael_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (dp : (p - 1) ∣ (p * q * r - 1)) (dq : (q - 1) ∣ (p * q * r - 1))
    (dr : (r - 1) ∣ (p * q * r - 1)) :
    IsCarmichael (p * q * r) ∧ (p * q * r).primeFactors.card = 3 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hr2 : 2 ≤ r := hr.two_le
  have hfac : (p * q * r).primeFactors = {p, q, r} := primeFactors_three hp hq hr
  have hsq : Squarefree (p * q * r) := squarefree_three hp hq hr hpq hpr hqr
  have hgt : 1 < p * q * r := by
    calc 1 < 2 * 2 * 2 := by norm_num
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq2) hr2
  refine ⟨⟨hgt, ?_, hsq, ?_⟩, ?_⟩
  · refine Nat.not_prime_mul ?_ (by omega)
    have : 2 * 2 ≤ p * q := Nat.mul_le_mul hp2 hq2
    omega
  · intro s hs
    rw [hfac] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact dp
    · exact dq
    · exact dr
  · rw [hfac, Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr])]
    simp

/-- **Chernick's theorem**: if `6k+1`, `12k+1` and `18k+1` are all prime (with `k ≥ 1`),
then their product is a Carmichael number with exactly three prime factors. -/
theorem chernick_isCarmichael (hk : 1 ≤ k)
    (h1 : Nat.Prime (6 * k + 1)) (h2 : Nat.Prime (12 * k + 1)) (h3 : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  have hexp := chernick_expand k
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  refine isCarmichael_three_primes h1 h2 h3 (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
    rw [hsub]
  · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩
  · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩
  · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩

end Chernick

/-- `1729` (the Hardy–Ramanujan number, `k = 1` in Chernick's family) is a Carmichael
number with exactly three prime factors. -/
theorem isCarmichael_1729 : IsCarmichael 1729 ∧ (Nat.primeFactors 1729).card = 3 := by
  have := chernick_isCarmichael (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- **Conditional infinitude of three-prime Carmichael numbers.**

Assuming the Dickson/Hardy–Littlewood-type hypothesis that the linear forms
`6k+1, 12k+1, 18k+1` are simultaneously prime for arbitrarily large `k`
(a special case of Dickson's conjecture, which is open), there are infinitely many
Carmichael numbers with exactly three prime factors. -/
theorem ThreePrimeCarmichaelInfinitude
    (hDickson : ∀ N : ℕ, ∃ k, N < k ∧
      Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)) :
    ∀ N : ℕ, ∃ n, N < n ∧ IsCarmichael n ∧ n.primeFactors.card = 3 := by
  intro N
  obtain ⟨k, hkN, h1, h2, h3⟩ := hDickson N
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), ?_, ?_, ?_⟩
  · calc N < 6 * k + 1 := by omega
      _ ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := by
          have h : (6 * k + 1) ≤ (6 * k + 1) * (12 * k + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          exact h.trans (Nat.le_mul_of_pos_right _ (by omega))
  · exact (chernick_isCarmichael (by omega) h1 h2 h3).1
  · exact (chernick_isCarmichael (by omega) h1 h2 h3).2

/-- Set-theoretic form of the conditional infinitude statement. -/
theorem threePrimeCarmichael_infinite
    (hDickson : ∀ N : ℕ, ∃ k, N < k ∧
      Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)) :
    {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hC⟩ := ThreePrimeCarmichaelInfinitude hDickson N
  exact absurd (hN (show n ∈ {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3} from hC))
    (by omega)

end CarmichaelKorselt
end Brockian

