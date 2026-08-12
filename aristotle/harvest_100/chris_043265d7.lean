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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring because Lean 4 requires `import`
commands to precede every other command, including module docstrings.)

## Contents

* `PolignacProperty n` : there are infinitely many pairs of consecutive primes `(p, p+n)`.
* `DicksonTwoForms` : Dickson's conjecture for two linear forms with equal leading
  coefficients.
* `PolignacConjecture` : Dickson's conjecture implies Polignac's conjecture for every
  positive even gap. This is a Lean-checked conditional reduction of Polignac's
  conjecture (which is open) to a standard prime-tuple hypothesis.
* `not_polignacProperty_of_odd` : unconditionally, Polignac's property fails for odd gaps.
* `polignacProperty_two_iff_twinPrimes` : for gap `2` Polignac's property is exactly the
  twin prime conjecture.
-/

namespace Brockian.PolignacPrimes

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies
strictly between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ Nat.Prime r

/-- The statement of Polignac's conjecture for the gap `n`: there are infinitely many
pairs of consecutive primes `(p, p + n)`. -/
def PolignacProperty (n : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ ConsecutivePrimes p (p + n)

/-- Dickson's conjecture for two linear forms `M * x + a` and `M * x + b` sharing the
same leading coefficient: if the pair is admissible (for every prime `q` some value of
`x` makes the product of the two forms indivisible by `q`), then both forms are
simultaneously prime for infinitely many `x`. -/
def DicksonTwoForms : Prop :=
  ∀ M a b : ℕ, 0 < M →
    (∀ q : ℕ, Nat.Prime q → ∃ x : ℕ, ¬ (q ∣ (M * x + a) * (M * x + b))) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ Nat.Prime (M * x + a) ∧ Nat.Prime (M * x + b)

/-- Solving `M * t + c ≡ 0 (mod q)` when `q` is a prime not dividing `M`. -/
lemma exists_mul_add_dvd {q M : ℕ} (c : ℕ) (hq : Nat.Prime q) (hM : ¬ q ∣ M) :
    ∃ t : ℕ, q ∣ M * t + c := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hMne : (M : ZMod q) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M q).mp h)
  refine ⟨((-(c : ZMod q)) * (M : ZMod q)⁻¹).val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  field_simp
  ring

/-- The sieving construction: a modulus `M` and residue `a` such that for each
`1 ≤ j ≤ k` the number `a + j` is divisible by a prime `> n` dividing `M`, while `a`
and `a + n` are coprime to `M`. -/
lemma exists_sieving_residue (n : ℕ) (hn : 2 ≤ n) :
    ∀ k : ℕ, k + 1 ≤ n →
      ∃ M a : ℕ, 0 < M ∧ Odd M ∧
        (∀ r : ℕ, Nat.Prime r → r ∣ M → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∣ M ∧ q ∣ (a + j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, 1, one_pos, odd_one,
      fun r hr hd => absurd (Nat.eq_one_of_dvd_one hd) hr.ne_one,
      fun j hj1 hj2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨M, a, hM0, hModd, hcop, hdiv⟩ := ih (by omega)
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (M + n + k + 2)
    have hqM : ¬ q ∣ M := fun h => absurd (Nat.le_of_dvd hM0 h) (by omega)
    obtain ⟨t, ht⟩ := exists_mul_add_dvd (a + (k + 1)) hq hqM
    have htq : q ∣ a + M * t + (k + 1) := by
      have h : a + M * t + (k + 1) = M * t + (a + (k + 1)) := by ring
      rwa [h]
    refine ⟨M * q, a + M * t, Nat.mul_pos hM0 hq.pos, ?_, ?_, ?_⟩
    · exact hModd.mul (hq.odd_of_ne_two (by omega))
    · intro r hr hrdvd
      rcases (Nat.Prime.dvd_mul hr).mp hrdvd with hrM | hrq
      · obtain ⟨h1, h2⟩ := hcop r hr hrM
        have hMt : r ∣ M * t := hrM.mul_right t
        refine ⟨fun h => h1 (by simpa using Nat.dvd_sub h hMt), fun h => h2 ?_⟩
        have hsub : r ∣ (a + M * t + n) - M * t := Nat.dvd_sub h hMt
        have heq : (a + M * t + n) - M * t = a + n := by omega
        rwa [heq] at hsub
      · have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
        subst hrq'
        constructor
        · intro h
          have hsub : r ∣ (a + M * t + (k + 1)) - (a + M * t) := Nat.dvd_sub htq h
          have heq : (a + M * t + (k + 1)) - (a + M * t) = k + 1 := by omega
          rw [heq] at hsub
          exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
        · intro h
          have hsub : r ∣ (a + M * t + n) - (a + M * t + (k + 1)) := Nat.dvd_sub h htq
          have heq : (a + M * t + n) - (a + M * t + (k + 1)) = n - (k + 1) := by omega
          rw [heq] at hsub
          exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
    · intro j hj1 hj2
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · obtain ⟨p, hp, hpn, hpM, hpa⟩ := hdiv j hj1 (by omega)
        refine ⟨p, hp, hpn, hpM.mul_right q, ?_⟩
        have heq : a + M * t + j = (a + j) + M * t := by ring
        rw [heq]
        exact Nat.dvd_add hpa (hpM.mul_right t)
      · have hjeq : j = k + 1 := by omega
        subst hjeq
        exact ⟨q, hq, by omega, Dvd.intro_left M rfl, htq⟩

/-- Two distinct small shifts cannot both be roots of the same linear form mod `r`. -/
lemma no_two_roots {r M c x y : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2) (hM : ¬ r ∣ M)
    (hxy : x < y) (hy : y ≤ 2) (h1 : r ∣ M * x + c) (h2 : r ∣ M * y + c) : False := by
  have hd : r ∣ (M * y + c) - (M * x + c) := Nat.dvd_sub h2 h1
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hM2 : ¬ r ∣ 2 * M := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hM h
  interval_cases y <;> interval_cases x
  · exact hM (by rwa [show M * 1 + c - (M * 0 + c) = M by omega] at hd)
  · exact hM2 (by rwa [show M * 2 + c - (M * 0 + c) = 2 * M by omega] at hd)
  · exact hM (by rwa [show M * 2 + c - (M * 1 + c) = M by omega] at hd)

/-- Admissibility of the pair of forms produced by the sieving construction. -/
lemma admissible {n M a : ℕ} (hn : Even n) (hM : Odd M)
    (hcop : ∀ r : ℕ, Nat.Prime r → r ∣ M → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) :
    ∀ q : ℕ, Nat.Prime q → ∃ x : ℕ, ¬ (q ∣ (M * x + a) * (M * x + (a + n))) := by
  intro q hq
  by_cases hqM : q ∣ M
  · obtain ⟨h1, h2⟩ := hcop q hq hqM
    refine ⟨0, fun h => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
  · by_cases hq2 : q = 2
    · subst hq2
      obtain ⟨m, hm⟩ := hn
      obtain ⟨k, hk⟩ := hM
      rcases Nat.even_or_odd a with ha | ha
      · obtain ⟨b, hb⟩ := ha
        refine ⟨1, fun h => ?_⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
        · obtain ⟨c, hc⟩ := h; omega
        · obtain ⟨c, hc⟩ := h; omega
      · obtain ⟨b, hb⟩ := ha
        refine ⟨0, fun h => ?_⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
        · obtain ⟨c, hc⟩ := h; omega
        · obtain ⟨c, hc⟩ := h; omega
    · by_contra hcon
      push_neg at hcon
      have h0 := (Nat.Prime.dvd_mul hq).mp (hcon 0)
      have h1 := (Nat.Prime.dvd_mul hq).mp (hcon 1)
      have h2 := (Nat.Prime.dvd_mul hq).mp (hcon 2)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        first
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h0 h1
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h0 h2
          | exact no_two_roots hq hq2 hqM (by omega) (by omega) h1 h2

/-- **Polignac's conjecture**, conditionally on Dickson's conjecture for two linear
forms: for every positive even `n` there are infinitely many pairs of consecutive
primes differing by `n`. -/
theorem PolignacConjecture (hD : DicksonTwoForms) (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    PolignacProperty n := by
  have hn2 : 2 ≤ n := by rcases hn with ⟨m, hm⟩; omega
  obtain ⟨M, a, hM0, hModd, hcop, hdiv⟩ := exists_sieving_residue n hn2 (n - 1) (by omega)
  intro N
  obtain ⟨x, hx, hp1, hp2⟩ :=
    hD M a (a + n) hM0 (admissible hn hModd hcop) (N + M + 2)
  have hxM : x ≤ M * x := Nat.le_mul_of_pos_left x hM0
  have hMx : M ≤ M * x := Nat.le_mul_of_pos_right M (by omega)
  refine ⟨M * x + a, by omega, hp1, ?_, by omega, ?_⟩
  · have heq : M * x + (a + n) = M * x + a + n := by ring
    rwa [heq] at hp2
  · intro r hr1 hr2 hrp
    obtain ⟨q, hq, hqn, hqM, hqa⟩ := hdiv (r - (M * x + a)) (by omega) (by omega)
    have hqr : q ∣ r := by
      have heq : r = M * x + (a + (r - (M * x + a))) := by omega
      rw [heq]
      exact Nat.dvd_add (hqM.mul_right x) hqa
    have hqeq := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqr
    have hqle : q ≤ M := Nat.le_of_dvd hM0 hqM
    omega

/-- Unconditionally, Polignac's property fails for every odd gap: consecutive primes
differing by an odd amount force one of them to be even. -/
theorem not_polignacProperty_of_odd {n : ℕ} (hn : Odd n) : ¬ PolignacProperty n := by
  intro h
  obtain ⟨p, hp2, hpp, hqq, hlt, -⟩ := h 2
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  have hev : Even (p + n) := hpodd.add_odd hn
  have h2 := (Nat.Prime.even_iff hqq).mp hev
  obtain ⟨m, hm⟩ := hn
  omega

/-- For the gap `2`, Polignac's property is equivalent to the twin prime conjecture. -/
theorem polignacProperty_two_iff_twinPrimes :
    PolignacProperty 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  constructor
  · intro h N
    obtain ⟨p, hN, hp, hq, -, -⟩ := h N
    exact ⟨p, hN, hp, hq⟩
  · intro h N
    obtain ⟨p, hN, hp, hq⟩ := h (max N 2)
    refine ⟨p, by omega, hp, hq, by omega, ?_⟩
    intro r hr1 hr2 hrp
    have hreq : r = p + 1 := by omega
    subst hreq
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hev : Even (p + 1) := hpodd.add_one
    have h2 := (Nat.Prime.even_iff hrp).mp hev
    omega

end Brockian.PolignacPrimes

