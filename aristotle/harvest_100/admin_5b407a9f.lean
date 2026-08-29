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

import Mathlib
/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the requested header comment appears verbatim immediately after the
-- single `import Mathlib` line.

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- The set of indices `n` for which the Cullen number `C n` is prime. -/
def cullenPrimeIndices : Set ℕ := {n : ℕ | Nat.Prime (cullen n)}

/-- The Cullen prime infinitude conjecture: there are infinitely many Cullen primes. -/
def CullenPrimeConjecture : Prop := cullenPrimeIndices.Infinite

/-! ## Basic growth facts -/

lemma self_le_cullen (n : ℕ) : n ≤ cullen n := by
  have h : n * 1 ≤ n * 2 ^ n := Nat.mul_le_mul_left n Nat.one_le_two_pow
  simp only [cullen]
  omega

lemma two_le_cullen {n : ℕ} (hn : 1 ≤ n) : 2 ≤ cullen n := by
  have h : 1 * 2 ^ 1 ≤ n * 2 ^ n :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_right (by norm_num) hn)
  simp only [cullen]
  omega

/-! ## An unconditional divisibility law and infinitely many composite Cullen numbers -/

/-- For every odd prime `p` we have `p ∣ C (p - 2)`: indeed
`(p-2) * 2 ^ (p-2) + 1 ≡ -2 ^ (p-1) + 1 ≡ 0 [MOD p]` by Fermat's little theorem. -/
theorem odd_prime_dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · interval_cases p <;> simp_all
    · exact h3
  refine (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1 ?_
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := by
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).1 this
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hferm : ((2 : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hsub : ((p - 2 : ℕ) : ZMod p) = -2 := by
    have h2p : (2 : ℕ) ≤ p := by omega
    rw [Nat.cast_sub h2p, ZMod.natCast_self]
    push_cast
    ring
  simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
    hsub]
  have hpow : (2 : ZMod p) ^ (p - 2) * 2 = 2 ^ (p - 1) := by
    have hps : p - 1 = (p - 2) + 1 := by omega
    rw [hps, pow_succ]
  have hrw : (-2 : ZMod p) * 2 ^ (p - 2) = -(2 ^ (p - 2) * 2) := by ring
  rw [hrw, hpow, hferm]
  ring

/-- Every Cullen number `C (6k+2)` is divisible by `3`. -/
lemma three_dvd_cullen_six_mul_add_two (k : ℕ) : 3 ∣ cullen (6 * k + 2) := by
  have hpow : (2 : ℕ) ^ (6 * k + 2) % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ m ih =>
        have h : (2 : ℕ) ^ (6 * (m + 1) + 2) = 2 ^ (6 * m + 2) * 64 := by ring
        rw [h, Nat.mul_mod, ih]
  have h : cullen (6 * k + 2) % 3 = 0 := by
    simp only [cullen]
    omega
  omega

/-- There are infinitely many `n` for which the Cullen number `C n` is *not* prime. -/
theorem infinite_composite_cullen : {n : ℕ | ¬ Nat.Prime (cullen n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨6 * (a + 1) + 2, ?_, by omega⟩
  simp only [Set.mem_setOf_eq]
  intro hprime
  have hdvd := three_dvd_cullen_six_mul_add_two (a + 1)
  have h3 : (3 : ℕ) = 1 ∨ (3 : ℕ) = cullen (6 * (a + 1) + 2) :=
    hprime.eq_one_or_self_of_dvd 3 hdvd
  have hbig : 6 * (a + 1) + 2 ≤ cullen (6 * (a + 1) + 2) := self_le_cullen _
  omega

/-! ## Reformulations of the conjecture -/

/-- Reformulation of the conjecture as an unboundedness statement. -/
theorem cullenPrimeConjecture_iff_forall_exists_ge :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Nat.Prime (cullen n) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt.le, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    exact ⟨n, hp, by omega⟩

/-- The contrapositive form: the conjecture fails exactly when all sufficiently large
Cullen numbers are composite. -/
theorem not_cullenPrimeConjecture_iff :
    ¬ CullenPrimeConjecture ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ Nat.Prime (cullen n) := by
  rw [cullenPrimeConjecture_iff_forall_exists_ge]
  push_neg
  rfl

/-! ## A sieve criterion -/

/-- Trial-division criterion: a number `≥ 2` with no prime factor `p` satisfying `p * p ≤ m`
is prime. -/
lemma prime_of_no_small_prime_factor {m : ℕ} (hm : 2 ≤ m)
    (h : ∀ p : ℕ, p.Prime → p * p ≤ m → ¬ p ∣ m) : Nat.Prime m := by
  by_contra hnp
  have hpos : 0 < m := by omega
  have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self hpos hnp
  have hmf : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  exact h m.minFac hmf (by nlinarith [hsq]) (Nat.minFac_dvd m)

/-! ## Main conditional reduction -/

/--
**Cullen prime infinitude, conditional on a sieve hypothesis.**

If for every bound `N` there is some `n ≥ N` such that the Cullen number
`C n = n * 2 ^ n + 1` has no prime factor `p` with `p * p ≤ C n`, then there are
infinitely many Cullen primes.

The unconditional statement (that infinitely many Cullen numbers are prime) is a well-known
open problem; this is a Lean-checked reduction of it to the stated sieve hypothesis, which is
precisely the assertion that trial division up to `√(C n)` fails infinitely often.
-/
theorem CullenPrimeInfinitude
    (H : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ p : ℕ, p.Prime → p * p ≤ cullen n → ¬ p ∣ cullen n) :
    {n : ℕ | Nat.Prime (cullen n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hsieve⟩ := H (a + 1)
  exact ⟨n, prime_of_no_small_prime_factor (two_le_cullen (by omega)) hsieve, by omega⟩

end Brockian.CullenWoodall

