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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1`. -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

@[simp] lemma cullen_zero : cullen 0 = 2 := rfl
@[simp] lemma cullen_one : cullen 1 = 3 := rfl

lemma cullen_pos (n : ℕ) : 0 < cullen n := Nat.succ_pos _

lemma one_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- `cullen` is strictly monotone on positive indices; in particular it grows. -/
lemma lt_cullen (n : ℕ) : n ≤ cullen n := by
  have : n ≤ n * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.pos_pow_of_pos _ (by norm_num))
  exact this.trans (Nat.le_succ _)

/-!
## An unconditional Fermat-type divisibility result

For an odd prime `p`, Fermat's little theorem gives `2 ^ (p - 1) ≡ 1 [MOD p]`, hence
`C (p - 1) = (p - 1) * 2 ^ (p - 1) + 1 ≡ -1 + 1 ≡ 0 [MOD p]`.
Consequently every odd prime divides some Cullen number, and infinitely many Cullen
numbers are composite.
-/

lemma two_pow_sub_one_eq_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    ((2 : ZMod p)) ^ (p - 1) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ZMod.pow_card_sub_one_eq_one ?_
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h2
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- **Fermat-type divisibility for Cullen numbers**: every odd prime `p` divides the
Cullen number `C (p - 1)`. -/
theorem prime_dvd_cullen_sub_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
      push_cast [Nat.cast_sub hp1]; ring
    rw [this, ZMod.natCast_self]; ring
  have : ((cullen (p - 1) : ℕ) : ZMod p) = 0 := by
    unfold cullen
    push_cast
    rw [hcast, two_pow_sub_one_eq_one p hp hodd]
    ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp this

/-- For a prime `p ≥ 5` the Cullen number `C (p - 1)` is composite. -/
theorem not_prime_cullen_sub_one (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ (cullen (p - 1)).Prime := by
  have hodd : p ≠ 2 := by omega
  have hdvd : p ∣ cullen (p - 1) := prime_dvd_cullen_sub_one p hp hodd
  intro hprime
  have hle : p = cullen (p - 1) ∨ p = 1 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
    · exact Or.inr h
    · exact Or.inl h.symm
  -- but `C (p-1) = (p-1) * 2^(p-1) + 1 > p`
  have hgrow : p < cullen (p - 1) := by
    have h1 : p ≤ 2 ^ (p - 1) := by
      calc p ≤ 2 ^ p := Nat.le_of_lt (Nat.lt_two_pow_self)
        _ ≤ 2 ^ (p - 1) * 2 := by
            rw [← pow_succ]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ (p - 1) * 2 := le_rfl
      -- refine below
    have h2 : 2 ≤ p - 1 := by omega
    have h3 : p < (p - 1) * 2 ^ (p - 1) := by
      have : 2 * p ≤ (p - 1) * 2 ^ (p-1) := by
        have hb : 2 ≤ 2 ^ (p - 1) := by
          calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 * p ≤ 2 * (2 ^ (p-1)) := by omega
          _ ≤ (p - 1) * 2 ^ (p - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold cullen; omega
  omega

/-- **Infinitely many Cullen numbers are composite.** -/
theorem infinite_composite_cullen : {n : ℕ | ¬ (cullen n).Prime}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (N + 2) 5)
  refine ⟨p - 1, ?_, ?_⟩
  · exact not_prime_cullen_sub_one p hp (le_trans (le_max_right _ _) hpge)
  · have := le_trans (le_max_left (N + 2) 5) hpge
    omega

/-!
## Woodall numbers

For an odd prime `p` we have `(p-1)^2 ≡ 1 [MOD p]` and `(p-1) ∣ (p-1)^2`, so
`2 ^ ((p-1)^2) ≡ 1 [MOD p]`, whence `p ∣ W ((p-1)^2)`.
-/

/-- **Fermat-type divisibility for Woodall numbers**: every odd prime `p` divides the
Woodall number `W ((p - 1) ^ 2)`. -/
theorem prime_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ woodall ((p - 1) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set n := (p - 1) ^ 2 with hn
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcast : ((n : ℕ) : ZMod p) = 1 := by
    have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
        push_cast [Nat.cast_sub hp1]; ring
      rw [this, ZMod.natCast_self]; ring
    rw [hn]
    push_cast
    rw [h1]; ring
  have hpow : ((2 : ZMod p)) ^ n = 1 := by
    have hdvd : (p - 1) ∣ n := by
      rw [hn, pow_two]; exact Dvd.intro _ rfl
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, two_pow_sub_one_eq_one p hp hodd, one_pow]
  have hzero : ((n * 2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [hcast, hpow]
    ring
  have hmod : (1 : ℕ) ≡ n * 2 ^ n [MOD p] := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mp hzero.symm
    exact this
  have hone : 1 ≤ n * 2 ^ n := by
    have hnpos : 1 ≤ n := by
      have : 2 ≤ p := hp.two_le
      have : 1 ≤ p - 1 := by omega
      rw [hn]; nlinarith
    exact one_le_mul_two_pow hnpos
  exact (Nat.modEq_iff_dvd' hone).mp hmod

/-!
## The conjecture and its reduction

The infinitude of Cullen primes is an open problem: no proof is known that `n * 2 ^ n + 1`
is prime for infinitely many `n` (the known Cullen prime indices begin
`1, 141, 4713, 5795, 6611, 18496, …`).  What we record here is the exact reduction of the
conjecture to an unboundedness statement, together with the unconditional partial results
above.
-/

/-- The (open) Cullen prime conjecture: there are infinitely many Cullen primes. -/
def CullenPrimeConjecture : Prop := {n : ℕ | (cullen n).Prime}.Infinite

/-- **Cullen prime infinitude, as a Lean-checked reduction.**

The set of indices `n` for which the Cullen number `C n = n * 2 ^ n + 1` is prime is
infinite **if and only if** such indices are arbitrarily large.  In particular the
right-to-left direction is a conditional proof of the Cullen prime conjecture from the
hypothesis that for every bound `N` some `n > N` yields a Cullen prime.

(The unconditional statement is an open problem; see `infinite_composite_cullen` and
`prime_dvd_cullen_sub_one` for the unconditional results proved in this file.) -/
theorem CullenPrimeInfinitude :
    {n : ℕ | (cullen n).Prime}.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ (cullen n).Prime := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h N
    exact ⟨n, hlt, hn⟩
  · intro h N
    obtain ⟨n, hlt, hn⟩ := h N
    exact ⟨n, hn, hlt⟩

/-- Restatement of the reduction in terms of `CullenPrimeConjecture`. -/
theorem cullenPrimeConjecture_iff :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n, N < n ∧ (cullen n).Prime :=
  CullenPrimeInfinitude

/-- A sanity check: `C 1 = 3` is a Cullen prime, while `C 2 = 9` is not. -/
example : (cullen 1).Prime ∧ ¬ (cullen 2).Prime := by
  constructor
  · rw [cullen_one]; norm_num
  · unfold cullen; norm_num
    decide

end Brockian.CullenWoodall

