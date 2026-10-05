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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- repeated below verbatim as this module's docstring.)
import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

open Nat

/-- Pépin's condition for the `n`-th Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
def PepinWitness (n : ℕ) : Prop :=
  (3 : ZMod (Nat.fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1

/-- For `n ≥ 1`, the Fermat number `Fₙ` is congruent to `1` modulo `4`. -/
lemma fermatNumber_mod_four (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 4 = 1 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 2 := ⟨2 ^ n - 2, by omega⟩
  have : Nat.fermatNumber n = 4 * 2 ^ k + 1 := by
    rw [Nat.fermatNumber, hk]
    ring
  rw [this]
  omega

/-- For `n ≥ 1`, the Fermat number `Fₙ` is congruent to `2` modulo `3`. -/
lemma fermatNumber_mod_three (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 3 = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ m := by
    rw [hm, pow_succ]; ring
  have h4 : (2 : ℕ) ^ (2 ^ n) = 4 ^ (2 ^ m) := by
    rw [hpow, pow_mul]
    norm_num
  have : (4 : ℕ) ^ (2 ^ m) % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.fermatNumber, h4]
  omega

/-- For `n ≥ 1`, `(Fₙ - 1) / 2 = 2 ^ (2 ^ n - 1)`, i.e. `Fₙ / 2 = 2 ^ (2 ^ n - 1)`. -/
lemma fermatNumber_div_two (n : ℕ) : Nat.fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
  have : Nat.fermatNumber n = 2 * 2 ^ k + 1 := by
    rw [Nat.fermatNumber, hk, pow_succ]; ring
  rw [this, hk]
  simp [Nat.mul_add_div]

/-- `2` is a quadratic nonresidue modulo `3`, i.e. the Legendre symbol `(2 | 3)` is `-1`. -/
lemma legendreSym_three_two : legendreSym 3 2 = -1 := by decide

/-- If a prime `p` satisfies `p % 4 = 1` and `p % 3 = 2`, then `3` is a quadratic
nonresidue modulo `p`. -/
lemma legendreSym_three_eq_neg_one (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 1) (h3 : p % 3 = 2) :
    legendreSym p 3 = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hqr : legendreSym 3 (p : ℤ) = legendreSym p 3 :=
    legendreSym.quadratic_reciprocity_one_mod_four h4 (by norm_num)
  have hmod : legendreSym 3 (p : ℤ) = legendreSym 3 ((p : ℤ) % ((3 : ℕ) : ℤ)) :=
    legendreSym.mod (p := 3) _
  have hcast : ((p : ℤ) % ((3 : ℕ) : ℤ)) = 2 := by push_cast; omega
  rw [← hqr, hmod, hcast]
  exact legendreSym_three_two

/-- **Pépin's test, necessity.** If the `n`-th Fermat number (`n ≥ 1`) is prime, then
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
theorem pepinWitness_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (Nat.fermatNumber n).Prime) :
    PepinWitness n := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  set p := Nat.fermatNumber n with hpdef
  have hleg : legendreSym p 3 = -1 :=
    legendreSym_three_eq_neg_one p (fermatNumber_mod_four n hn) (fermatNumber_mod_three n hn)
  -- Euler's criterion
  have heuler : ((legendreSym p 3 : ℤ) : ZMod p) = ((3 : ℤ) : ZMod p) ^ (p / 2) :=
    legendreSym.eq_pow (p := p) 3
  rw [hleg, fermatNumber_div_two n] at heuler
  unfold PepinWitness
  rw [← hpdef]
  push_cast at heuler
  rw [← heuler]

/-- **Pépin's test.** For `n ≥ 1`, the `n`-th Fermat number is prime if and only if
Pépin's condition `3 ^ ((Fₙ - 1) / 2) = -1 (mod Fₙ)` holds. -/
theorem prime_fermatNumber_iff_pepinWitness (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fermatNumber n).Prime ↔ PepinWitness n :=
  ⟨pepinWitness_of_prime n hn, fun h => Nat.pepin_primality n h⟩

/-- The first five Fermat numbers `F₀ = 3, F₁ = 5, F₂ = 17, F₃ = 257, F₄ = 65537` are prime. -/
lemma prime_fermatNumber_of_le_four (n : ℕ) (hn : n ≤ 4) : (Nat.fermatNumber n).Prime := by
  interval_cases n <;> · rw [Nat.fermatNumber]; norm_num

/-- `F₅ = 4294967297 = 641 * 6700417` is not prime, so index `4` is the last index for which
a Fermat prime is currently known. -/
lemma not_prime_fermatNumber_five : ¬ (Nat.fermatNumber 5).Prime := by
  rw [Nat.fermatNumber]
  norm_num

/-- **Fermat prime beyond four.** The existence of a Fermat prime `Fₙ` with index `n > 4`
-- the first open range, since `F₀, …, F₄` are prime while `F₅` is composite -- is equivalent
to the existence of an index `n > 4` satisfying Pépin's condition. This is a Lean-checked
reduction of the (open) conjecture to an explicit, effectively testable criterion. -/
theorem FermatPrimeBeyondFour :
    (∃ n, 4 < n ∧ (Nat.fermatNumber n).Prime) ↔ (∃ n, 4 < n ∧ PepinWitness n) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, pepinWitness_of_prime n (by omega) hp⟩
  · rintro ⟨n, hn, hw⟩
    exact ⟨n, hn, Nat.pepin_primality n hw⟩

/-- A weaker, unconditional reading of "Fermat prime beyond four": there is a Fermat number
exceeding `4` that is prime (namely `F₁ = 5`). -/
theorem exists_prime_fermatNumber_gt_four :
    ∃ n, 4 < Nat.fermatNumber n ∧ (Nat.fermatNumber n).Prime :=
  ⟨1, by norm_num, by norm_num⟩

end Brockian.FermatNumbers

