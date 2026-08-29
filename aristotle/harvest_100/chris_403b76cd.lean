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

/- (Lean requires `import` to be the first command, so this required header is
   given as a plain block comment; it is repeated as a module docstring below.)

# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- Riesel's candidate constant `k = 509203`. -/
def k : ℕ := 509203

/-- The covering set of primes for `k = 509203`. -/
def coveringPrimes : List ℕ := [3, 5, 7, 13, 17, 241]

/-- For each residue `r` of `n` modulo `24`, the prime of the covering set that
divides `509203 * 2 ^ n - 1`. -/
def pick (r : ℕ) : ℕ :=
  [3, 5, 7, 241, 3, 5, 3, 13, 3, 5, 3, 7, 3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7].getD r 3

lemma pick_mem : ∀ r < 24, pick r ∈ coveringPrimes := by decide

lemma pick_period : ∀ r < 24, 2 ^ 24 % pick r = 1 % pick r := by decide

lemma pick_value : ∀ r < 24, (k * 2 ^ r) % pick r = 1 % pick r := by decide

lemma pick_bounds : ∀ r < 24, 3 ≤ pick r ∧ pick r ≤ 241 := by decide

/-- If `2 ^ 24 ≡ 1 [MOD p]`, then powers of two modulo `p` only depend on the
exponent modulo `24`. -/
lemma pow_two_period {p : ℕ} (h : 2 ^ 24 ≡ 1 [MOD p]) (n : ℕ) :
    2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 24]
  rw [pow_add, pow_mul]
  calc ((2 ^ 24) ^ (n / 24) * 2 ^ (n % 24))
      ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] :=
        Nat.ModEq.mul (Nat.ModEq.pow (n / 24) h) (Nat.ModEq.refl _)
    _ = 2 ^ (n % 24) := by rw [one_pow, one_mul]

/-- The covering congruence: for every `n` some prime of the covering set divides
`509203 * 2 ^ n - 1`. -/
theorem exists_covering_prime (n : ℕ) :
    ∃ p ∈ coveringPrimes, p ∣ k * 2 ^ n - 1 ∧ 3 ≤ p ∧ p ≤ 241 := by
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  refine ⟨pick (n % 24), pick_mem _ hr, ?_, pick_bounds _ hr⟩
  have hle : 1 ≤ k * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by simp [k])
  rw [← Nat.modEq_iff_dvd' hle]
  calc (1 : ℕ) ≡ k * 2 ^ (n % 24) [MOD pick (n % 24)] := (pick_value _ hr).symm
    _ ≡ k * 2 ^ n [MOD pick (n % 24)] :=
        Nat.ModEq.mul_left k (pow_two_period (pick_period _ hr) n).symm

/-- **The Riesel problem, covering-set half.** `k = 509203` is a Riesel number:
`509203 * 2 ^ n - 1` is never prime.  (The statement is proved for every `n : ℕ`,
in particular for all `n ≥ 1`.) -/
theorem RieselProblem (n : ℕ) : ¬ Nat.Prime (509203 * 2 ^ n - 1) := by
  intro hN
  obtain ⟨p, -, hdvd, hp3, hp241⟩ := exists_covering_prime n
  have hbig : 509202 ≤ 509203 * 2 ^ n - 1 := by
    have : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have : 509203 ≤ 509203 * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hN p hdvd) with h | h <;> omega

end Brockian.RieselCovering

