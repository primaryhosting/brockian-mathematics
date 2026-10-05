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
/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in a plain block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 4000000

namespace Brockian.SierpinskiCovering

/-- `k` is a *Sierpiński number*: an odd positive integer `k` such that `k * 2 ^ n + 1`
is composite for every `n ≥ 1`. -/
def IsSierpinskiNumber (k : ℕ) : Prop :=
  0 < k ∧ Odd k ∧ ∀ n : ℕ, 0 < n → ¬ Nat.Prime (k * 2 ^ n + 1)

/-- The covering set data: for a residue `r` of `n` modulo `36`, `coverList[r]` is a prime
of the covering set `{3, 5, 7, 13, 19, 37, 73}` dividing `78557 * 2 ^ n + 1`. -/
def coverList : List ℕ :=
  [3, 5, 3, 73, 3, 5, 3, 7, 3, 5, 3, 13, 3, 5, 3, 19, 3, 5, 3, 7,
   3, 5, 3, 13, 3, 5, 3, 37, 3, 5, 3, 7, 3, 5, 3, 13]

/-- The prime of the covering set assigned to the exponent `n`. -/
def cover (n : ℕ) : ℕ := coverList.getD (n % 36) 1

/-- The finite verification underlying the covering argument: for each residue `r < 36`,
the assigned modulus `p` satisfies `1 < p ≤ 73`, `p ∣ 78557 * 2 ^ r + 1`, and
`2 ^ 36 ≡ 1 [MOD p]`. -/
lemma cover_spec : ∀ r < 36,
    1 < coverList.getD r 1 ∧ coverList.getD r 1 ≤ 73 ∧
      (78557 * 2 ^ r + 1) % coverList.getD r 1 = 0 ∧
      2 ^ 36 % coverList.getD r 1 = 1 := by
  decide

lemma one_lt_cover (n : ℕ) : 1 < cover n :=
  (cover_spec (n % 36) (Nat.mod_lt _ (by norm_num))).1

lemma cover_le (n : ℕ) : cover n ≤ 73 :=
  (cover_spec (n % 36) (Nat.mod_lt _ (by norm_num))).2.1

/-- The covering property: every number of the form `78557 * 2 ^ n + 1` is divisible by one
of the primes `3, 5, 7, 13, 19, 37, 73`. -/
theorem cover_dvd (n : ℕ) : cover n ∣ 78557 * 2 ^ n + 1 := by
  obtain ⟨hlt, -, hdvd, hper⟩ := cover_spec (n % 36) (Nat.mod_lt _ (by norm_num))
  set p := coverList.getD (n % 36) 1 with hpdef
  have hcov : cover n = p := rfl
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hlt
  have h2 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [hper, hone]
  have h3 : ((2 : ℕ) ^ 36) ^ (n / 36) ≡ 1 [MOD p] := by
    simpa using h2.pow (n / 36)
  have hsplit : (2 : ℕ) ^ n = ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h4 : (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD p] := by
    rw [hsplit]
    simpa using h3.mul_right ((2 : ℕ) ^ (n % 36))
  have h5 : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD p] :=
    (h4.mul_left 78557).add_right 1
  have h6 : 78557 * 2 ^ (n % 36) + 1 ≡ 0 [MOD p] := by
    unfold Nat.ModEq
    simpa using hdvd
  rw [hcov]
  exact Nat.modEq_zero_iff_dvd.1 (h5.trans h6)

/-- **The Sierpiński covering theorem.** `78557` is a Sierpiński number: `78557 * 2 ^ n + 1`
is composite for every `n ≥ 1`, because it is always divisible by one of the primes of the
covering set `{3, 5, 7, 13, 19, 37, 73}`.

(That `78557` is the *smallest* Sierpiński number is the still-open Sierpiński problem;
what is proved here is the covering half of it.) -/
theorem SierpinskiProblem : IsSierpinskiNumber 78557 := by
  refine ⟨by norm_num, ⟨39278, by norm_num⟩, ?_⟩
  intro n _ hprime
  have hdvd := cover_dvd n
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h (Nat.ne_of_gt (one_lt_cover n))
  · have h1 : cover n ≤ 73 := cover_le n
    have h2 : (78557 : ℕ) * 2 ^ n + 1 ≤ 73 := h ▸ h1
    have h3 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    nlinarith

end Brockian.SierpinskiCovering

