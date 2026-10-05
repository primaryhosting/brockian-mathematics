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

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- `IsComposite N` means that `N` factors as a product of two factors, each `> 1`. -/
def IsComposite (N : Nat) : Prop := ∃ a b : Nat, 1 < a ∧ 1 < b ∧ N = a * b

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
for every `n ≥ 1`. -/
def IsRieselNumber (k : Nat) : Prop :=
  k % 2 = 1 ∧ ∀ n : Nat, 1 ≤ n → IsComposite (k * 2 ^ n - 1)

/-- The covering set for `k = 509203`: to the residue `r = n % 24` we assign the prime of
`{3, 5, 7, 13, 17, 241}` that divides `509203 * 2 ^ n - 1`. -/
def cov : Nat → Nat
  | 0 => 3
  | 1 => 5
  | 2 => 3
  | 3 => 241
  | 4 => 3
  | 5 => 5
  | 6 => 3
  | 7 => 13
  | 8 => 3
  | 9 => 5
  | 10 => 3
  | 11 => 7
  | 12 => 3
  | 13 => 5
  | 14 => 3
  | 15 => 17
  | 16 => 3
  | 17 => 5
  | 18 => 3
  | 19 => 13
  | 20 => 3
  | 21 => 5
  | 22 => 3
  | _ => 7

/-- The cofactor witnessing `509203 * 2 ^ r ≡ 1 (mod cov r)`. -/
def cofK (r : Nat) : Nat := (509203 * 2 ^ r - 1) / cov r

/-- The cofactor witnessing `2 ^ 24 ≡ 1 (mod cov r)`. -/
def cofP (r : Nat) : Nat := (2 ^ 24 - 1) / cov r

/-- The covering data, checked residue by residue: for each `r < 24` the number `cov r`
lies strictly between `1` and `242`, divides `2 ^ 24 - 1`, and satisfies
`509203 * 2 ^ r ≡ 1 (mod cov r)`. -/
theorem cov_spec : ∀ r, r < 24 →
    1 < cov r ∧ cov r ≤ 241 ∧
      2 ^ 24 = 1 + cov r * cofP r ∧
      509203 * 2 ^ r = 1 + cov r * cofK r := by
  decide

/-- If `p` divides `2 ^ 24 - 1` (in the form `2 ^ 24 = 1 + p * t`), then `p` divides
`2 ^ (24 * q) - 1` for every `q`. -/
theorem pow24_mul (p t : Nat) (ht : 2 ^ 24 = 1 + p * t) :
    ∀ q : Nat, ∃ s : Nat, 2 ^ (24 * q) = 1 + p * s := by
  intro q
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨s + t + p * s * t, ?_⟩
      have h1 : 24 * (q + 1) = 24 * q + 24 := by omega
      rw [h1, Nat.pow_add, hs, ht]
      grind

/-- The heart of the covering argument: for every `n`, the number `509203 * 2 ^ n - 1`
is divisible by `cov (n % 24)`, with an explicit cofactor. -/
theorem exists_factor (n : Nat) :
    ∃ m : Nat, 509203 * 2 ^ n = 1 + cov (n % 24) * m := by
  obtain ⟨h1, h2, hP, hK⟩ := cov_spec (n % 24) (Nat.mod_lt _ (by omega))
  obtain ⟨s, hs⟩ := pow24_mul (cov (n % 24)) (cofP (n % 24)) hP (n / 24)
  refine ⟨cofK (n % 24) + s + cov (n % 24) * cofK (n % 24) * s, ?_⟩
  have hn : n = 24 * (n / 24) + n % 24 := (Nat.div_add_mod n 24).symm
  have hpow : (2 : Nat) ^ n = 2 ^ (24 * (n / 24)) * 2 ^ (n % 24) := by
    rw [← Nat.pow_add, ← hn]
  rw [hpow]
  have e1 : 509203 * (2 ^ (24 * (n / 24)) * 2 ^ (n % 24))
      = (509203 * 2 ^ (n % 24)) * 2 ^ (24 * (n / 24)) := by
    rw [Nat.mul_comm (2 ^ (24 * (n / 24))) (2 ^ (n % 24)), ← Nat.mul_assoc]
  rw [e1, hK, hs]
  grind

/-- **Riesel's theorem** (1956): `509203` is a Riesel number, i.e. `509203 * 2 ^ n - 1`
is composite for every `n ≥ 1`.  The proof is the classical covering-congruence argument
using the covering set `{3, 5, 7, 13, 17, 241}` of divisors of `2 ^ 24 - 1`,
whose multiplicative orders `2, 4, 3, 12, 8, 24` for the base `2` cover all residues
modulo `24`. -/
theorem isRieselNumber_509203 : IsRieselNumber 509203 := by
  refine ⟨by decide, ?_⟩
  intro n hn
  obtain ⟨h1, h2, _, _⟩ := cov_spec (n % 24) (Nat.mod_lt _ (by omega))
  obtain ⟨m, hm⟩ := exists_factor n
  -- `509203 * 2 ^ n` is huge, hence the cofactor `m` cannot be `0` or `1`
  have hbig : 1018406 ≤ 509203 * 2 ^ n := by
    have : (2 : Nat) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have := Nat.mul_le_mul_left 509203 this
    omega
  have hm1 : 1 < m := by
    have hm2 : m = 0 ∨ m = 1 ∨ 1 < m := by omega
    cases hm2 with
    | inl h => subst h; omega
    | inr h =>
      cases h with
      | inl h => subst h; omega
      | inr h => exact h
  refine ⟨cov (n % 24), m, h1, hm1, ?_⟩
  omega

/-- **The Riesel problem** (positive part): there exists a Riesel number, i.e. an odd
`k > 1` such that `k * 2 ^ n - 1` is composite for every `n ≥ 1`.  A witness is
`k = 509203`, Riesel's original example. -/
theorem RieselProblem : ∃ k : Nat, 1 < k ∧ IsRieselNumber k :=
  ⟨509203, by omega, isRieselNumber_509203⟩

end RieselCovering
end Brockian

