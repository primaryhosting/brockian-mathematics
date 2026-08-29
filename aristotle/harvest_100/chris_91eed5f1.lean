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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace SierpinskiCovering

/-- `k` is a *Sierpiński number* if it is odd and `k * 2 ^ n + 1` is composite
(here: not prime) for every `n ≥ 1`. -/
def IsSierpinski (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n + 1)

/-- The classical covering set for `78557`. -/
def cover : List ℕ := [3, 5, 7, 13, 19, 37, 73]

lemma cover_prime : ∀ p ∈ cover, Nat.Prime p := by decide

/-- Every element of the covering set has multiplicative order dividing `36` modulo itself,
i.e. it divides `2 ^ 36 - 1`. -/
lemma cover_dvd_two_pow_36_sub_one : ∀ p ∈ cover, p ∣ 2 ^ 36 - 1 := by decide

/-- The covering property: for each residue `r` of the exponent modulo `36`, some prime of the
covering set divides `78557 * 2 ^ r + 1`. -/
lemma cover_residue : ∀ r < 36, ∃ p ∈ cover, p ∣ 78557 * 2 ^ r + 1 := by decide

lemma cover_le : ∀ p ∈ cover, p ≤ 73 := by decide

/-- Key step: for every exponent `n`, some prime of the covering set divides `78557 * 2 ^ n + 1`. -/
theorem exists_cover_dvd (n : ℕ) : ∃ p ∈ cover, p ∣ 78557 * 2 ^ n + 1 := by
  obtain ⟨p, hp, hpd⟩ := cover_residue (n % 36) (Nat.mod_lt _ (by norm_num))
  refine ⟨p, hp, ?_⟩
  -- `2 ^ 36 ≡ 1 [MOD p]`
  have h1 : (1 : ℕ) ≡ 2 ^ 36 [MOD p] :=
    (Nat.modEq_iff_dvd' (by norm_num)).mpr (cover_dvd_two_pow_36_sub_one p hp)
  have h2 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] := h1.symm
  have h3 : ((2 : ℕ) ^ 36) ^ (n / 36) ≡ 1 [MOD p] := by
    simpa using h2.pow (n / 36)
  have hsplit : (2 : ℕ) ^ n = ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have h4 : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD p] := by
    rw [hsplit]
    exact ((h3.mul_right _).mul_left 78557).add_right 1
  have h5 : 78557 * 2 ^ (n % 36) + 1 ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpd
  exact (Nat.modEq_zero_iff_dvd).mp (h4.trans h5)

/-- **Sierpiński problem (covering set part).**  `78557` is a Sierpiński number: it is odd and
`78557 * 2 ^ n + 1` is never prime for `n ≥ 1`.  (That `78557` is the *smallest* such number is
still open; see `sierpinski_least_iff` for the reduction of that statement.) -/
theorem SierpinskiProblem : IsSierpinski 78557 := by
  constructor
  · decide
  · intro n hn hprime
    obtain ⟨p, hp, hpd⟩ := exists_cover_dvd n
    have hpe : p = 78557 * 2 ^ n + 1 :=
      ((Nat.Prime.eq_one_or_self_of_dvd hprime p hpd).resolve_left
        (cover_prime p hp).ne_one)
    have hlarge : 78557 * 2 ^ 1 + 1 ≤ 78557 * 2 ^ n + 1 := by
      have : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have := cover_le p hp
    omega

/-- Reduction of the (open) Sierpiński problem — that `78557` is the least Sierpiński number — to
the statement that no smaller natural number is a Sierpiński number.  The nontrivial half,
membership of `78557`, is supplied by `SierpinskiProblem`. -/
theorem sierpinski_least_iff :
    IsLeast {k : ℕ | IsSierpinski k} 78557 ↔ ∀ k < 78557, ¬ IsSierpinski k := by
  constructor
  · rintro ⟨-, hlb⟩ k hk hks
    exact absurd (hlb hks) (by omega)
  · intro h
    refine ⟨SierpinskiProblem, ?_⟩
    intro k hk
    by_contra hlt
    exact h k (by omega) hk

end SierpinskiCovering
end Brockian

