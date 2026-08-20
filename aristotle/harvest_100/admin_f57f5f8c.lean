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
import Brockian.SierpinskiCovering

/-!
# Sierpiński numbers: Mathlib-flavoured restatement

`Brockian/SierpinskiCovering.lean` must be import-free (its mandated header comment has to
precede everything, and Lean requires `import` to come first), so it develops the covering
argument using only the core `Nat` API.  Here we restate its conclusions with the usual
Mathlib vocabulary: `Nat.Prime`, `Odd`, and `Set.Infinite`.
-/

namespace Brockian.SierpinskiCovering

/-- A composite number is not prime. -/
theorem IsComposite.not_prime {N : ℕ} (h : IsComposite N) : ¬ Nat.Prime N := by
  obtain ⟨d, hd, h1, h2⟩ := h
  intro hp
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- Mathlib form: a Sierpiński number is odd, positive, and `k * 2 ^ n + 1` is never prime. -/
theorem isSierpinskiNumber_iff (k : ℕ) :
    IsSierpinskiNumber k ↔
      Odd k ∧ 0 < k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n + 1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Nat.odd_iff.mpr h1, h2, fun n hn => (h3 n hn).not_prime⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Nat.odd_iff.mp h1, h2, fun n hn => ?_⟩
    have hN : 2 ≤ k * 2 ^ n + 1 := by
      have : 1 * 2 ^ 1 ≤ k * 2 ^ n :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hn)
      omega
    obtain ⟨d, hd, hdvd⟩ := Nat.exists_prime_and_dvd (n := k * 2 ^ n + 1) (by omega)
    refine ⟨d, hdvd, hd.one_lt, ?_⟩
    rcases (Nat.le_of_dvd (by omega) hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hd) (h3 n hn)

/-- `78557 * 2 ^ n + 1` is never prime: `78557` is a Sierpiński number. -/
theorem not_prime_78557 (n : ℕ) (hn : 1 ≤ n) : ¬ Nat.Prime (78557 * 2 ^ n + 1) :=
  ((isSierpinskiNumber_iff 78557).mp isSierpinskiNumber_78557).2.2 n hn

/-- **Sierpiński's theorem.** The set of Sierpiński numbers is infinite. -/
theorem setOf_isSierpinskiNumber_infinite : {k : ℕ | IsSierpinskiNumber k}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk, hks⟩ := SierpinskiProblem N
  exact absurd (hN hks) (by omega)

end Brockian.SierpinskiCovering

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` line): Lean 4 requires every `import`
command to precede all other syntax, including module doc comments, so the mandated header
above forces the development to rely only on the automatically available `Init` prelude.
A Mathlib-flavoured restatement (with `Nat.Prime`, `Odd` and `Set.Infinite`) is provided in
`Brockian/SierpinskiMathlib.lean`, which imports this module.
-/

namespace Brockian.SierpinskiCovering

/-- `IsComposite N` means `N` has a nontrivial divisor; in particular `N` is not prime. -/
def IsComposite (N : Nat) : Prop := ∃ d, d ∣ N ∧ 1 < d ∧ d < N

/-- A *Sierpiński number* is an odd positive natural number `k` such that `k * 2 ^ n + 1`
is composite for every `n ≥ 1`. -/
def IsSierpinskiNumber (k : Nat) : Prop :=
  k % 2 = 1 ∧ 0 < k ∧ ∀ n : Nat, 1 ≤ n → IsComposite (k * 2 ^ n + 1)

/-- The product `3 * 5 * 7 * 13 * 19 * 37 * 73` of the primes of the covering set. -/
def coverModulus : Nat := 70050435

/-- The prime of the covering set attached to a residue `r` of `n` modulo `36`. -/
def coverPrime (r : Nat) : Nat :=
  if r % 2 = 0 then 3
  else if r % 4 = 1 then 5
  else if r % 12 = 7 then 7
  else if r % 12 = 11 then 13
  else if r % 36 = 15 then 19
  else if r % 36 = 27 then 37
  else 73

/-- The four facts needed about `coverPrime r`: it divides `78557 * 2 ^ r + 1`, it satisfies
`2 ^ 36 ≡ 1`, it lies in `[2, 73]`, and it divides the cover modulus. -/
def coverCheck (r : Nat) : Bool :=
  (78557 * 2 ^ r + 1) % coverPrime r == 0 &&
    2 ^ 36 % coverPrime r == 1 % coverPrime r &&
    (2 ≤ coverPrime r) && (coverPrime r ≤ 73) &&
    coverModulus % coverPrime r == 0

/-- The covering set `{3, 5, 7, 13, 19, 37, 73}` really covers all residues modulo `36`. -/
theorem coverCheck_lt_36 : ∀ r, r < 36 → coverCheck r = true := by decide

theorem coverCheck_mod (n : Nat) : coverCheck (n % 36) = true :=
  coverCheck_lt_36 _ (Nat.mod_lt _ (by decide))

/-- Congruences multiply and add: a small modular-arithmetic helper. -/
theorem mul_add_one_mod {p a b c d : Nat} (h1 : a % p = b % p) (h2 : c % p = d % p) :
    (a * c + 1) % p = (b * d + 1) % p := by
  rw [Nat.add_mod, Nat.mul_mod, h1, h2, ← Nat.mul_mod, ← Nat.add_mod]

/-- If `2 ^ 36 ≡ 1 [MOD p]` then `2 ^ n ≡ 2 ^ (n % 36) [MOD p]`. -/
theorem pow_two_mod_of_order {p n : Nat} (h : 2 ^ 36 % p = 1 % p) :
    2 ^ n % p = 2 ^ (n % 36) % p := by
  have hsplit : n = 36 * (n / 36) + n % 36 := by omega
  calc 2 ^ n % p
      = ((2 ^ 36) ^ (n / 36) * 2 ^ (n % 36)) % p := by
        rw [← Nat.pow_mul, ← Nat.pow_add, ← hsplit]
    _ = (((2 ^ 36) ^ (n / 36)) % p * (2 ^ (n % 36) % p)) % p := by rw [Nat.mul_mod]
    _ = ((1 ^ (n / 36)) % p * (2 ^ (n % 36) % p)) % p := by
        rw [Nat.pow_mod, h, ← Nat.pow_mod]
    _ = 2 ^ (n % 36) % p := by rw [Nat.one_pow, ← Nat.mul_mod, Nat.one_mul]

/-- **The covering argument.** For every `k` congruent to `78557` modulo `70050435` and every
`n`, the number `k * 2 ^ n + 1` is divisible by the covering prime attached to `n % 36`. -/
theorem coverPrime_dvd {k : Nat} (hk : k % coverModulus = 78557 % coverModulus) (n : Nat) :
    (k * 2 ^ n + 1) % coverPrime (n % 36) = 0 := by
  have hc := coverCheck_mod n
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hdvd, hord⟩, _⟩, _⟩, hmod⟩ := hc
  have hkp : k % coverPrime (n % 36) = 78557 % coverPrime (n % 36) := by
    have hd : coverPrime (n % 36) ∣ coverModulus := Nat.dvd_of_mod_eq_zero hmod
    rw [← Nat.mod_mod_of_dvd k hd, hk, Nat.mod_mod_of_dvd _ hd]
  have h2 : 2 ^ n % coverPrime (n % 36) = 2 ^ (n % 36) % coverPrime (n % 36) :=
    pow_two_mod_of_order hord
  rw [mul_add_one_mod hkp h2, hdvd]

/-- Every odd `k > 73` congruent to `78557` modulo `70050435` is a Sierpiński number. -/
theorem isSierpinskiNumber_of_mod {k : Nat} (hodd : k % 2 = 1) (hbig : 73 < k)
    (hk : k % coverModulus = 78557 % coverModulus) : IsSierpinskiNumber k := by
  refine ⟨hodd, by omega, ?_⟩
  intro n hn
  have hc := coverCheck_mod n
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, _⟩, hp2⟩, hp73⟩, _⟩ := hc
  refine ⟨coverPrime (n % 36), Nat.dvd_of_mod_eq_zero (coverPrime_dvd hk n), by omega, ?_⟩
  have h1 : k * 2 ^ 1 ≤ k * 2 ^ n :=
    Nat.mul_le_mul_left k (Nat.pow_le_pow_right (by decide) hn)
  simp only [Nat.pow_one] at h1
  omega

/-- `78557` is a Sierpiński number. -/
theorem isSierpinskiNumber_78557 : IsSierpinskiNumber 78557 :=
  isSierpinskiNumber_of_mod (by decide) (by decide) rfl

/-- **Sierpiński's theorem (Sierpiński problem, covering-set solution).** There are
infinitely many Sierpiński numbers: for every bound `N` there is an odd `k > N` with
`k * 2 ^ n + 1` composite for all `n ≥ 1`. -/
theorem SierpinskiProblem : ∀ N : Nat, ∃ k : Nat, N < k ∧ IsSierpinskiNumber k := by
  intro N
  refine ⟨78557 + coverModulus * (2 * (N + 1)), ?_, ?_⟩
  · have : coverModulus * (2 * (N + 1)) ≥ N := by
      have h := Nat.mul_le_mul_left coverModulus (Nat.le_add_right N 1)
      have h2 : coverModulus * (N + 1) ≤ coverModulus * (2 * (N + 1)) :=
        Nat.mul_le_mul_left coverModulus (by omega)
      have h3 : N ≤ coverModulus * N := Nat.le_mul_of_pos_left N (by decide)
      simp only [coverModulus] at *
      omega
    omega
  · refine isSierpinskiNumber_of_mod ?_ ?_ ?_
    · simp only [coverModulus]
      omega
    · simp only [coverModulus]
      omega
    · rw [Nat.mul_comm, Nat.add_mul_mod_self_right]

end Brockian.SierpinskiCovering

