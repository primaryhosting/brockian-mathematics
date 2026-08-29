/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained and uses no imports, so that the header
comment above can be the very first thing in the file: Lean requires `import`
commands to precede every other command, including module documentation.
Consequently primality is developed from scratch here, as `Brockian.IsPrimeNat`.
The companion file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports
Mathlib, proves `IsPrimeNat n ↔ Nat.Prime n`, and restates the main result in
Mathlib's vocabulary.
-/

namespace Brockian

/-- `IsPrimeNat n` is the usual definition of primality for natural numbers:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem gwWheelCheck_sound :
    ∀ (s : Nat) (ps : List (Nat × Nat)) (n : Nat), gwWheelCheck s ps n = true →
      ∀ m, m < ps.length → ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n + 2 * m := by
  intro s ps
  induction ps with
  | nil => intro n _ m hm; simp at hm
  | cons a ps ih =>
    obtain ⟨p, q⟩ := a
    intro n h m hm
    simp only [gwWheelCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hpq, hp⟩, hq⟩, hrest⟩ := h
    cases m with
    | zero => exact ⟨p, q, primeBWith_sound hp, primeBWith_sound hq, by omega⟩
    | succ m =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hm
      obtain ⟨p', q', hp', hq', hsum⟩ := ih (n + 2) hrest m hm
      exact ⟨p', q', hp', hq', by omega⟩

/-- The explicit "wheel" of Goldbach witnesses: the `k`-th entry is a pair of primes
summing to `4 + 2 * k`, for `k = 0, ..., 574`, thus covering every even number from
`4` up to `1152`. -/
