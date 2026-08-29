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

theorem primeBWith_sound {n s : Nat} (h : primeBWith n s = true) : IsPrimeNat n := by
  simp only [primeBWith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h2, hs⟩, hnd⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases h1 : m = 1
  · exact Or.inl h1
  · right
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hm) (by omega)
    have hmn : m ≤ n := Nat.le_of_dvd (by omega) hm
    rcases Nat.lt_or_ge m n with h3 | h3
    · exfalso
      obtain ⟨t, ht⟩ := hm
      have ht0 : 2 ≤ t := by
        match t with
        | 0 => rw [Nat.mul_zero] at ht; omega
        | 1 => rw [Nat.mul_one] at ht; omega
        | (k + 2) => omega
      rcases Nat.lt_or_ge m s with hms | hms
      · exact noDivBelow_sound n s hnd m (by omega) hms (by omega)
          (Nat.dvd_iff_mod_eq_zero.mp ⟨t, ht⟩)
      · have hts : t < s := by
          rcases Nat.lt_or_ge t s with hlt | hge
          · exact hlt
          · exact absurd (Nat.mul_le_mul hms hge) (by omega)
        have htn : t < n := by
          have h2t : 2 * t ≤ m * t := Nat.mul_le_mul_right t (by omega)
          omega
        exact noDivBelow_sound n s hnd t (by omega) hts htn
          (Nat.dvd_iff_mod_eq_zero.mp ⟨m, by rw [ht, Nat.mul_comm]⟩)
    · omega

/-- `gwWheelCheck s ps n` checks that the `k`-th entry `(p, q)` of `ps` is a pair of
primes with `p + q = n + 2 * k`, using `s` as the trial-division bound. -/
