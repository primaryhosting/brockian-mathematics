import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in a Mathlib-free file (a module
docstring may not precede `import`, so the required header comment forces that file to be
import-free).  Here we identify the primality predicate used there with Mathlib's
`Nat.Prime` and restate the result accordingly.
-/

namespace Brockian

/-- The from-first-principles primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem isPrimeFast_sound {n : Nat} (h : isPrimeFast n = true) : IsPrimeNat n := by
  rw [isPrimeFast, Bool.and_eq_true] at h
  obtain ⟨h2, hnf⟩ := h
  have h2' : 2 ≤ n := Nat.le_of_ble_eq_true h2
  refine ⟨h2', fun d hd => ?_⟩
  obtain ⟨e, he⟩ := hd
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- `d = 0` is impossible since `n ≥ 2`; so `d = 1`.
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · rw [Nat.zero_mul] at he; omega
    · exact Or.inl rfl
  · -- `d ≥ 2`: the trial division rules out `d * d ≤ n`, so `e < d`.
    have hdd : ¬ (d * d ≤ n) := fun hle =>
      noFactorFrom_sound n 2 n d hnf hd2 hle ⟨e, he⟩
    have hdpos : 0 < d := by omega
    have hed : e < d := by
      rcases Nat.lt_or_ge e d with hlt | hge
      · exact hlt
      · exact absurd (Nat.le_trans (Nat.mul_le_mul (Nat.le_refl d) hge)
          (Nat.le_of_eq he.symm)) hdd
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · rw [Nat.mul_zero] at he; omega
      · exact hpos
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · have hE : e = 1 := by omega
      subst hE
      right; omega
    · exact absurd (show e ∣ n from ⟨d, by rw [he]; exact Nat.mul_comm d e⟩)
        (noFactorFrom_sound n 2 n e hnf he2
          (Nat.le_trans (Nat.mul_le_mul (Nat.le_refl e) (Nat.le_of_lt hed))
            (Nat.le_of_eq (by rw [he]; exact Nat.mul_comm e d))))

/-- Search for the least `p ≥ p₀` such that both `p` and `m - p` pass the primality test. -/
