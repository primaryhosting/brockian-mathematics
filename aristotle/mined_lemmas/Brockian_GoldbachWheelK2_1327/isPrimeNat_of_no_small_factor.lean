/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free: Lean 4 does not allow a module docstring
(`/-! ... -/`) to precede the `import` commands, so the required header comment
forces the development to be self-contained in core Lean.  The primality
predicate is therefore spelled out explicitly (`2 ≤ p ∧ every divisor of p is 1
or p`).  The companion file `RequestProject.GoldbachWheelK2_1327Mathlib`
imports Mathlib and restates the result with `Nat.Prime`.
-/

namespace Brockian

/-- `noFacB n k = true` certifies that no `m` with `2 ≤ m ≤ k` and `m * m ≤ n` divides `n`.
Trial divisions are skipped as soon as `m * m > n`, which keeps kernel evaluation cheap. -/

theorem isPrimeNat_of_no_small_factor {n : Nat} (h2 : 2 ≤ n)
    (h : ∀ m, 2 ≤ m → m * m ≤ n → ¬ m ∣ n) : IsPrimeNat n := by
  refine ⟨h2, fun m hmd => ?_⟩
  rcases Decidable.em (m = 1) with hm1 | hm1
  · exact Or.inl hm1
  rcases Decidable.em (m = n) with hmn | hmn
  · exact Or.inr hmn
  exfalso
  have hm0 : m ≠ 0 := by
    intro h0
    subst h0
    exact absurd (Nat.eq_zero_of_zero_dvd hmd) (by omega)
  have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmd
  have hm2 : 2 ≤ m := by omega
  have hmlt : m < n := by omega
  obtain ⟨c, hnc⟩ := id hmd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hnc
    omega
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, Nat.mul_one] at hnc
    omega
  have hc2 : 2 ≤ c := by omega
  have hcd : c ∣ n := ⟨m, by rw [hnc, Nat.mul_comm]⟩
  rcases Nat.lt_or_ge c m with hlt | hge
  · exact h c hc2 (by calc c * c ≤ m * c := Nat.mul_le_mul (Nat.le_of_lt hlt) (Nat.le_refl c)
                    _ = n := hnc.symm) hcd
  · exact h m hm2 (by calc m * m ≤ m * c := Nat.mul_le_mul (Nat.le_refl m) hge
                    _ = n := hnc.symm) hmd

