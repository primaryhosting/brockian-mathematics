/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module doc comment, and Lean 4 forbids any
`import` after it, so this file is written in pure core Lean (no Mathlib) and is fully
self-contained.  The file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports Mathlib and
this file, proves `Brockian.IsPrimeNat n ↔ Nat.Prime n`, and restates the result in Mathlib
vocabulary.
-/

namespace Brockian

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/

theorem isPrimeNat_of_no_divisor_le_sqrt {n : Nat} (h2 : 2 ≤ n)
    (H : ∀ m : Nat, 2 ≤ m → m * m ≤ n → ¬ m ∣ n) : IsPrimeNat n := by
  refine ⟨h2, ?_⟩
  intro m hm
  cases hm with
  | intro k hk =>
    have hm0 : m ≠ 0 := by
      intro h; subst h; simp at hk; omega
    have hk0 : k ≠ 0 := by
      intro h; subst h; simp at hk; omega
    rcases Nat.lt_or_ge m 2 with hlt | hm2
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge k 2 with hklt | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        exact Or.inr (by omega)
      · exfalso
        rcases Nat.le_total m k with h | h
        · exact H m hm2 (by
            calc m * m ≤ m * k := Nat.mul_le_mul_left m h
              _ = n := hk.symm) ⟨k, hk⟩
        · exact H k hk2 (by
            calc k * k ≤ m * k := Nat.mul_le_mul_right k h
              _ = n := hk.symm) ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The wheel modulus `1153` is prime. -/
