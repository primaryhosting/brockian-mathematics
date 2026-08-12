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
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- **Bézout's identity** for the integers: for all `a b : ℤ` there exist `x y : ℤ`
with `a * x + b * y = Int.gcd a b`.

The witnesses are the extended Euclidean algorithm coefficients `Int.gcdA` / `Int.gcdB`,
and the identity is Mathlib's `Int.gcd_eq_gcd_ab`. -/
theorem bezout (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) :=
  ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩

/-! ### A self-contained proof

The statement above is closed by a single Mathlib lemma. For completeness we also give a
proof from first principles, by the Euclidean-algorithm induction `Nat.gcd.induction`,
which does not use `Int.gcd_eq_gcd_ab`. -/

/-- Bézout's identity for natural numbers (with integer coefficients), proved directly by
induction along the Euclidean algorithm. -/
theorem nat_bezout (m n : ℕ) :
    ∃ x y : ℤ, (m : ℤ) * x + (n : ℤ) * y = (Nat.gcd m n : ℤ) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
      obtain ⟨x, y, hxy⟩ := ih
      refine ⟨y - (n / m : ℕ) * x, x, ?_⟩
      rw [Nat.gcd_rec]
      have hmod : ((n % m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) * ((n / m : ℕ) : ℤ) := by
        have h := Nat.mod_add_div n m
        have h' : ((n % m : ℕ) : ℤ) + (m : ℤ) * ((n / m : ℕ) : ℤ) = (n : ℤ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
        linarith
      rw [hmod] at hxy
      linarith

/-- Bézout's identity for the integers, deduced from `nat_bezout` by adjusting signs;
this is an independent proof of `NumberTheory.bezout`. -/
theorem bezout_of_nat_bezout (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) := by
  obtain ⟨x, y, hxy⟩ := nat_bezout a.natAbs b.natAbs
  have hg : ((Int.gcd a b : ℕ) : ℤ) = ((Nat.gcd a.natAbs b.natAbs : ℕ) : ℤ) := rfl
  have ha : ((a.natAbs : ℕ) : ℤ) = a ∨ ((a.natAbs : ℕ) : ℤ) = -a := by
    rcases Int.natAbs_eq a with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  have hb : ((b.natAbs : ℕ) : ℤ) = b ∨ ((b.natAbs : ℕ) : ℤ) = -b := by
    rcases Int.natAbs_eq b with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ⟨x, y, by rw [hg, ← hxy, ha, hb]⟩
  · exact ⟨x, -y, by rw [hg, ← hxy, ha, hb]; ring⟩
  · exact ⟨-x, y, by rw [hg, ← hxy, ha, hb]; ring⟩
  · exact ⟨-x, -y, by rw [hg, ← hxy, ha, hb]; ring⟩

end NumberTheory

