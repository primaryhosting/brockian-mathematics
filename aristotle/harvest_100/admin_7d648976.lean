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
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Rewriting the natural-number remainder as an integer linear expression. -/
private theorem cast_mod_eq (m n : Nat) :
    ((n % m : Nat) : Int) = (n : Int) - (m : Int) * ((n / m : Nat) : Int) := by
  have h := Nat.div_add_mod n m
  omega

/-- Bézout's identity for natural numbers, proved by the Euclidean recursion. -/
theorem bezout_nat (m n : Nat) :
    ∃ x y : Int, (m : Int) * x + (n : Int) * y = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _hm ih =>
      obtain ⟨x, y, h⟩ := ih
      refine ⟨y - ((n / m : Nat) : Int) * x, x, ?_⟩
      rw [Nat.gcd_rec]
      rw [cast_mod_eq] at h
      grind

/-- **Bézout's identity**: for integers `a` and `b` there exist integers `x` and `y`
with `a * x + b * y = Int.gcd a b`. -/
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) := by
  obtain ⟨x, y, h⟩ := bezout_nat a.natAbs b.natAbs
  obtain ⟨u, hu⟩ : ∃ u : Int, (a.natAbs : Int) * x = a * u := by
    rcases Int.natAbs_eq a with ha | ha
    · exact ⟨x, by rw [← ha]⟩
    · exact ⟨-x, by rw [ha]; grind⟩
  obtain ⟨v, hv⟩ : ∃ v : Int, (b.natAbs : Int) * y = b * v := by
    rcases Int.natAbs_eq b with hb | hb
    · exact ⟨y, by rw [← hb]⟩
    · exact ⟨-y, by rw [hb]; grind⟩
  exact ⟨u, v, by rw [← hu, ← hv]; exact h⟩

end NumberTheory

import Mathlib
import RequestProject.NumberTheory.Bezout

/-!
# Bezout (Mathlib cross-check)

A second, Mathlib-based proof of Bézout's identity over the integers, using
`Int.gcd_eq_gcd_ab`, together with a check that it agrees with the self-contained
statement `NumberTheory.bezout` proved in `RequestProject/NumberTheory/Bezout.lean`.
-/

namespace NumberTheory

/-- **Bézout's identity** via Mathlib's extended Euclidean coefficients
`Int.gcdA` / `Int.gcdB`. -/
theorem bezout_mathlib (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) :=
  ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩

example : ∀ a b : ℤ, ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) := NumberTheory.bezout

end NumberTheory

