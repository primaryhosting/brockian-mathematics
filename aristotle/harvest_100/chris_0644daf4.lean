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

/-- Bezout's identity for natural numbers: `gcd m n` is an integer linear
combination of `m` and `n`. Proved by the Euclidean-algorithm recursion. -/
theorem natBezout (m n : Nat) :
    ∃ x y : Int, (m : Int) * x + (n : Int) * y = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y - (n / m : Nat) * x, x, ?_⟩
    have hd : (m : Int) * ((n / m : Nat) : Int) + ((n % m : Nat) : Int) = (n : Int) := by
      have := Nat.div_add_mod n m
      omega
    rw [Nat.gcd_rec m n]
    grind

/-- **Bezout's identity**: for integers `a` and `b` there exist integers `x`, `y`
with `a * x + b * y = Int.gcd a b`. -/
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) := by
  obtain ⟨x, y, h⟩ := natBezout a.natAbs b.natAbs
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb | hb
  · exact ⟨x, y, by rw [Int.gcd]; grind⟩
  · exact ⟨x, -y, by rw [Int.gcd]; grind⟩
  · exact ⟨-x, y, by rw [Int.gcd]; grind⟩
  · exact ⟨-x, -y, by rw [Int.gcd]; grind⟩

end NumberTheory

