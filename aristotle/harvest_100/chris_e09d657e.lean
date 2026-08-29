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

/-- Bézout's identity for natural numbers, proved by the Euclidean-algorithm recursion:
for all `m n : ℕ` there are integers `x y` with `m * x + n * y = gcd m n`. -/
theorem nat_bezout (m n : Nat) : ∃ x y : Int, (m : Int) * x + (n : Int) * y = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _ ih =>
      obtain ⟨x, y, hxy⟩ := ih
      have h : ((n % m : Nat) : Int) + (m : Int) * ((n / m : Nat) : Int) = (n : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, Nat.mod_add_div]
      refine ⟨y - ((n / m : Nat) : Int) * x, x, ?_⟩
      rw [Nat.gcd_rec]
      grind

/-- **Bézout's identity**: for integers `a` and `b` there exist integers `x` and `y` such that
`a * x + b * y = Int.gcd a b`. -/
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) := by
  obtain ⟨x, y, hxy⟩ := nat_bezout a.natAbs b.natAbs
  show ∃ x y : Int, a * x + b * y = ((Nat.gcd a.natAbs b.natAbs : Nat) : Int)
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb | hb
  · exact ⟨x, y, by grind⟩
  · exact ⟨x, -y, by grind⟩
  · exact ⟨-x, y, by grind⟩
  · exact ⟨-x, -y, by grind⟩

end NumberTheory

