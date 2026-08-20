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

/-- Bézout's identity for natural numbers, proved by the Euclidean recursion:
for all `m n : ℕ` there are integers `x y` with `m * x + n * y = Nat.gcd m n`. -/

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) := by
  obtain ⟨x, y, hxy⟩ := bezout_nat a.natAbs b.natAbs
  have hg : (Int.gcd a b : Int) = (Nat.gcd a.natAbs b.natAbs : Int) := rfl
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb | hb
  · exact ⟨x, y, by rw [hg, ← hxy, ← ha, ← hb]⟩
  · refine ⟨x, -y, ?_⟩
    have hb' : ((b.natAbs : Int)) = -b := by omega
    rw [hg, ← hxy, ← ha, hb']; grind
  · refine ⟨-x, y, ?_⟩
    have ha' : ((a.natAbs : Int)) = -a := by omega
    rw [hg, ← hxy, ha', ← hb]; grind
  · refine ⟨-x, -y, ?_⟩
    have ha' : ((a.natAbs : Int)) = -a := by omega
    have hb' : ((b.natAbs : Int)) = -b := by omega
    rw [hg, ← hxy, ha', hb']; grind

end NumberTheory

