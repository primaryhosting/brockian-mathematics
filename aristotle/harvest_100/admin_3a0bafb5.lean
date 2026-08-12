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

/-- Bézout's identity at the level of natural-number arguments: for all `m n : Nat` there are
integers `x`, `y` with `m * x + n * y = Nat.gcd m n`. -/
theorem bezout_nat :
    ∀ m n : Nat, ∃ x y : Int, (m : Int) * x + (n : Int) * y = (Nat.gcd m n : Int) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n
    match m, ih with
    | 0, _ => exact ⟨0, 1, by simp⟩
    | (m + 1), ih =>
      obtain ⟨x, y, hxy⟩ := ih (n % (m + 1)) (Nat.mod_lt _ (Nat.succ_pos m)) (m + 1)
      refine ⟨y - ((n / (m + 1) : Nat) : Int) * x, x, ?_⟩
      have hmod : (n % (m + 1)) + (m + 1) * (n / (m + 1)) = n := Nat.mod_add_div n (m + 1)
      have hc : ((n % (m + 1) : Nat) : Int)
          + ((m + 1 : Nat) : Int) * ((n / (m + 1) : Nat) : Int) = (n : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, hmod]
      have hg : Nat.gcd (m + 1) n = Nat.gcd (n % (m + 1)) (m + 1) := Nat.gcd_rec (m + 1) n
      rw [hg, ← hxy, ← hc]
      generalize ((n % (m + 1) : Nat) : Int) = r
      generalize ((n / (m + 1) : Nat) : Int) = q
      generalize ((m + 1 : Nat) : Int) = M
      rw [Int.mul_sub, Int.add_mul, ← Int.mul_assoc]
      omega

/-- **Bézout's identity** for the integers: for any integers `a` and `b` there exist
integers `x` and `y` with `a * x + b * y = Int.gcd a b`. -/
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) := by
  obtain ⟨x, y, hxy⟩ := bezout_nat a.natAbs b.natAbs
  refine ⟨(if 0 ≤ a then x else -x), (if 0 ≤ b then y else -y), ?_⟩
  have ha : (a.natAbs : Int) * x = a * (if 0 ≤ a then x else -x) := by
    by_cases h : 0 ≤ a
    · rw [if_pos h, Int.natAbs_of_nonneg h]
    · have hna : (a.natAbs : Int) = -a := by omega
      rw [hna, if_neg h, Int.neg_mul, Int.mul_neg]
  have hb : (b.natAbs : Int) * y = b * (if 0 ≤ b then y else -y) := by
    by_cases h : 0 ≤ b
    · rw [if_pos h, Int.natAbs_of_nonneg h]
    · have hnb : (b.natAbs : Int) = -b := by omega
      rw [hnb, if_neg h, Int.neg_mul, Int.mul_neg]
  rw [← ha, ← hb, hxy]
  rfl

end NumberTheory

