import Mathlib

/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace RequestProject

universe u

/-- Casting natural numbers into the ordinals is additive:
`((m + n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) + (n : Ordinal.{u})`. -/
theorem Ordinal.natCast_add (m n : ℕ) :
    ((m + n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) + (n : Ordinal.{u}) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : ((m + (k + 1) : ℕ) : Ordinal.{u}) = ((m + k : ℕ) : Ordinal.{u}) + 1 := by
        rw [← Nat.add_assoc]
        exact_mod_cast Nat.cast_succ (R := Ordinal.{u}) (m + k)
      have h2 : ((k + 1 : ℕ) : Ordinal.{u}) = (k : Ordinal.{u}) + 1 :=
        Nat.cast_succ (R := Ordinal.{u}) k
      rw [h1, ih, h2, add_assoc]

/-- Casting natural numbers into the ordinals is multiplicative:
`((m * n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) * (n : Ordinal.{u})`. -/
theorem Ordinal.natCast_mul (m n : ℕ) :
    ((m * n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) * (n : Ordinal.{u}) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : ((m * (k + 1) : ℕ) : Ordinal.{u}) = ((m * k : ℕ) : Ordinal.{u}) + (m : Ordinal.{u}) := by
        rw [Nat.mul_succ]
        exact Ordinal.natCast_add (m * k) m
      have h2 : ((k + 1 : ℕ) : Ordinal.{u}) = (k : Ordinal.{u}) + 1 :=
        Nat.cast_succ (R := Ordinal.{u}) k
      rw [h1, ih, h2, mul_add, mul_one]

end RequestProject

-- Axiom check
#print axioms RequestProject.Ordinal.natCast_add
#print axioms RequestProject.Ordinal.natCast_mul

