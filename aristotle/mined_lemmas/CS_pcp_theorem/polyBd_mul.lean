import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
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

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem polyBd_mul {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) :
    PolyBd (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, fun n => ?_⟩
  calc f n * g n ≤ (n + 2) ^ a * (n + 2) ^ b := Nat.mul_le_mul (ha n) (hb n)
    _ = (n + 2) ^ (a + b) := (pow_add _ _ _).symm

/-! ## Boolean circuits -/

/-- Boolean circuits with `n` input variables, built from constants, variables,
negation, conjunction and disjunction. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

namespace Circuit

/-- Value of a circuit on a given assignment of its input variables. -/
