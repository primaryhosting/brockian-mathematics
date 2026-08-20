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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

universe u v

/-- A deterministic two-party communication protocol tree over inputs `X` (Alice) and `Y` (Bob).
`alice m k` means Alice sends the bit `m x` and the protocol continues with `k (m x)`;
`bob m k` means Bob sends the bit `m y`. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → (Bool → Protocol X Y) → Protocol X Y
  | bob : (Y → Bool) → (Bool → Protocol X Y) → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on a given pair of inputs. -/

lemma trans_mem_paths (P : Protocol X Y) (x : X) (y : Y) : trans P x y ∈ paths P := by
  induction P generalizing x y with
  | leaf b => simp [trans, paths]
  | alice m k ih =>
      cases h : m x <;> simp [trans, paths, h] <;> exact ih _ x y
  | bob m k ih =>
      cases h : m y <;> simp [trans, paths, h] <;> exact ih _ x y

