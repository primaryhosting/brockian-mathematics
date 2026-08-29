import Mathlib

/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The partial function computed by the program with (Gödel) index `n`. -/

theorem phi_surjective {g : ℕ →. ℕ} (hg : Nat.Partrec g) : ∃ n : ℕ, phi n = g := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hg
  exact ⟨Encodable.encode c, by simp [phi, hc]⟩

/-- Each index denotes a partial recursive function. -/
