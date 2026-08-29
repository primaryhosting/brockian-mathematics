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
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem IsPoly.subst {f : (γ → ℕ) → ℤ} (hf : IsPoly f) (σ : γ → Option δ) :
    IsPoly (fun w : δ → ℕ => f (fun c => (σ c).elim 0 w)) := by
  induction hf with
  | proj i =>
      cases h : σ i with
      | none => simpa [h] using IsPoly.const (α := δ) 0
      | some d => simpa [h] using IsPoly.proj (α := δ) d
  | const n => exact IsPoly.const n
  | sub _ _ ihf ihg => exact ihf.sub ihg
  | mul _ _ ihf ihg => exact ihf.mul ihg

/-- Every Diophantine set can be defined using only finitely many auxiliary variables. -/
