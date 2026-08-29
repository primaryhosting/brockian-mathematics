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

theorem dioph_ex_vec {β : Type} {P : (β → ℕ) → (α → ℕ) → Prop}
    (h : Dioph {w : α ⊕ β → ℕ | P (w ∘ Sum.inr) (w ∘ Sum.inl)}) :
    Dioph {v : α → ℕ | ∃ x : β → ℕ, P x v} := by
  refine Dioph.ext (Dioph.ex_dioph h) fun v => ?_
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Function.comp_def] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Function.comp_def] using hx⟩

/-! ### Logical connectives -/

