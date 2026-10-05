import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma singleton_mem_hgtFinsets (x : α) :
    ({x} : Finset α) ∈ (chainFinsets α).filter (fun c => ∀ y ∈ c, y ≤ x) := by
  refine Finset.mem_filter.2 ⟨mem_chainFinsets.2 ?_, ?_⟩
  · simp
  · intro y hy
    simp only [Finset.mem_singleton] at hy
    exact hy.le

