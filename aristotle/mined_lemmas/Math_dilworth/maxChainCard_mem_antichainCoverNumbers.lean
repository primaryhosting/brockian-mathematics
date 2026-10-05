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

lemma maxChainCard_mem_antichainCoverNumbers :
    maxChainCard α ∈ antichainCoverNumbers α := by
  refine ⟨fun i => {x : α | hgt x = (i : ℕ) + 1}, ?_, ?_⟩
  · intro i a ha b hb hab hle
    have ha' : hgt a = (i : ℕ) + 1 := ha
    have hb' : hgt b = (i : ℕ) + 1 := hb
    have : hgt a < hgt b := hgt_strictMono (lt_of_le_of_ne hle hab)
    omega
  · intro x
    have h1 : 1 ≤ hgt x := one_le_hgt x
    have h2 : hgt x ≤ maxChainCard α := hgt_le_maxChainCard x
    refine ⟨⟨hgt x - 1, by omega⟩, ?_⟩
    show hgt x = (hgt x - 1) + 1
    omega

