/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem DSPACE_zero_trivial {L : Set (List Γ)} (hL : L ∈ DSPACE Γ (fun _ => 0)) :
    L = ∅ ∨ L = Set.univ := by
  obtain ⟨M, hsp, hdec⟩ := hL
  have hrun : ∀ (x : List Γ) (t : ℕ), M.run x t = 0 := by
    intro x t
    have : M.run x t < 2 ^ (0 : ℕ) := hsp x _ ⟨t, rfl⟩
    simpa using this
  by_cases h : M.result 0 = some true
  · right
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx
    obtain ⟨t, ht⟩ := (hdec x).2 hx
    rw [hrun x t, h] at ht
    simp at ht
  · left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨t, ht⟩ := (hdec x).1 hx
    rw [hrun x t] at ht
    exact h ht

end CS

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

import RequestProject.Savitch.Interp

/-!
# The space invariant of the Savitch simulator

The simulator only ever visits states whose recursion stack has depth at most `s` and all of
whose numerical components are at most `2 ^ s`.  This is the content of the predicate
`CS.Good`, which we prove to be preserved by the transition function.
-/

namespace CS

open Classical

variable {Γ : Type}

/-- `GoodStack s k l`: `l` is a legitimate recursion stack whose topmost frame awaits a value
at recursion level `k`. -/
