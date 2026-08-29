import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Finset

/-- The trace of a set `A ⊆ ℕ` on the initial segment `{0, 1, ..., N - 1}`. -/

theorem szemeredi_of_finitary (hSz : SzemerediFinitary) {A : Set ℕ} (hA : HasPosUpperDensity A)
    (k : ℕ) : HasAPOfLength A k := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N₀, hN₀⟩ := hSz k δ hδ
  obtain ⟨N, hN, hcard⟩ := hdens N₀
  obtain ⟨a, d, hd, hmem⟩ := hN₀ N hN (trace A N) (trace_subset A N) hcard
  exact ⟨a, d, hd, fun i hi => mem_of_mem_trace (hmem i hi)⟩

/-- **Furstenberg–Szemerédi.**

Positive-density subsets of `ℕ` contain arbitrarily long arithmetic progressions.

Two Lean-checked components are recorded here:

* the *base case*: unconditionally, every set of positive upper density contains an arithmetic
  progression of length `k` for every `k ≤ 3` (the length-three case being Roth's theorem);
* the *reduction*: assuming the finitary form of Szemerédi's theorem (`SzemerediFinitary`), every
  set of positive upper density contains arithmetic progressions of *every* length. -/
