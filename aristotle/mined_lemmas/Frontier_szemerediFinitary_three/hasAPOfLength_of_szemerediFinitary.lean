/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Finset

/-- `A` has positive upper density: there is `δ > 0` such that infinitely many initial
segments `{0, …, n-1}` meet `A` in at least `δ * n` elements. -/

theorem hasAPOfLength_of_szemerediFinitary {A : Set ℕ} (hA : HasPositiveUpperDensity A)
    {k : ℕ} (hk : SzemerediFinitary k) : HasAPOfLength A k := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N, hN⟩ := hk δ hδ
  obtain ⟨n, hnN, hn⟩ := hdens N
  obtain ⟨a, d, hd, hAP⟩ := hN n hnN _ (Finset.filter_subset _ _) hn
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have := hAP i hi
  simp only [Finset.mem_filter] at this
  exact this.2

/-- **Furstenberg–Szemerédi**.

Every subset `A ⊆ ℕ` of positive upper density contains a nontrivial three-term arithmetic
progression (unconditionally, via Roth's theorem), and, for every `k`, contains a `k`-term
arithmetic progression as soon as the finitary Szemerédi statement in length `k` holds.
The second component is the Lean-checked reduction of the infinitary multiple-recurrence
form of Szemerédi's theorem to its finitary form. -/
