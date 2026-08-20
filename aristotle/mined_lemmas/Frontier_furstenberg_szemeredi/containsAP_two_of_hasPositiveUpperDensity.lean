/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `A ⊆ ℕ` has positive upper (Banach-type) density: there is `δ > 0` such that for
arbitrarily large `M` the initial segment `{0, …, M-1}` meets `A` in at least `δ * M` points. -/

theorem containsAP_two_of_hasPositiveUpperDensity {A : Set ℕ} (hA : HasPositiveUpperDensity A) :
    ContainsAP A 2 := by
  obtain ⟨a, -, ha⟩ := exists_mem_ge_of_hasPositiveUpperDensity hA 0
  obtain ⟨b, hb, hbA⟩ := exists_mem_ge_of_hasPositiveUpperDensity hA (a + 1)
  refine ⟨a, b - a, by omega, ?_⟩
  intro i hi
  interval_cases i
  · simpa using ha
  · have : a + 1 * (b - a) = b := by omega
    rw [this]; exact hbA

/-- **Furstenberg–Szemerédi (reduction).**  Granting the finitary form of Szemerédi's theorem
(the combinatorial content supplied by Furstenberg's multiple recurrence theorem via the
Furstenberg correspondence principle), every subset of `ℕ` of positive upper density contains
arithmetic progressions of every length. -/
