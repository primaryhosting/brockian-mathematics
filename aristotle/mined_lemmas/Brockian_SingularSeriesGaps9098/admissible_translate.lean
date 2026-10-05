/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

namespace Brockian

/-- A finite set of integers `H` (a "gap pattern") is *admissible* when, for every prime `p`,
the elements of `H` do not cover all residue classes modulo `p`.  This is exactly the condition
under which the associated singular series is nonzero, i.e. the Hardy–Littlewood prime tuple
conjecture predicts infinitely many translates of `H` consisting entirely of primes. -/

theorem admissible_translate {H : Finset ℤ} (hH : Admissible H) (m : ℤ) :
    Admissible (H.image (fun x => x + m)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (m : ZMod p), ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have := hr y hy
  push_cast
  intro hcon
  exact this (by linear_combination hcon)

/-- The `k`-element pattern `{0, k!, 2·k!, …, (k-1)·k!}` is admissible for every `k`. -/
