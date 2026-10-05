import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

/-- Two antitone functions on a linear order monovary. -/

theorem monovary_of_antitone {ι : Type*} [LinearOrder ι] {f g : ι → ℝ}
    (hf : Antitone f) (hg : Antitone g) : Monovary f g := by
  intro i j hij
  rcases le_total j i with h | h
  · exact hf h
  · exact absurd (hg h) (not_le.2 hij)

/-- A bilinear pairing against a doubly stochastic matrix, with monovarying weights, is bounded
by the "diagonal" pairing.  This is the rearrangement step in the von Neumann trace inequality. -/
