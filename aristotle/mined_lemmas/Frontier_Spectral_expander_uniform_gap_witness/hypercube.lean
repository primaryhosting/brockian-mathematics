/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = flipAt i x
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [flipAt_flipAt]⟩
  loopless := ⟨by
    rintro x ⟨i, h⟩
    exact flipAt_ne i x h.symm⟩

instance instDecidableAdj (k : ℕ) : DecidableRel (hypercube k).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ i, y = flipAt i x))

