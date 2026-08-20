import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem exists_unique_shift (p s : ℕ) [NeZero p] :
    ∃ r₀, r₀ < p ∧ p ∣ s + r₀ ∧ ∀ r, r < p → p ∣ s + r → r = r₀ := by
  have hcast : ∀ a : ℕ, (p ∣ s + a) ↔ ((a : ZMod p) = -(s : ZMod p)) := by
    intro a
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  refine ⟨((-(s : ZMod p)).val), ZMod.val_lt _, ?_, ?_⟩
  · rw [hcast, ZMod.natCast_val, ZMod.cast_id]
  · intro r hr hdvd
    rw [hcast] at hdvd
    rw [← hdvd, ZMod.val_cast_of_lt hr]

open Classical in
/-- **Razborov–Smolensky**: for distinct primes `p` and `q`, the `MOD p` function is not
computed by polynomial size constant depth circuits with unbounded fan-in AND/OR/NOT gates
and `MOD q` gates. -/
