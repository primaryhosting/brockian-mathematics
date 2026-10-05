import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Filter Set

open Classical in
/-- Choice of an element of a set of naturals (junk value `0` when empty). -/

theorem pickElem_mem {s : Set ℕ} (h : s.Nonempty) : pickElem s ∈ s := by
  simp only [pickElem, dif_pos h]
  exact h.choose_spec

/-- The decreasing family of sets used to build a monochromatic sequence. -/
