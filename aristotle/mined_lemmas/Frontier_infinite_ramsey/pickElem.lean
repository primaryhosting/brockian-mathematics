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

noncomputable def pickElem (s : Set ℕ) : ℕ := if h : s.Nonempty then h.choose else 0

