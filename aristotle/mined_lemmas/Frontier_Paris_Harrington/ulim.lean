import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

noncomputable def ulim {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) : Fin r :=
  (exists_ulim U f).choose

