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

theorem ulim_spec {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) :
    {x | f x = ulim U f} ∈ U :=
  (exists_ulim U f).choose_spec

/-! ## The infinite Ramsey theorem

We fix a family `D` of colourings, where `D i` colours the `(k - i)`-element sets, obtained by
iterating the ultrafilter-limit operation. -/

/-- The set of admissible next elements after having chosen the finite set `T`. -/
