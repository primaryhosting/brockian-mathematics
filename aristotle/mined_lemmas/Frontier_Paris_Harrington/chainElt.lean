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

noncomputable def chainElt {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
    (n : ℕ) : ℕ := sInf (goodSet D k (chain U D k n))

