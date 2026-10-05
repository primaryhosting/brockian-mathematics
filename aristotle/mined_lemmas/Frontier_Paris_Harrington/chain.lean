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

noncomputable def chain {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ) :
    ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (sInf (goodSet D k (chain U D k n))) (chain U D k n)

/-- The `n`-th element chosen by the greedy construction. -/
