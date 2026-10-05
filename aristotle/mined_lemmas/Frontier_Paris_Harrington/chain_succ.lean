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

theorem chain_succ {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k n : ℕ) :
    chain U D k (n + 1) = insert (chainElt U D k n) (chain U D k n) := rfl

section Greedy

variable {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
  (hU : (U : Filter ℕ) ≤ cofinite)
  (hD : ∀ i s, D (i + 1) s = ulim U (fun x => D i (insert x s)))

include hU hD

