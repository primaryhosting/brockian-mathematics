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

def IsHomog (k : ℕ) {r : ℕ} (c : Finset ℕ → Fin r) (Y : Finset ℕ) : Prop :=
  ∀ s ⊆ Y, s.card = k → ∀ t ⊆ Y, t.card = k → c s = c t

/-! ## Ultrafilter limits of finitely valued functions -/

