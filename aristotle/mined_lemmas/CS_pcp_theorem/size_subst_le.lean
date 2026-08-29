import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem size_subst_le {k N : ℕ} (c : Circuit k) (f : Fin k → Circuit N) (M : ℕ)
    (hf : ∀ i, (f i).size ≤ M) : (c.subst f).size ≤ c.size * (M + 1) := by
  induction c with
  | const b => simp [subst, size]
  | var i => simpa [subst, size] using (hf i).trans (Nat.le_succ M)
  | not c ih => simp only [subst, size]; nlinarith [ih]
  | and c d ihc ihd => simp only [subst, size]; nlinarith [ihc, ihd]
  | or c d ihc ihd => simp only [subst, size]; nlinarith [ihc, ihd]

/-- Conjunction of a list of circuits. -/
