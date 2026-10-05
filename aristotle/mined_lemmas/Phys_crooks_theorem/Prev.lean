/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

noncomputable def Prev (β : ℝ) (E : ℕ → X → ℝ) (p : ℕ → X → X → ℝ) (N : ℕ)
    (δ : Fin (N + 1) → X) : ℝ :=
  Real.exp (-β * Erev E N 0 (st δ 0)) / Zpf β (Erev E N) 0 *
    ∏ s ∈ range N, prev p N s (st δ s) (st δ (s + 1))

/-- Work done on the system along the trajectory `δ` of the reverse process. -/
