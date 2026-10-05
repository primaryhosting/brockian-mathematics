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

noncomputable def Pfwd (β : ℝ) (E : ℕ → X → ℝ) (p : ℕ → X → X → ℝ) (N : ℕ)
    (γ : Fin (N + 1) → X) : ℝ :=
  Real.exp (-β * E 0 (st γ 0)) / Zpf β E 0 * ∏ t ∈ range N, p t (st γ t) (st γ (t + 1))

/-- Work done on the system along the forward trajectory `γ`. -/
