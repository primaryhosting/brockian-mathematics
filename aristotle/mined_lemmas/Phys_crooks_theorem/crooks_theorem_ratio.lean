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

theorem crooks_theorem_ratio [Nonempty X] (hβ : β ≠ 0) (hDB : DetailedBalance β E p N) (w : ℝ)
    (hne : ∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -w), Prev β E p N δ ≠ 0) :
    (∑ γ ∈ Finset.univ.filter (fun γ : Fin (N + 1) → X => Wfwd E N γ = w), Pfwd β E p N γ) /
        (∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -w), Prev β E p N δ) =
      Real.exp (β * (w - deltaF β E N)) := by
  rw [crooks_theorem hβ hDB w, mul_div_assoc, div_self hne, mul_one]

/-- The heat-bath (Gibbs) relaxation kernel for the protocol step `t`. -/
