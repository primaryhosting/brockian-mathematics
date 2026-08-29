import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Metric Set

namespace Brouwer2D

noncomputable section

/-- The punctured complex plane, the base of the exponential covering map. -/
abbrev Cstar := {z : ℂ // z ≠ 0}

/-- The exponential covering map `ℂ → ℂ \ {0}`. -/

theorem const_of_exp_eq_one {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] {g : A → ℂ}
    (hg : Continuous g) (h : ∀ x, Complex.exp (g x) = 1) (x y : A) : g x = g y :=
  isCoveringMap_pexp.isSeparatedMap.const_of_comp
    isCoveringMap_pexp.isLocalHomeomorph.isLocallyInjective hg
    (fun a a' => Subtype.ext (by simp [pexp, h])) x y

/-- The standard parametrization of the unit circle. -/
