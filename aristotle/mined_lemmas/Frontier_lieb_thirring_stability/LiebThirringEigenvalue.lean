import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

def LiebThirringEigenvalue (d : ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin n → Space d → ℝ) (V : Space d → ℝ),
    AdmissibleFamily u → Measurable V →
    Integrable (fun x => negPart (V x) ^ ((1 : ℝ) + d / 2)) →
    Integrable (fun x => V x * density u x) →
    -L * (∫ x, negPart (V x) ^ ((1 : ℝ) + d / 2)) ≤ kineticEnergy u + potentialEnergy V u

/-- The Lieb–Thirring kinetic energy inequality: for every `H¹`-orthonormal family, the
kinetic energy dominates `K ∫ ρ^(1 + 2/d)`, where `ρ` is the one-particle density.  This is
the form of the inequality that yields stability of matter. -/
