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

noncomputable def coulombPotential {N K : ℕ} (Z : Fin K → ℝ) (R : Fin K → Space 3)
    (x : Config N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin K, -(Z j / dist (pos x i) (R j)))
    + (∑ i : Fin N, ∑ i' : Fin N, if i < i' then 1 / dist (pos x i) (pos x i') else 0)
    + (∑ j : Fin K, ∑ j' : Fin K, if j < j' then Z j * Z j' / dist (R j) (R j') else 0)

/-- The energy `⟨ψ, Hψ⟩` of a normalized many-body wave function `ψ`. -/
