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

def OrthonormalFamily {d n : ℕ} (u : Fin n → Space d → ℝ) : Prop :=
  ∀ i j, (∫ x, u i x * u j x) = if i = j then 1 else 0

/-- Regularity conditions making a family of orbitals a legitimate `H¹` orthonormal family. -/
structure AdmissibleFamily {d n : ℕ} (u : Fin n → Space d → ℝ) : Prop where
  differentiable : ∀ i, Differentiable ℝ (u i)
  measurable : ∀ i, Measurable (u i)
  sq_integrable : ∀ i, Integrable (fun x => (u i x) ^ 2)
  grad_integrable : ∀ i, Integrable (fun x => ‖gradient (u i) x‖ ^ 2)
  orthonormal : OrthonormalFamily u

/-! ## The Lieb–Thirring inequality

We state the Lieb–Thirring inequality for `γ = 1` in its equivalent variational form: for
every `H¹`-orthonormal family `u` and every potential `V`, the sum of the one-particle
energies `∑ᵢ ⟨uᵢ, (-Δ + V) uᵢ⟩` is bounded below by `-L ∫ (V₋)^(1 + d/2)`.  By the min–max
principle this is exactly the statement that the sum of the negative eigenvalues of the
Schrödinger operator `-Δ + V` on `L²(ℝ^d)` is at least `-L ∫ (V₋)^(1 + d/2)`. -/
