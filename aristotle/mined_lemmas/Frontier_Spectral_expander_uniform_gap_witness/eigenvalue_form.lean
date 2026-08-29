import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem eigenvalue_form {k : ℕ} (mu : ℝ) (v : Cube k → ℝ) (hv : v ≠ 0)
    (hL : ((hypercube k).lapMatrix ℝ).mulVec v = mu • v) :
    ∃ S : Finset (Fin k), mu = 2 * S.card := by
  set c : Finset (Fin k) → ℝ := fun S => ∑ y : Cube k, v y * chi S y with hc
  have key : ∀ S : Finset (Fin k), mu * c S = 2 * S.card * c S := by
    intro S
    have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * chi S x = mu * c S := by
      rw [hc]
      simp only [hL, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have h2 : ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec (chi S) x
        = 2 * S.card * c S := by
      simp only [lap_chi, Pi.smul_apply, smul_eq_mul, hc]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [← h1, ← h2]
    exact lap_symm v (chi S)
  obtain ⟨x, hx⟩ : ∃ x : Cube k, v x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  have hsum : ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, c S * chi S x ≠ 0 := by
    rw [fourier_inversion v x]
    exact mul_ne_zero (by positivity) hx
  obtain ⟨S, _, hS⟩ : ∃ S ∈ (Finset.univ : Finset (Fin k)).powerset, c S * chi S x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hsum (Finset.sum_eq_zero hcon)
  have hcS : c S ≠ 0 := fun h => hS (by rw [h]; ring)
  exact ⟨S, mul_right_cancel₀ hcS (key S)⟩

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (which has `2 ^ k` vertices) equals `2`.  In particular the family `(Q k)` has a
spectral gap bounded below by `2`, uniformly in `k`. -/
