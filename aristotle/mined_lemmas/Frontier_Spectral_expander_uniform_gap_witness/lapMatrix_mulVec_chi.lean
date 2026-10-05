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

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

/-- The basis vector flipping coordinate `i`. -/

lemma lapMatrix_mulVec_chi (k : ℕ) (s : Cube k) :
    (hypercube k).lapMatrix ℝ *ᵥ chi s = (2 * wt s : ℝ) • chi s := by
  funext x
  rw [hypercube_lapMatrix_mulVec]
  have h : ∀ i : Fin k, chi s (x + flip i) = chi s x * sgn (s i) := by
    intro i
    rw [chi_add_right]
    simp [chi, dot_flip_right]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, sum_sgn_eq]
  simp [Pi.smul_apply]
  ring

/-- Fourier coefficients of the Laplacian applied to a vector. -/
