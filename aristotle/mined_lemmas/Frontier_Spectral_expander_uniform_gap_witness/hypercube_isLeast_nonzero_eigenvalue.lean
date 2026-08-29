/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Frontier.Spectral

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

theorem hypercube_isLeast_nonzero_eigenvalue (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  constructor
  · obtain ⟨v, hv0, hv⟩ := eigenvector_two (⟨0, hk⟩ : Fin k)
    exact ⟨two_ne_zero, v, hv0, hv⟩
  · rintro μ ⟨hμ, v, hv0, hv⟩
    exact two_le_of_nonzero_eigenvalue hμ hv0 hv

/-- **Uniform spectral gap for the hypercube family.**
There is a constant `c > 0` (namely `c = 2`, independent of `k`) such that for every `k ≥ 1`
the smallest nonzero eigenvalue of the Laplacian of the hypercube graph `Q_k`
(on `2 ^ k` vertices) is exactly `c`. In particular the family `(Q_k)` of graphs
has a uniform spectral gap. -/
