/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1` in place `i`). -/

theorem hypercube_family_uniform_gap :
    (∀ k : ℕ, Fintype.card (Cube k) = 2 ^ k) ∧
    ∀ k : ℕ, 1 ≤ k → (∀ μ : ℝ, μ ≠ 0 → (∃ v : Cube k → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) → 2 ≤ μ) ∧
      ∃ v : Cube k → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  refine ⟨card_cube, fun k hk => ⟨fun μ hμ hv => ?_, two_is_eigenvalue hk⟩⟩
  exact (expander_uniform_gap_witness k hk).2 ⟨hμ, hv⟩

end Frontier.Spectral

