/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma sum_flip_sq {k : ℕ} (f : Cube k → ℝ) :
    ∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2
      = ∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2 := by
  have hi : ∀ i : Fin k, ∑ x : Cube k, (f (flipAt i x)) ^ 2 = ∑ x : Cube k, (f x) ^ 2 := by
    intro i
    refine Fintype.sum_bijective (flipAt i) ?_ _ _ (fun x => rfl)
    exact Function.bijective_iff_has_inverse.2
      ⟨flipAt i, fun x => flipAt_flipAt i x, fun x => flipAt_flipAt i x⟩
  calc ∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2
      = ∑ i : Fin k, ∑ x : Cube k, (f (flipAt i x)) ^ 2 := Finset.sum_comm
    _ = ∑ _i : Fin k, ∑ x : Cube k, (f x) ^ 2 := Finset.sum_congr rfl fun i _ => hi i
    _ = ∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2 := Finset.sum_comm

/-- The Laplacian quadratic form equals half the Dirichlet form. -/
