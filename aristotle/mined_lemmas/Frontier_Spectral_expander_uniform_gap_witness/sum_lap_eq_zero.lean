/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma sum_lap_eq_zero {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ f) x = 0 := by
  have h : ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ f) x
      = (∑ x : Fin k → Bool, ∑ i : Fin k, f x)
        - ∑ x : Fin k → Bool, ∑ i : Fin k, f (cflip i x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lap_apply, ← Finset.sum_sub_distrib]
    simp
  rw [h, sub_eq_zero]
  calc ∑ _x : Fin k → Bool, ∑ _i : Fin k, f _x
      = ∑ _i : Fin k, ∑ _x : Fin k → Bool, f _x := Finset.sum_comm
    _ = ∑ i : Fin k, ∑ x : Fin k → Bool, f (cflip i x) :=
        Finset.sum_congr rfl fun i _ => (sum_cflip i f).symm
    _ = ∑ x : Fin k → Bool, ∑ i : Fin k, f (cflip i x) := Finset.sum_comm

/-! ### The Poincaré inequality for the hypercube -/

