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

lemma dotProduct_lap {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = En f / 2 := by
  have hsq : ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2
      = ∑ x : Fin k → Bool, ∑ i : Fin k, (f x) ^ 2 := by
    calc ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2
        = ∑ i : Fin k, ∑ x : Fin k → Bool, (f (cflip i x)) ^ 2 := Finset.sum_comm
      _ = ∑ _i : Fin k, ∑ x : Fin k → Bool, (f x) ^ 2 :=
          Finset.sum_congr rfl fun i _ => sum_cflip i (fun x => (f x) ^ 2)
      _ = ∑ x : Fin k → Bool, ∑ _i : Fin k, (f x) ^ 2 := Finset.sum_comm
  have hEn : En f = 2 * ∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - f x * f (cflip i x)) := by
    unfold En
    have h1 : ∑ x : Fin k → Bool, ∑ i : Fin k, (f x - f (cflip i x)) ^ 2
        = (∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - 2 * (f x * f (cflip i x))))
          + ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hsq, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hEn]
  have : f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f)
      = ∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - f x * f (cflip i x)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lap_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [this]
  ring

