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

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/


lemma hat_lap {k : ℕ} (f : Cube k → ℝ) (s : Cube k) :
    hat ((hypercube k).lapMatrix ℝ *ᵥ f) s = (2 * wt s : ℝ) * hat f s := by
  classical
  have key : ∀ i : Fin k, ∑ x, f (flipAt x i) * chi s x = sgn (s i) * hat f s := by
    intro i
    let e : Equiv.Perm (Cube k) :=
      Function.Involutive.toPerm (fun x => flipAt x i) (fun x => flipAt_flipAt x i)
    have he : ∀ x : Cube k, e x = flipAt x i := fun _ => rfl
    calc ∑ x, f (flipAt x i) * chi s x
        = ∑ x, (fun y => f y * chi s (flipAt y i)) (e x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [he, flipAt_flipAt]
      _ = ∑ y, f y * chi s (flipAt y i) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = sgn (s i) * hat f s := by
          rw [hat, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [chi_flipAt]
          ring
  unfold hat
  have hterm : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ f) x * chi s x
      = (k : ℝ) * (f x * chi s x) - ∑ i, f (flipAt x i) * chi s x := by
    intro x
    rw [lap_mulVec_apply, sub_mul, Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_comm, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i),
    ← Finset.sum_mul, sum_sgn]
  simp only [hat]
  ring

