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

lemma sum_cons_split {k : ℕ} (F : (Fin (k + 1) → Bool) → ℝ) :
    ∑ x : Fin (k + 1) → Bool, F x
      = ∑ y : Fin k → Bool, (F (Fin.cons false y) + F (Fin.cons true y)) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) => Bool) F]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [add_comm]
  rfl

/-- Poincaré inequality: `4 * (∑ f² - (∑ f)²/2^k) ≤ En f`. -/
