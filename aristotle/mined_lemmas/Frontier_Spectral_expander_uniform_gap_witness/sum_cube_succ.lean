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


lemma sum_cube_succ {k : ℕ} (F : Cube (k+1) → ℝ) :
    ∑ x : Cube (k+1), F x = ∑ y : Cube k, (F (Fin.cons 0 y) + F (Fin.cons 1 y)) := by
  have h1 : ∑ x : Cube (k+1), F x = ∑ p : ZMod 2 × Cube k, F (Fin.cons p.1 p.2) := by
    refine (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => ZMod 2)) _ _ ?_).symm
    intro p
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

