import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

lemma sum_energy_telescope :
    ∑ k ∈ Finset.range N, (E (k + 1) (x k) - E (k + 1) (x (k + 1)))
      = work E N x + E 0 (x 0) - E N (x N) := by
  have h : ∀ k, E (k + 1) (x k) - E (k + 1) (x (k + 1))
      = (E (k + 1) (x k) - E k (x k)) + (E k (x k) - E (k + 1) (x (k + 1))) := by
    intro k; ring
  simp only [h, Finset.sum_add_distrib]
  have h2 : ∑ k ∈ Finset.range N, ((fun k => E k (x k)) k - (fun k => E k (x k)) (k + 1))
      = E 0 (x 0) - E N (x N) := Finset.sum_range_sub' (fun k => E k (x k)) N
  rw [work]
  simp only at h2
  rw [h2]
  ring

/-- **Crooks fluctuation theorem** (product form): the forward path weight equals
`e^{β(W − ΔF)}` times the weight of the time-reversed path under the reversed protocol. -/
