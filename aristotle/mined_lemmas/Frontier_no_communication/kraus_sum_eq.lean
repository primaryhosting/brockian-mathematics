import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix

variable {A B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

/-- The reduced state (partial trace over the second subsystem `B`) of a bipartite
state `ρ` on `A ⊗ B`.  This is the object that encodes *all* statistics available to
an observer who only has access to subsystem `A`. -/

lemma kraus_sum_eq (K : I → Matrix B B ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) (c c' : B) :
    ∑ b, ∑ i, K i b c * star (K i b c') = if c' = c then 1 else 0 := by
  have h := congrFun (congrFun hK c') c
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] at h
  rw [Finset.sum_comm]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

/-- **No-communication theorem** (Kraus / CPTP form).

If `ρ` is any (bipartite) state of a composite system `A ⊗ B` -- in particular an
entangled one -- and Bob performs an arbitrary local operation on his half `B`,
described by Kraus operators `K i` satisfying the completeness relation
`∑ i, (K i)ᴴ * (K i) = 1`, then Alice's reduced state, obtained by tracing out `B`,
is completely unchanged.  Since the reduced state determines every measurement
statistic accessible to Alice, no information can be transmitted from Bob to Alice
by local operations. -/
