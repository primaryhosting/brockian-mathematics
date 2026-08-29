import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Infinite two-player games of perfect information

We work with the Gale–Stewart game on a nonempty type `A`:  players I and II alternately
choose elements of `A`, player I moving first, producing an infinite play `x : ℕ → A`.
Player I wins the play iff `x ∈ W`.
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

lemma seqOpen_of_isOpen {W : Set (ℕ → A)} (hW : IsOpen W) : SeqOpen W := by
  intro x hx
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  have hy' : ∀ i < I.sup id + 1, y i = x i := takePrefix_eq_iff.mp hy
  refine hsub (fun i hi => ?_)
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy' i (by omega)]
  exact (hu i hi).2

omit [Nonempty A] in
