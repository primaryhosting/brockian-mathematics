import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma exists_basic_nbhd [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W)
    {f : ℕ → A} (hf : f ∈ W) : ∃ n, ∀ g : ℕ → A, (∀ i < n, g i = f i) → g ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW f hf
  refine ⟨(I.sup id) + 1, fun g hg => hsub ?_⟩
  intro i hi
  have h1 : i ≤ I.sup id := by simpa using Finset.le_sup (f := id) hi
  rw [hg i (by omega)]
  exact (hu i hi).2

/-- If player I wins the subgame after every reply `b` to the move `a`, then I wins from `p`. -/
