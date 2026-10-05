/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma mixedProfiles_isCompact : IsCompact (mixedProfiles S) := by
  have hbox : IsCompact (Set.pi Set.univ
      (fun i : ι => Set.pi Set.univ (fun _ : S i => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset mixedProfiles_isClosed ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  intro i s
  refine ⟨(hx i).1 s, ?_⟩
  have : x i s ≤ ∑ t, x i t :=
    Finset.single_le_sum (f := fun t => x i t) (fun t _ => (hx i).1 t) (mem_univ s)
  rw [(hx i).2] at this
  exact this

/-! ## Nash's map -/

/-- The gain of player `i` from switching to the pure strategy `s`, truncated at `0`. -/
