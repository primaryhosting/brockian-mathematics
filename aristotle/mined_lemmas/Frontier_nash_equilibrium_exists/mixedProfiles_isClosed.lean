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

lemma mixedProfiles_isClosed : IsClosed (mixedProfiles S) := by
  have h1 : mixedProfiles S =
      (⋂ i : ι, ⋂ s : S i, {x : ∀ j, S j → ℝ | 0 ≤ x i s}) ∩
        (⋂ i : ι, {x : ∀ j, S j → ℝ | ∑ s, x i s = 1}) := by
    ext x
    simp only [mixedProfiles, IsMixed, IsDist, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · exact fun h => ⟨fun i s => (h i).1 s, fun i => (h i).2⟩
    · exact fun h i => ⟨fun s => h.1 i s, h.2 i⟩
  rw [h1]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun s =>
      isClosed_le continuous_const (continuous_coord i s)
  · exact isClosed_iInter fun i =>
      isClosed_eq (continuous_finset_sum _ fun s _ => continuous_coord i s) continuous_const

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
