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

lemma nashMap_mapsTo (u : ι → (∀ j, S j) → ℝ) :
    Set.MapsTo (nashMap u) (mixedProfiles S) (mixedProfiles S) := by
  intro x hx i
  have hden : (0 : ℝ) < 1 + ∑ t, gain u i t x := lt_of_lt_of_le zero_lt_one (one_le_denom u i x)
  refine ⟨fun s => ?_, ?_⟩
  · exact div_nonneg (add_nonneg ((hx i).1 s) (gain_nonneg u i s x)) hden.le
  · show ∑ s, (x i s + gain u i s x) / (1 + ∑ t, gain u i t x) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, (hx i).2, div_self hden.ne']

/-- In any mixed profile some strategy in the support of player `i` is not better than
the profile itself. -/
