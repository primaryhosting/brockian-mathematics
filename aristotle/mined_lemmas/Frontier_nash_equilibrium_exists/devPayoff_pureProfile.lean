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

lemma devPayoff_pureProfile (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) (p : ∀ j, S j) :
    devPayoff u i s (pureProfile p) = u i (Function.update p i s) := by
  classical
  rw [devPayoff, Finset.sum_eq_single (Function.update p i s)]
  · have h1 : (Function.update p i s) i = s := Function.update_self ..
    rw [h1]
    have h2 : ∀ j ∈ univ.erase i,
        pureProfile p j ((Function.update p i s) j) = 1 := by
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp [pureProfile]
    rw [Finset.prod_congr rfl h2]
    simp
  · intro q _ hq
    by_cases hqi : q i = s
    · have : ∃ j ∈ univ.erase i, q j ≠ p j := by
        by_contra hcon
        push_neg at hcon
        exact hq (funext fun j => by
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; exact hqi
          · rw [Function.update_of_ne hji]
            exact hcon j (Finset.mem_erase.mpr ⟨hji, mem_univ j⟩))
      obtain ⟨j, hj, hjne⟩ := this
      have : (∏ k ∈ univ.erase i, pureProfile p k (q k)) = 0 :=
        Finset.prod_eq_zero hj (by simp [pureProfile, hjne])
      rw [this]
      ring
    · simp [hqi]
  · intro h
    exact absurd (mem_univ (Function.update p i s)) h

