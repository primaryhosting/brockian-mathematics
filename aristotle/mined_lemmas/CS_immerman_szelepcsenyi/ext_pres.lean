import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma ext_pres {s t : CSt P.N P.V} (hs : Inv P x s) (hE : Ext P s t)
    (hedge : P.step x s.w t.w) : Inv P x t := by
  obtain ⟨hpc, hji, j', w', hj', rfl⟩ := hE
  obtain ⟨hcore, hu, hS, hjle, hw⟩ := hs.2.2.2.1 hpc
  refine inv_mk3 P x _ hpc hcore hu hS ?_ ?_
  · show (j' : ℕ) ≤ (s.i : ℕ)
    omega
  · show w' ∈ RS P x (j' : ℕ)
    rw [hj']
    exact Or.inr ⟨s.w, hw, hedge⟩

