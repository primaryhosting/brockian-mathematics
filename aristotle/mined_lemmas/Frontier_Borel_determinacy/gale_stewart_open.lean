import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

theorem gale_stewart_open (A : Set (ℕ → X)) (hA : IsOpenPayoff A) : Determined A := by
  by_cases h : IWins A []
  · exact Or.inl h
  refine Or.inr ⟨defenseStrategy A, fun σ hmem => ?_⟩
  obtain ⟨n, hn⟩ := hA _ hmem
  refine not_IWins_posFrom h σ n ⟨defenseStrategy A, fun τ' => ?_⟩
  refine hn _ (fun i hi => ?_)
  set q := posFrom [] σ (defenseStrategy A) n with hqdef
  have hqlen : q.length = n := by rw [hqdef, posFrom_length]; simp
  have h1 : playFrom q (defenseStrategy A) τ' i
      = q.getD i (Classical.arbitrary X) := by
    have : i < q.length + 0 := by omega
    simpa [posFrom] using playFrom_eq_getD q (defenseStrategy A) τ' 0 i this
  have h2 : playFrom [] σ (defenseStrategy A) i = q.getD i (Classical.arbitrary X) := by
    have : i < ([] : List X).length + n := by simpa using hi
    simpa [hqdef] using playFrom_eq_getD ([] : List X) σ (defenseStrategy A) n i this
  rw [h1, h2]

/-! ### The dual (closed) case -/

