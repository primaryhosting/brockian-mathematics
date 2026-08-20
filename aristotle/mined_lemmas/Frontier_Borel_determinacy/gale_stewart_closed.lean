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

theorem gale_stewart_closed (A : Set (ℕ → X)) (hA : IsOpenPayoff Aᶜ) : Determined A := by
  by_cases h : IIWins A []
  · exact Or.inr h
  refine Or.inl ⟨attackStrategy A, fun τ => ?_⟩
  by_contra hmem
  obtain ⟨n, hn⟩ := hA _ hmem
  refine not_IIWins_posFrom h τ n ⟨attackStrategy A, fun σ' hmem' => ?_⟩
  set q := posFrom [] (attackStrategy A) τ n with hqdef
  have hqlen : q.length = n := by rw [hqdef, posFrom_length]; simp
  refine hn (playFrom q σ' (attackStrategy A)) (fun i hi => ?_) hmem'
  have h1 : playFrom q σ' (attackStrategy A) i = q.getD i (Classical.arbitrary X) := by
    have : i < q.length + 0 := by omega
    simpa [posFrom] using playFrom_eq_getD q σ' (attackStrategy A) 0 i this
  have h2 : playFrom [] (attackStrategy A) τ i = q.getD i (Classical.arbitrary X) := by
    have : i < ([] : List X).length + n := by simpa using hi
    simpa [hqdef] using playFrom_eq_getD ([] : List X) (attackStrategy A) τ n i this
  rw [h1, h2]

/-! ### Sanity checks: plays really follow the strategies -/

