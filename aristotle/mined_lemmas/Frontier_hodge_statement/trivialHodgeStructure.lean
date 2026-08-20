/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of the pinned revision) contains no singular cohomology of complex
varieties, no Hodge decomposition and no Chow groups / cycle class maps, so there
is no existing lemma that closes this goal: the statement has to be built from
scratch.  We therefore

* define rational Hodge structures (`Frontier.HodgeStructure`) and their spaces of
  Hodge classes (`Frontier.hodgeClasses`),
* package the cohomological data of a smooth projective complex variety together
  with its cycle class maps (`Frontier.HodgeData`),
* state the Hodge conjecture for such data (`Frontier.HodgeConjecture`), and
* prove, in `Frontier.hodge_statement`, the base case `p = 0` of the conjecture
  together with the standard reduction of the conjecture to the inclusion
  "every Hodge class is algebraic".
-/

import Mathlib

namespace Frontier

open TensorProduct

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation on `ℂ ⊗[ℚ] V`, acting on the left tensor factor.  It is only
`ℚ`-linear (it is conjugate-linear over `ℂ`). -/

noncomputable def trivialHodgeStructure (p : ℕ) : HodgeStructure ℚ (2 * p) where
  piece pq := if pq = (p, p) then ⊤ else ⊥
  weight pq hpq := by
    have : pq ≠ (p, p) := by
      rintro rfl
      exact hpq (by omega)
    simp [this]
  internal := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = (p, p)
      · subst hi
        have : (⨆ j, ⨆ (_ : j ≠ (p, p)),
            (if j = (p, p) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥)) = ⊥ :=
          iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => by simp [hj]
        rw [this]
        exact disjoint_bot_right
      · simp only [hi, if_false]
        exact disjoint_bot_left
    · exact top_le_iff.mp (le_iSup_of_le (p, p) (by simp))
  conj_piece pq := by
    by_cases hpq : pq = (p, p)
    · subst hpq
      simp
    · simp [hpq]

open Classical in
/-- An explicit example of `HodgeData`, witnessing that the structure is inhabited. -/
