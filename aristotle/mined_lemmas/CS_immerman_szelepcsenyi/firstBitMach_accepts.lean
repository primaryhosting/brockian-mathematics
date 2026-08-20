import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma firstBitMach_accepts (n : ℕ) (x : Fin n → Bool) :
    (firstBitMach n).Accepts x ↔ ∃ h : 0 < n, x ⟨0, h⟩ = true := by
  have hedge : ((firstBitMach n).edge false true).holds x ↔ ∃ h : 0 < n, x ⟨0, h⟩ = true := by
    by_cases h : 0 < n
    · simp [firstBitMach, h, Lit.holds]
    · simp [firstBitMach, h, Lit.holds]
  rw [← hedge]
  constructor
  · intro hacc
    rcases hacc.cases_head with hcon | ⟨c, hc, _⟩
    · exact absurd hcon (by simp)
    · have : c = true := by
        by_contra hne
        have hc' : c = false := by
          cases c with
          | false => rfl
          | true => exact absurd rfl hne
        rw [hc'] at hc
        exact absurd hc (by simp [Mach.Step, firstBitMach, Lit.holds])
      rw [this] at hc
      exact hc
  · intro hstep
    exact Relation.ReflTransGen.single hstep

/-- The language "the first input bit is `true`" belongs to `NL`. -/
