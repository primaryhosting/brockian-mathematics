import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem loopVal_iff :
    ∀ i : ℕ, loopVal R k a b i = true ↔
      ∃ m : Fin n, i ≤ (m : ℕ) ∧ cy R k a m = true ∧ cy R k m b = true := by
  intro i
  induction hd : n - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    subst hd
    by_cases h : i < n
    · rw [loopVal_of_lt h]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      rw [ih (n - (i + 1)) (by omega) (i + 1) rfl]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨m, hm, h1, h2⟩)
        · exact ⟨⟨i, h⟩, le_refl _, h1, h2⟩
        · exact ⟨m, by omega, h1, h2⟩
      · rintro ⟨m, hm, h1, h2⟩
        rcases eq_or_lt_of_le hm with heq | hlt
        · left
          have : m = ⟨i, h⟩ := Fin.ext heq.symm
          subst this
          exact ⟨h1, h2⟩
        · exact Or.inr ⟨m, by omega, h1, h2⟩
    · rw [loopVal_of_ge h]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨m, hm, -, -⟩
      have := m.isLt
      omega

