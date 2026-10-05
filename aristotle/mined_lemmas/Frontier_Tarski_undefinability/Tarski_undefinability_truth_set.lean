/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is given as a plain block comment and repeated below verbatim.)

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open FirstOrder Language

/-! ## The language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, the successor `S`,
addition and multiplication. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | succ : arithFunc 1
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The relation symbols of the language of arithmetic: the order relation `<`. -/
inductive arithRel : ℕ → Type
  | lt : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic, `(0, S, +, ·, <)`. -/

theorem Tarski_undefinability_truth_set
    (codeF : arith.Formula (Fin 1) → ℕ) (codeS : arith.Sentence → ℕ) (sub : ℕ → ℕ → ℕ)
    (hsub : ∀ (φ : arith.Formula (Fin 1)) (n : ℕ), sub (codeF φ) n = codeS (substNumeral φ n))
    (hsubDef : IsArithmetical₃ {t : ℕ × ℕ × ℕ | sub t.1 t.2.1 = t.2.2})
    (T : Set ℕ) (hT : ∀ σ : arith.Sentence, codeS σ ∈ T ↔ (ℕ ⊨ σ)) :
    ¬ IsArithmetical T := by
  intro hTdef
  refine Tarski_undefinability codeF
    {p : ℕ × ℕ | ∃ k : ℕ, (p.1, p.2, k) ∈ {t : ℕ × ℕ × ℕ | sub t.1 t.2.1 = t.2.2} ∧ k ∈ T}
    ?_ (isArithmetical₂_exists_and hsubDef hTdef)
  intro φ n
  constructor
  · rintro ⟨k, hk, hkT⟩
    simp only [Set.mem_setOf_eq] at hk
    rw [← hk, hsub φ n] at hkT
    exact (realize_substNumeral φ n).1 ((hT _).1 hkT)
  · intro h
    refine ⟨sub (codeF φ) n, rfl, ?_⟩
    rw [hsub φ n]
    exact (hT _).2 ((realize_substNumeral φ n).2 h)

end Frontier

