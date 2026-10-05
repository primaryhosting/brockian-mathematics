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

theorem isArithmetical₂_exists_and {S : Set (ℕ × ℕ × ℕ)} {A : Set ℕ}
    (hS : IsArithmetical₃ S) (hA : IsArithmetical A) :
    IsArithmetical₂ {p : ℕ × ℕ | ∃ k : ℕ, (p.1, p.2, k) ∈ S ∧ k ∈ A} := by
  obtain ⟨σ, hσ⟩ := hS
  obtain ⟨α, hα⟩ := hA
  classical
  set g : Fin 3 → Fin 2 ⊕ Unit := ![Sum.inl 0, Sum.inl 1, Sum.inr ()] with hg
  set h : Fin 1 → Fin 2 ⊕ Unit := ![Sum.inr ()] with hh
  refine ⟨Formula.iExs Unit ((σ.relabel g) ⊓ (α.relabel h)), ?_⟩
  intro m n
  rw [Formula.realize_iExs]
  simp only [Set.mem_setOf_eq, BoundedFormula.realize_inf, Formula.realize_relabel]
  constructor
  · rintro ⟨k, hk, hkA⟩
    refine ⟨fun _ => k, ?_, ?_⟩
    · have : (Sum.elim ![m, n] (fun _ : Unit => k)) ∘ g = ![m, n, k] := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact (hσ m n k).1 hk
    · have : (Sum.elim ![m, n] (fun _ : Unit => k)) ∘ h = ![k] := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact (hα k).1 hkA
  · rintro ⟨i, h1, h2⟩
    refine ⟨i (), ?_, ?_⟩
    · have e : (Sum.elim ![m, n] i) ∘ g = ![m, n, i ()] := by
        funext j; fin_cases j <;> rfl
      rw [e] at h1
      exact (hσ m n (i ())).2 h1
    · have e : (Sum.elim ![m, n] i) ∘ h = ![i ()] := by
        funext j; fin_cases j <;> rfl
      rw [e] at h2
      exact (hα (i ())).2 h2

/-- Substituting the numeral for `n` for the unique free variable of `φ`, producing a
sentence of the language of arithmetic. -/
