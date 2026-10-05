/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u

local infixr:65 " ⊗ " => Sum.elim

/-! ## Exponential polynomials

An *exponential polynomial* in variables of type `α` is built from variables and natural
number constants using addition, multiplication and exponentiation.  These are the objects
occurring in the Davis–Putnam–Robinson theorem. -/

/-- Syntax of exponential polynomials with variables in `α`. -/
inductive ExpPoly (α : Type u) : Type u
  | var : α → ExpPoly α
  | const : ℕ → ExpPoly α
  | add : ExpPoly α → ExpPoly α → ExpPoly α
  | mul : ExpPoly α → ExpPoly α → ExpPoly α
  | pow : ExpPoly α → ExpPoly α → ExpPoly α

/-- Evaluation of an exponential polynomial at a valuation `v : α → ℕ`. -/

theorem exists_expPoly_sub {α : Type u} (p : Poly α) :
    ∃ e f : ExpPoly α, ∀ v, (p v : ℤ) = (e.eval v : ℤ) - (f.eval v : ℤ) := by
  induction p using Poly.induction with
  | H1 i => exact ⟨.var i, .const 0, fun v => by simp [ExpPoly.eval]⟩
  | H2 n => exact ⟨.const n.toNat, .const (-n).toNat, fun v => by simp [ExpPoly.eval]⟩
  | H3 p q hp hq =>
    obtain ⟨e₁, f₁, h₁⟩ := hp
    obtain ⟨e₂, f₂, h₂⟩ := hq
    refine ⟨.add e₁ f₂, .add f₁ e₂, fun v => ?_⟩
    simp only [Poly.sub_apply, ExpPoly.eval, h₁ v, h₂ v]
    push_cast
    ring
  | H4 p q hp hq =>
    obtain ⟨e₁, f₁, h₁⟩ := hp
    obtain ⟨e₂, f₂, h₂⟩ := hq
    refine ⟨.add (.mul e₁ e₂) (.mul f₁ f₂), .add (.mul e₁ f₂) (.mul f₁ e₂), fun v => ?_⟩
    simp only [Poly.mul_apply, ExpPoly.eval, h₁ v, h₂ v]
    push_cast
    ring

/-- Every Diophantine set is exponential Diophantine (exponentiation may simply be unused). -/
