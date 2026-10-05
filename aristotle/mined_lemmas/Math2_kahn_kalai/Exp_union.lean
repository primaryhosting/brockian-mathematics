import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_union (a b : ℝ) :
    ∀ (V : Finset X) (f : Finset X → ℝ),
      Exp V a (fun W₁ => Exp V b (fun W₂ => f (W₁ ∪ W₂))) = Exp V (a + b - a * b) f := by
  intro V
  induction V using Finset.induction_on with
  | empty => intro f; simp [Exp, wt]
  | insert x V₀ hx ih =>
      intro f
      have inner1 : ∀ (h : Finset X → ℝ) (W₁ : Finset X),
          Exp (insert x V₀) b (fun W₂ => h (W₁ ∪ W₂))
            = (1 - b) * Exp V₀ b (fun W₂ => h (W₁ ∪ W₂))
              + b * Exp V₀ b (fun W₂ => h (insert x (W₁ ∪ W₂))) := by
        intro h W₁
        rw [Exp_insert hx]
        simp only [Finset.union_insert]
      have inner2 : ∀ A : Finset X,
          Exp (insert x V₀) b (fun W₂ => f (insert x (A ∪ W₂)))
            = Exp V₀ b (fun W₂ => f (insert x (A ∪ W₂))) := by
        intro A
        rw [Exp_insert hx]
        simp only [Finset.union_insert, Finset.insert_idem]
        ring
      rw [Exp_insert hx]
      simp only [inner1, Finset.insert_union, inner2]
      rw [Exp_linear V₀ a (1 - b) b, ih f, ih (fun U => f (insert x U)), Exp_insert hx]
      ring

import RequestProject.KeyLemma

/-!
# The Park–Pham iteration

Repeatedly applying the key lemma, halving the bound on the edge sizes each time.
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- Total density after all the rounds used for an `ℓ`-bounded hypergraph. -/
