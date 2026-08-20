import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem exists_poly_of_dioph (p : ℕ → Prop) (hd : Dioph {v : Fin2 1 → ℕ | p (v Fin2.fz)}) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ), ∀ a : ℕ,
      (∃ x : Fin n → ℕ, MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) P = 0) ↔ p a := by
  classical
  obtain ⟨β, P, hP⟩ := hd
  obtain ⟨q, hq⟩ := exists_mvPolynomial P.isPoly
  obtain ⟨n, f, hfinj, q₀, rfl⟩ := MvPolynomial.exists_fin_rename q
  refine ⟨n, rename (fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i)) q₀, ?_⟩
  intro a
  have key : ∀ w : Fin n → ℕ, ∀ g : Fin2 1 ⊕ β → ℕ, (∀ i, g (f i) = w i) →
      (MvPolynomial.eval (fun i => (w i : ℤ)) q₀ = P g) := by
    intro w g hg
    rw [hq g, eval_rename]
    have : (fun i => ((w i : ℤ))) = ((fun i => (g i : ℤ)) ∘ f) := by
      funext i; simp [Function.comp, hg i]
    rw [this]
  have key2 : ∀ x : Fin n → ℕ,
      MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ))
        (rename (fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i)) q₀)
      = MvPolynomial.eval (fun i => ((Sum.elim (fun _ => a) (fun _ => x i) (f i) : ℕ) : ℤ)) q₀ := by
    intro x
    rw [eval_rename]
    have : ((Fin.cons (a : ℤ) fun i => (x i : ℤ)) ∘
        fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i))
        = fun i => ((Sum.elim (fun _ => a) (fun _ => x i) (f i) : ℕ) : ℤ) := by
      funext i
      rcases h : f i with j | b <;> simp [Function.comp, h]
    rw [this]
  constructor
  · rintro ⟨x, hx⟩
    rw [key2] at hx
    refine (hP (fun _ => a)).2 ?_
    refine ⟨fun b => if h : ∃ i, f i = inr b then x h.choose else 0, ?_⟩
    rw [← key (fun i => Sum.elim (fun _ => a) (fun _ => x i) (f i)) _ ?_]
    · exact hx
    · intro i
      rcases h : f i with j | b
      · simp [h]
      · have hex : ∃ i', f i' = inr b := ⟨i, h⟩
        have hspec := hex.choose_spec
        have : hex.choose = i := hfinj (by rw [hspec, h])
        simp [h, hex, this]
  · intro hpa
    obtain ⟨t, ht⟩ := (hP (fun _ => a)).1 hpa
    refine ⟨fun i => Sum.elim (fun _ => 0) (fun b => t b) (f i), ?_⟩
    rw [key2, key _ (Sum.elim (fun _ => a) t) ?_]
    · exact ht
    · intro i; rcases h : f i with j | b <;> simp

/-! ### Hilbert's tenth problem -/

/-- **Hilbert's tenth problem is undecidable.**  There is a polynomial `P` with integer
coefficients in variables `x₀, x₁, …, xₙ` such that no algorithm decides, for a given natural
number `a`, whether the Diophantine equation `P (a, x₁, …, xₙ) = 0` is solvable. -/
