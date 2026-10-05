import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Bb_nonneg {L : ℝ} (hL : 0 < L) : ∀ ℓ : ℕ, 0 ≤ Bb L ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    match ℓ with
    | 0 => simp [Bb]
    | (n + 1) =>
      rw [Bb_succ]
      have h1 := Aterm_nonneg hL (n + 1)
      have h2 := ih ((n + 1) / 2) (by omega)
      linarith

