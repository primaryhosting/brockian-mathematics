import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_nonneg {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : Finset X → ℝ}
    (h : ∀ A ∈ V.powerset, 0 ≤ f A) : 0 ≤ Exp V p f := by
  have := Exp_mono (V := V) (p := p) hp0 hp1 (f := fun _ => (0:ℝ)) (g := f) (by simpa using h)
  simpa [Exp_const] using this

