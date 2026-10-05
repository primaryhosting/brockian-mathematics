import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_le_of_le {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : Finset X → ℝ}
    {c : ℝ} (h : ∀ A ∈ V.powerset, f A ≤ c) : Exp V p f ≤ c := by
  have := Exp_mono (V := V) (p := p) hp0 hp1 (f := f) (g := fun _ => c) h
  simpa [Exp_const] using this

