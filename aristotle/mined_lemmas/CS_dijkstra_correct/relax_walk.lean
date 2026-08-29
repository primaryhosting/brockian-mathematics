import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

lemma relax_walk {w : V → V → ℝ≥0∞} {S : Finset V} {d : V → ℝ≥0∞}
    (hrel : ∀ x ∈ S, ∀ y, d y ≤ d x + w x y) :
    ∀ (l : List V) (x : V), InS S x l → d (endpt x l) ≤ d x + wcost w x l := by
  intro l
  induction l with
  | nil => intro x _; simp [endpt, wcost]
  | cons a l ih =>
      rintro x ⟨hx, hrest⟩
      have h1 : d (endpt a l) ≤ d a + wcost w a l := ih a hrest
      have h2 : d a ≤ d x + w x a := hrel x hx a
      calc d (endpt x (a :: l)) = d (endpt a l) := rfl
        _ ≤ d a + wcost w a l := h1
        _ ≤ (d x + w x a) + wcost w a l := by gcongr
        _ = d x + wcost w x (a :: l) := by simp [wcost, add_assoc]

omit [Fintype V] [DecidableEq V] in
/-- Every walk leaving `S` has a prefix, of no greater weight, that stays inside `S`
until its endpoint, which lies outside `S`. -/
