/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (only Lean's prelude is available), because a
module doc comment such as the header above cannot legally precede an `import` line.
Everything below is therefore developed from scratch: the Cantor–Schröder–Bernstein
back-and-forth construction and its correctness proof.  The only classical ingredient
used is `Classical.choice`.

A Mathlib-flavoured restatement, phrased with `Equiv` (`X ≃ Y`), is derived from the
main theorem in `RequestProject/SchroederBernsteinEquiv.lean`.
-/

namespace Infinity

universe u v

section
variable {X : Type u} {Y : Type v}

/-- `iterate F n x` is the `n`-fold application `F (F (… (F x)))`. -/

theorem bij_injective {f : X → Y} {g : Y → X} (hf : Function.Injective f) :
    Function.Injective (bij f g) := by
  have key : ∀ x x' : X, Reach f g x → ¬ Reach f g x' → bij f g x ≠ bij f g x' := by
    intro x x' hx hx' he
    have h1 : g (bij f g x') = x' := bij_neg hx'
    rw [← he, bij_pos hx] at h1
    exact hx' (h1 ▸ reach_step hx)
  intro x x' he
  by_cases hx : Reach f g x
  · by_cases hx' : Reach f g x'
    · exact hf (by rw [← bij_pos hx, ← bij_pos hx', he])
    · exact absurd he (key x x' hx hx')
  · by_cases hx' : Reach f g x'
    · exact absurd he.symm (key x' x hx' hx)
    · have h1 := bij_neg hx
      rw [he, bij_neg hx'] at h1
      exact h1.symm

