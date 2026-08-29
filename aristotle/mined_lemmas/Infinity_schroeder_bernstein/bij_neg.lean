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

theorem bij_neg {f : X → Y} {g : Y → X} {x : X} (hx : ¬ Reach f g x) :
    g (bij f g x) = x := by
  have h : bij f g x = Classical.choose (exists_preimage hx) := by
    simp [bij, dif_neg hx]
  rw [h]
  exact Classical.choose_spec (exists_preimage hx)

/-- Reachability is preserved by one step of `g ∘ f`. -/
