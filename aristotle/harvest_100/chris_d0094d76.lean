/-
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace AdditiveComb

/-- **Schur's theorem, instance `S(2) < 5`.**

For every 2-colouring `f : Fin 5 → Bool` of the set `{1, 2, 3, 4, 5}` (where the index `i : Fin 5`
denotes the number `i + 1`) there is a monochromatic Schur triple: elements `x, y, z` of the set
with `x + y = z` and `f x = f y = f z`.  (The solutions `x = y` are allowed, as in the usual
definition of the Schur number.)

Proved by exhaustive finite case analysis over the `2 ^ 5` colourings. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, ((x : ℕ) + 1) + ((y : ℕ) + 1) = ((z : ℕ) + 1) ∧ f x = f y ∧ f y = f z := by
  revert f
  decide

/-- The same statement phrased for a colouring `c : ℕ → Bool` of the integers `1, …, 5`. -/
theorem schur_five_nat (c : ℕ → Bool) :
    ∃ x ∈ Finset.Icc 1 5, ∃ y ∈ Finset.Icc 1 5, ∃ z ∈ Finset.Icc 1 5,
      x + y = z ∧ c x = c y ∧ c y = c z := by
  obtain ⟨x, y, z, hxyz, hxy, hyz⟩ := schur_five (fun i => c ((i : ℕ) + 1))
  refine ⟨(x : ℕ) + 1, ?_, (y : ℕ) + 1, ?_, (z : ℕ) + 1, ?_, hxyz, hxy, hyz⟩ <;>
    simp only [Finset.mem_Icc] <;>
    exact ⟨by omega, by have := x.isLt; have := y.isLt; have := z.isLt; omega⟩

end AdditiveComb

