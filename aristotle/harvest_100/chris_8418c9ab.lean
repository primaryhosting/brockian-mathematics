import Mathlib

/-!
# Pell 8 — infinitely many solutions

A Mathlib-based strengthening of `Math.pell_8`: the equation `x² - 8·y² = 1` has
solutions with arbitrarily large `y`, hence infinitely many integer solutions.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- From one solution of `x² - 8y² = 1` with `x ≥ 1`, `y ≥ 0`, one produces a larger one. -/
theorem pell_8_step {x y : ℤ} (h : x ^ 2 - 8 * y ^ 2 = 1) :
    (3 * x + 8 * y) ^ 2 - 8 * (x + 3 * y) ^ 2 = 1 := by
  ring_nf
  linarith [h]

/-- There are solutions of `x² - 8y² = 1` with `y` arbitrarily large. -/
theorem pell_8_large (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
  induction n with
  | zero => exact ⟨3, 1, by decide, by decide, by decide⟩
  | succ n ih =>
      obtain ⟨x, y, h, hx, hy⟩ := ih
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      refine ⟨3 * x + 8 * y, x + 3 * y, pell_8_step h, by linarith, ?_⟩
      push_cast
      linarith

/-- The set of integer solutions of `x² - 8y² = 1` is infinite. -/
theorem pell_8_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 8 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hb⟩
  obtain ⟨x, y, h, hx, hy⟩ := pell_8_large (b.toNat + 1)
  have := hb (show (x, y) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 8 * p.2 ^ 2 = 1} from h)
  have hy2 : y ≤ b := (Prod.le_def.mp this).2
  have : (b.toNat : ℤ) + 1 ≤ y := by exact_mod_cast hy
  have hbb : b ≤ (b.toNat : ℤ) := Int.self_le_toNat b
  omega

end Math

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- **Pell's equation for `d = 8`.**  The equation `x² - 8·y² = 1` has a nontrivial integer
solution, i.e. a solution with `y ≠ 0` (equivalently, with `x ≠ ±1`): namely `3² - 8·1² = 1`.

The proof needs nothing from `Mathlib`, so this file has no imports; a Mathlib-based
strengthening (infinitely many solutions) is in `RequestProject/Pell8Infinite.lean`. -/
theorem pell_8 : ∃ x y : Int, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by decide, by decide⟩

end Math

