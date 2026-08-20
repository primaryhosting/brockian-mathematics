/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-- The subgroup `2A` of an additive commutative group `A`. -/

theorem int_fg_via_descent : AddGroup.FG ℤ := by
  refine descent_of_height (fun n : ℤ => ((n : ℝ)) ^ 2) ?_ ?_ ?_ ?_
  · intro C
    refine Set.Finite.subset (Set.finite_Icc (-(⌈|C|⌉)) ⌈|C|⌉) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have h1 : ((n : ℝ)) ^ 2 ≤ (⌈|C|⌉ : ℝ) := le_trans (le_trans hn (le_abs_self C)) (Int.le_ceil _)
    have h2 : n ^ 2 ≤ ⌈|C|⌉ := by exact_mod_cast h1
    have h3 : |n| ≤ n ^ 2 := by
      rcases eq_or_ne n 0 with h | h
      · simp [h]
      · have : 1 ≤ |n| := Int.one_le_abs (by omega)
        nlinarith [sq_abs n, abs_nonneg n]
    have h4 := abs_le.mp (le_trans h3 h2)
    simp only [Set.mem_Icc]
    omega
  · intro Q
    refine ⟨2 * (Q : ℝ) ^ 2, fun P => ?_⟩
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ)), sq_nonneg ((P : ℝ) + (Q : ℝ))]
  · refine ⟨0, fun P => ?_⟩
    push_cast
    ring_nf
    nlinarith [sq_nonneg ((P : ℝ))]
  · have heq : twoSubgroup ℤ = AddSubgroup.zmultiples ((2 : ℕ) : ℤ) := by
      ext x
      simp only [mem_twoSubgroup_iff, AddSubgroup.mem_zmultiples_iff, smul_eq_mul]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, by push_cast; ring⟩
      · rintro ⟨k, rfl⟩; exact ⟨k, by push_cast; ring⟩
    rw [heq]
    exact Finite.of_equiv (ZMod 2) (Int.quotientZMultiplesNatEquivZMod 2).symm.toEquiv

/-- **Mordell's theorem** (finite generation of the Mordell–Weil group), as a Lean-checked
reduction to its two standard inputs:

* `weakMordellWeil` : for every elliptic curve over `ℚ`, the quotient `E(ℚ)/2E(ℚ)` is finite;
* `heightTheory` : every such curve carries a height function on its rational points with the
  three standard properties (finiteness of bounded-height sets, quasi-doubling under
  translation, quasi-quadrupling under duplication).

Given these, the group `E(ℚ)` of rational points of any elliptic curve over `ℚ` is finitely
generated. -/
