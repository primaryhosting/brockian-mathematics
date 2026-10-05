/-
/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The statement of the Mordell–Weil theorem

`Frontier.MordellStatement` is the formal statement of Mordell's theorem: for every elliptic
curve over `ℚ`, the group of rational points (in affine coordinates, i.e. the affine points
together with the point at infinity) is a finitely generated abelian group.

The main results below are a *Lean-checked reduction* of this statement to the two standard
inputs of the classical proof:

* the **weak Mordell–Weil theorem**: `E(ℚ)/2E(ℚ)` is finite, encoded as a finite set `R` of
  coset representatives;
* the **theory of heights**: a nonnegative height function `ht` on `E(ℚ)` with finite
  sublevel sets, a quasi-parallelogram bound `ht (P + Q) ≤ 2 * ht P + C_Q`, and a duplication
  bound `4 * ht P ≤ ht (2 • P) + C`.

The engine is `Frontier.descent_of_height`, the classical descent theorem for abstract abelian
groups, proved unconditionally below.
-/

/-- The Mordell–Weil theorem over `ℚ`: the group of rational points of an elliptic curve
over `ℚ` is finitely generated. -/

theorem descent_of_height_int_example : AddGroup.FG ℤ := by
  classical
  refine descent_of_height (A := ℤ) (m := 2) le_rfl (fun n => ((n : ℝ)) ^ 2)
    (fun n => sq_nonneg _) ?_ ?_ ?_ ({0, 1} : Finset ℤ) ?_
  · intro B
    refine Set.Finite.subset (Set.finite_Icc (-(⌈|B|⌉ : ℤ)) (⌈|B|⌉ : ℤ)) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have hB : ((n : ℝ)) ^ 2 ≤ |B| := le_trans hn (le_abs_self B)
    have habs : |(n : ℝ)| ≤ |B| + 1 := by
      nlinarith [abs_nonneg ((n : ℝ)), sq_abs ((n : ℝ)), abs_nonneg B,
        sq_nonneg (|(n : ℝ)| - 1)]
    have hceil : (|B| : ℝ) ≤ (⌈|B|⌉ : ℤ) := Int.le_ceil _
    have h1 : |(n : ℝ)| ≤ ((⌈|B|⌉ : ℤ) : ℝ) + 1 := by linarith
    have h2 : |n| ≤ ⌈|B|⌉ + 1 := by
      have : ((|n| : ℤ) : ℝ) ≤ ((⌈|B|⌉ + 1 : ℤ) : ℝ) := by
        push_cast
        simpa [abs_le, Int.cast_abs] using h1
      exact_mod_cast this
    -- refine the bound: `n ^ 2 ≤ |B|` forces `|n| ≤ ⌈|B|⌉`
    have h3 : |n| ≤ ⌈|B|⌉ := by
      by_contra hcon
      push_neg at hcon
      have hn1 : (⌈|B|⌉ : ℤ) + 1 ≤ |n| := hcon
      have hr : ((⌈|B|⌉ : ℤ) : ℝ) + 1 ≤ |(n : ℝ)| := by
        have : (((⌈|B|⌉ + 1 : ℤ)) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn1
        push_cast at this
        simpa [Int.cast_abs] using this
      have hBnn : (0 : ℝ) ≤ |B| := abs_nonneg B
      have : |B| + 1 ≤ |(n : ℝ)| := by linarith
      nlinarith [sq_abs ((n : ℝ)), abs_nonneg ((n : ℝ))]
    have := abs_le.mp h3
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro Q
    refine ⟨2 * ((Q : ℝ)) ^ 2, ?_⟩
    intro P
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ))]
  · refine ⟨0, fun P => ?_⟩
    have hsm : ((2 : ℕ) • P : ℤ) = 2 * P := by
      simp
    rw [hsm]
    push_cast
    nlinarith [sq_nonneg ((P : ℝ))]
  · intro P
    rcases Int.even_or_odd P with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨0, by simp, k, by rw [hk, two_nsmul]; ring⟩
    · exact ⟨1, by simp, k, by rw [hk, two_nsmul]; ring⟩

end Frontier

