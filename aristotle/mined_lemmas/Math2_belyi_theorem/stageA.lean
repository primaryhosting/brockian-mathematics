/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Belyi's theorem is formalized in its genus-zero (polynomial) form, which is the arithmetic heart
of the theorem: the "curve" is the projective line together with a finite set `S` of marked
complex points, and a Belyi map is given by a polynomial `f ∈ ℚ[X]` — viewed as a map
`ℙ¹ → ℙ¹` defined over `ℚ` for which `∞` is totally ramified over `∞`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` (i.e. all elements of
`S` are algebraic over `ℚ`) if and only if there is a nonconstant such `f` which maps `S` into
`{0, 1}` and all of whose critical values lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`.

The easy direction is elementary. The hard direction is Belyi's algorithm, carried out here in
two stages:

* `Math2.stageA`: composing with minimal polynomials, one finds a nonconstant `f ∈ ℚ[X]` for
  which the images of the marked points and all critical values are rational. Termination is
  measured by `Math2.muA`, a sum of factorials of the degrees of the algebraic numbers involved.
* `Math2.stageB`: a finite set of rationals is collapsed into `{0, 1}` by repeatedly composing
  with the polynomials `c · x^m (1-x)^n` (after an affine change of coordinates), each step
  strictly decreasing the number of relevant rational values.
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

set_option grind.warning false

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Critical points and critical values -/

/-- The critical points in `ℂ` of a polynomial with rational coefficients. -/

theorem stageA : ∀ (N : ℕ) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) → muA S ≤ N →
    ∃ (f : ℚ[X]) (T : Finset ℚ), 1 ≤ f.natDegree ∧
      (∀ z ∈ S, ∃ t ∈ T, aeval z f = (t : ℂ)) ∧
      (∀ w : ℂ, aeval w (derivative f) = 0 → ∃ t ∈ T, aeval w f = (t : ℂ)) := by
  intro N
  induction N with
  | zero =>
    intro S _ hmu
    have hSempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have hle : (degQ z + 1)! ≤ muA S :=
        Finset.single_le_sum (f := fun z => (degQ z + 1)!) (fun i _ => Nat.zero_le _) hz
      have := Nat.factorial_pos (degQ z + 1)
      omega
    refine ⟨X, ∅, by simp, ?_, ?_⟩
    · intro z hz; rw [hSempty] at hz; simp at hz
    · intro w hw; simp at hw
  | succ N ih =>
    intro S hS hmu
    by_cases hall : ∀ z ∈ S, degQ z ≤ 1
    · refine ⟨X, S.image ratOf, by simp, ?_, ?_⟩
      · intro z hz
        exact ⟨ratOf z, Finset.mem_image_of_mem _ hz, by
          simpa using eq_ratOf_of_degQ_le_one (hS z hz) (hall z hz)⟩
      · intro w hw; simp at hw
    · push_neg at hall
      obtain ⟨s0, hs0S, hs0d⟩ := hall
      have hd2 : 2 ≤ degQ s0 := hs0d
      set mp : ℚ[X] := minpoly ℚ s0 with hmp
      have hmp1 : 1 ≤ mp.natDegree := by
        have hdegs0 : degQ s0 = mp.natDegree := rfl
        omega
      set S' : Finset ℂ := S.image (fun z => aeval z mp) ∪ critVals mp with hS'def
      have halg' : ∀ y ∈ S', IsAlgebraic ℚ y := by
        intro y hy
        rw [hS'def, Finset.mem_union] at hy
        rcases hy with hy | hy
        · rw [Finset.mem_image] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          exact isAlgebraic_aeval (hS z hz) mp
        · rw [critVals, Finset.mem_image] at hy
          obtain ⟨w, hw, rfl⟩ := hy
          exact isAlgebraic_aeval (isAlgebraic_of_mem_critPts hmp1 hw) mp
      have hmu' : muA S' ≤ N := by
        have hstep : muA S' < muA S := muA_step hS hs0S hd2
        omega
      obtain ⟨f', T', hf'1, hf'S, hf'C⟩ := ih S' halg' hmu'
      refine ⟨f'.comp mp, T', ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_comp]
        calc 1 = 1 * 1 := by norm_num
          _ ≤ f'.natDegree * mp.natDegree := Nat.mul_le_mul hf'1 hmp1
      · intro z hz
        have hmem : aeval z mp ∈ S' := by
          rw [hS'def, Finset.mem_union]; exact Or.inl (Finset.mem_image_of_mem _ hz)
        obtain ⟨t, htT, ht⟩ := hf'S _ hmem
        exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩
      · intro w hw
        rw [Polynomial.derivative_comp, map_mul, mul_eq_zero] at hw
        rcases hw with hw | hw
        · have hwc : w ∈ critPts mp := mem_critPts hmp1 hw
          have hmem : aeval w mp ∈ S' := by
            rw [hS'def, Finset.mem_union]
            exact Or.inr (Finset.mem_image_of_mem _ hwc)
          obtain ⟨t, htT, ht⟩ := hf'S _ hmem
          exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩
        · rw [Polynomial.aeval_comp] at hw
          obtain ⟨t, htT, ht⟩ := hf'C _ hw
          exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩

/-! ## Belyi's theorem in genus zero -/

/-- **Belyi's theorem** (polynomial / genus zero form).

A finite set `S` of complex numbers consists of algebraic numbers (i.e. the marked points are
defined over `ℚ̄`) if and only if there is a nonconstant map `f : ℙ¹ → ℙ¹` defined over `ℚ`
(here given by a polynomial, so that `∞` is totally ramified over `∞`) which sends `S` into
`{0, 1}` and whose critical values all lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`. -/
