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

lemma exists_belyi_base {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ B : ℚ[X], 1 ≤ B.natDegree ∧ B.eval 0 = 0 ∧ B.eval 1 = 0 ∧ B.eval lam = 1 ∧
      (∀ w : ℂ, aeval w (derivative B) = 0 → aeval w B = 0 ∨ aeval w B = 1) := by
  obtain ⟨m, n, hm, hn, hlam0⟩ := exists_num_den h0 h1
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hlam : lam = ((M : ℚ) + 1) / ((M : ℚ) + (N : ℚ) + 2) := by
    rw [hlam0]; push_cast; ring_nf
  clear hlam0
  set D : ℚ := (M : ℚ) + (N : ℚ) + 2 with hD
  have hDpos : 0 < D := by positivity
  set c : ℚ := D ^ (M + N + 2) / (((M : ℚ) + 1) ^ (M + 1) * ((N : ℚ) + 1) ^ (N + 1)) with hc
  set B : ℚ[X] := C c * X ^ (M + 1) * (1 - X) ^ (N + 1) with hB
  have hcne : c ≠ 0 := by rw [hc]; positivity
  have hB0 : B.eval 0 = 0 := by simp [hB]
  have hB1 : B.eval 1 = 0 := by simp [hB]
  have h1l : 1 - lam = ((N : ℚ) + 1) / D := by rw [hlam]; field_simp; rw [hD]; ring
  have expand : B.eval lam = c * lam ^ (M + 1) * (1 - lam) ^ (N + 1) := by simp [hB]
  have hBlam : B.eval lam = 1 := by
    rw [expand, h1l, hlam, div_pow, div_pow, hc]
    have hpow : D ^ (M + 1) * D ^ (N + 1) = D ^ (M + N + 2) := by rw [← pow_add]; ring_nf
    field_simp
    ring
  refine ⟨B, one_le_natDegree_of_eval_ne (x := 0) (y := lam) (by rw [hB0, hBlam]; norm_num),
    hB0, hB1, hBlam, ?_⟩
  have hderiv : derivative B = C c * X ^ M * (1 - X) ^ N * (C ((M : ℚ) + 1) - C D * X) := by
    rw [hB, hD]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_C, derivative_one,
      derivative_sub, zero_mul, zero_add, mul_one, Nat.add_sub_cancel]
    push_cast
    simp only [C_add, C_1, map_ofNat]
    ring
  intro w hw
  rw [hderiv, hD] at hw
  simp only [map_mul, map_sub, map_pow, map_one, aeval_C, aeval_X, eq_ratCast,
    mul_eq_zero, sub_eq_zero, pow_eq_zero_iff'] at hw
  push_cast at hw
  have hcast0 : aeval (0 : ℂ) B = ((B.eval 0 : ℚ) : ℂ) := by simpa using aeval_ratCast 0 B
  have hcast1 : aeval (1 : ℂ) B = ((B.eval 1 : ℚ) : ℂ) := by simpa using aeval_ratCast 1 B
  have hcastl : aeval ((lam : ℚ) : ℂ) B = ((B.eval lam : ℚ) : ℂ) := aeval_ratCast lam B
  have hDne : ((M : ℂ) + (N : ℂ) + 2) ≠ 0 := by
    have h2 : (((D : ℚ)) : ℂ) ≠ 0 := mod_cast (ne_of_gt hDpos)
    rw [hD] at h2
    push_cast at h2
    exact h2
  rcases hw with (h | h) | h
  · rcases h with h | h
    · exact absurd (mod_cast h : (c : ℚ) = 0) hcne
    · left
      rw [h.1, hcast0, hB0]; norm_num
  · left
    rw [← h.1, hcast1, hB1]; norm_num
  · right
    have hwlam : w = ((lam : ℚ) : ℂ) := by
      rw [hlam, hD]
      push_cast
      field_simp
      linear_combination -h
    rw [hwlam, hcastl, hBlam]; norm_num

/-- Given three rationals `a < b < c` there is a polynomial with rational coefficients sending
`a, c` to `0`, `b` to `1`, and all of whose critical values lie in `{0, 1}`. -/
