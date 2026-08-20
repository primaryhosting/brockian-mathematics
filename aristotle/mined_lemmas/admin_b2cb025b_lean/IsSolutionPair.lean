import Mathlib

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

import Mathlib

/-!
# Weyl theory: the deficiency space of a Schrödinger operator is represented by ODE solutions

For a real (or complex) potential `q : ℝ → ℂ` the formal differential expression
`τ u = -u'' + q u` gives rise to a maximal operator on `L²(ℝ)`.  For `z : ℂ` the
*deficiency space* at `z` is the kernel of `τ - z` inside the maximal domain.

This file proves the two basic facts of Weyl's theory in this setting:

* the deficiency space is exactly the set of square integrable solutions of the
  ordinary differential equation `u'' = (q - z) u`;
* the space of *all* solutions of that ODE has dimension at most `2`, hence the
  deficiency index of the operator is at most `2`.

The second statement requires a regularity assumption on `q`; the (weak) form used here is
that `q` is bounded on every compact interval (`WeakRegularity`).  Continuous potentials
satisfy it (`WeakRegularity.of_continuous`).
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set

/-- **Weak regularity** of a potential: `q` is bounded on each compact interval.
This is weaker than continuity, and it is all that the uniqueness theory for the
associated ODE requires. -/

theorem IsSolutionPair.eq_zero_of_init {q : ℝ → ℂ} (hq : WeakRegularity q) {z : ℂ}
    {u v : ℝ → ℂ} (h : IsSolutionPair q z u v) (hu0 : u 0 = 0) (hv0 : v 0 = 0) : u = 0 := by
  funext x
  set a : ℝ := -(|x| + 1) with ha
  set b : ℝ := |x| + 1 with hb
  obtain ⟨C, hC⟩ := hq a b
  set V : ℝ → (ℂ × ℂ) → (ℂ × ℂ) := fun t w => (w.2, (q t - z) * w.1) with hV
  set K : NNReal := ⟨max 1 (C + ‖z‖), le_trans zero_le_one (le_max_left _ _)⟩ with hK
  have hKcoe : (K : ℝ) = max 1 (C + ‖z‖) := rfl
  have hbound : ∀ t ∈ Set.Ioo a b, ‖q t - z‖ ≤ (K : ℝ) := by
    intro t ht
    have h1 : ‖q t‖ ≤ C := hC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h2 : ‖q t - z‖ ≤ ‖q t‖ + ‖z‖ := norm_sub_le _ _
    rw [hKcoe]
    exact le_trans h2 (le_trans (by linarith) (le_max_right _ _))
  have hlip : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (V t) Set.univ := by
    intro t ht
    rw [lipschitzOnWith_univ]
    refine LipschitzWith.of_dist_le_mul fun w₁ w₂ => ?_
    have hd : dist ((q t - z) * w₁.1) ((q t - z) * w₂.1) = ‖q t - z‖ * dist w₁.1 w₂.1 := by
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    have h1 : (0 : ℝ) ≤ dist w₁.1 w₂.1 := dist_nonneg
    have h2 : (0 : ℝ) ≤ dist w₁.2 w₂.2 := dist_nonneg
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by rw [hKcoe]; exact le_max_left _ _
    have hqK := hbound t ht
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [hV, hd]
    refine max_le ?_ ?_
    · calc dist w₁.2 w₂.2 ≤ (K : ℝ) * dist w₁.2 w₂.2 := by nlinarith
        _ ≤ (K : ℝ) * max (dist w₁.1 w₂.1) (dist w₁.2 w₂.2) := by
              have := le_max_right (dist w₁.1 w₂.1) (dist w₁.2 w₂.2)
              nlinarith
    · calc ‖q t - z‖ * dist w₁.1 w₂.1 ≤ (K : ℝ) * dist w₁.1 w₂.1 := by nlinarith
        _ ≤ (K : ℝ) * max (dist w₁.1 w₂.1) (dist w₁.2 w₂.2) := by
              have := le_max_left (dist w₁.1 w₂.1) (dist w₁.2 w₂.2)
              nlinarith
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h0mem : (0 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> [linarith [ha]; linarith [hb]]
  have hxmem : x ∈ Set.Ioo a b := by
    constructor
    · have := neg_abs_le x; simp only [ha]; linarith
    · have := le_abs_self x; simp only [hb]; linarith
  have hf : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun t => (u t, v t)) (V t (u t, v t)) t ∧ (u t, v t) ∈ (Set.univ : Set (ℂ × ℂ)) :=
    fun t _ => ⟨(h.deriv_left t).prodMk (h.deriv_right t), Set.mem_univ _⟩
  have hg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (V t (0, 0)) t ∧
        ((0 : ℂ), (0 : ℂ)) ∈ (Set.univ : Set (ℂ × ℂ)) := by
    intro t _
    refine ⟨?_, Set.mem_univ _⟩
    have : V t (0, 0) = (0, 0) := by simp [hV]
    rw [this]
    exact hasDerivAt_const t _
  have key := ODE_solution_unique_of_mem_Ioo hlip h0mem hf hg (by simp [hu0, hv0])
  have := key hxmem
  simpa using congrArg Prod.fst this

/-- The map sending a solution to its initial data `(u 0, u' 0)`. -/
