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
# Deficiency indices, Weyl's criterion and essential self-adjointness

This file develops, from first principles, the *deficiency index* (von Neumann) criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space,
and applies it to a Schrödinger operator.

## Main definitions

* `Brockian.Weyl.DeficiencyODE.EssentiallySelfAdjoint`: a densely defined operator `A` is
  essentially self-adjoint when its adjoint `A†` is self-adjoint (equivalently, when the closure
  of `A` is self-adjoint).
* `Brockian.Weyl.DeficiencyODE.WeakRegularity`: the *weak regularity* (Weyl limit-point) condition:
  both deficiency subspaces `ker (A† ∓ i)` are trivial.

## Main results

* `Brockian.Weyl.DeficiencyODE.essentiallySelfAdjoint_of_weakRegularity`: the abstract
  von Neumann criterion; a densely defined symmetric operator satisfying `WeakRegularity` is
  essentially self-adjoint.
* `Brockian.Weyl.DeficiencyODE.weakRegularity_schrodingerOperator`: the discharge of the
  weak regularity hypothesis for the Schrödinger operator attached to an orthonormal family of
  eigenfunctions with real energies.
* `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity`: the
  resulting **unconditional** essential self-adjointness statement.
-/

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

open LinearPMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An operator is *essentially self-adjoint* when its adjoint is self-adjoint.
For a densely defined symmetric operator this is equivalent to the closure being self-adjoint. -/

lemma exists_seq_tendsto_adjoint (hA : Dense (A.domain : Set H)) (hsym : A.IsFormalAdjoint A)
    (hreg : WeakRegularity A) (u : A.adjoint.domain) :
    ∃ x : ℕ → A.domain, Tendsto (fun n => ((x n : H))) atTop (𝓝 (u : H)) ∧
      Tendsto (fun n => A (x n)) atTop (𝓝 (A.adjoint u)) := by
  classical
  set f : H := A.adjoint u - Complex.I • (u : H) with hf
  have hdense := dense_range_subI hA hreg.2
  -- choose an approximating sequence in the range of `A - i`
  have hchoice : ∀ n : ℕ, ∃ x : A.domain, ‖subI A x - f‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 (hdense f) _ hpos
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    rw [hx, ← dist_eq_norm, dist_comm]
    exact hdist
  choose x hx using hchoice
  -- the images converge to `f`
  have hgf : Tendsto (fun n => subI A (x n)) atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm]
    exact (hx n).le
  have hgcauchy : CauchySeq (fun n => subI A (x n)) := hgf.cauchySeq
  have hsubcoe : ∀ m n : ℕ, subI A (x m) - subI A (x n) = subI A (x m - x n) := by
    intro m n; rw [_root_.map_sub]
  have hxc : CauchySeq (fun n => ((x n : H))) := by
    refine cauchySeq_of_norm_le hgcauchy (fun m n => ?_)
    rw [hsubcoe m n]
    have := norm_le_norm_subI hsym (x m - x n)
    simpa using this
  have hAc : CauchySeq (fun n => A (x n)) := by
    refine cauchySeq_of_norm_le hgcauchy (fun m n => ?_)
    rw [hsubcoe m n]
    have h1 := norm_apply_le_norm_subI hsym (x m - x n)
    rwa [A.map_sub] at h1
  obtain ⟨xl, hxl⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨gl, hgl⟩ := cauchySeq_tendsto_of_complete hAc
  -- the limit lies in the domain of the adjoint
  have hkey : ∀ z : A.domain, ⟪gl, (z : H)⟫ = ⟪xl, A z⟫ := by
    intro z
    have h1 : Tendsto (fun n => ⟪A (x n), (z : H)⟫) atTop (𝓝 ⟪gl, (z : H)⟫) :=
      hgl.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪((x n : H)), A z⟫) atTop (𝓝 ⟪xl, A z⟫) :=
      hxl.inner tendsto_const_nhds
    have h3 : (fun n => ⟪A (x n), (z : H)⟫) = fun n => ⟪((x n : H)), A z⟫ :=
      funext fun n => hsym (x n) z
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  obtain ⟨hxlm, hxlval⟩ := adjoint_mem_apply hA hkey
  -- identify the limit with `u`
  have hlim : gl - Complex.I • xl = f := by
    have : Tendsto (fun n => subI A (x n)) atTop (𝓝 (gl - Complex.I • xl)) := by
      simpa [subI_apply] using hgl.sub (hxl.const_smul Complex.I)
    exact tendsto_nhds_unique this hgf
  have hv : A.adjoint (u - ⟨xl, hxlm⟩) = Complex.I • ((u : H) - xl) := by
    rw [LinearPMap.map_sub, hxlval]
    have : A.adjoint u - Complex.I • (u : H) = gl - Complex.I • xl := by rw [hlim]
    rw [smul_sub]
    linear_combination (norm := module) this
  have hzero : ((u : H) - xl) = 0 := by
    have := hreg.1 (u - ⟨xl, hxlm⟩) (by simpa using hv)
    simpa using this
  have hux : (u : H) = xl := by linear_combination (norm := module) hzero
  refine ⟨x, ?_, ?_⟩
  · rw [hux]; exact hxl
  · have : A.adjoint u = gl := by
      rw [show u = (⟨xl, hxlm⟩ : A.adjoint.domain) from Subtype.ext hux, hxlval]
    rw [this]; exact hgl

/-- Under weak regularity the adjoint of a densely defined symmetric operator is symmetric. -/
