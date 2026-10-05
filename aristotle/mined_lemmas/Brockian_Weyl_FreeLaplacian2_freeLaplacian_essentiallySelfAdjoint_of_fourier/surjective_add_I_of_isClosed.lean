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
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem surjective_add_I_of_isClosed {A : H →ₗ.[ℂ] H} (hclosed : A.IsClosed)
    (hsymm : A.IsFormalAdjoint A) (hdense : Dense (shiftedRange A Complex.I)) (v : H) :
    ∃ w : A.domain, A w + Complex.I • (w : H) = v := by
  classical
  have hclosedRange : IsClosed (shiftedRange A Complex.I) := by
    apply IsSeqClosed.isClosed
    intro f p hf hfp
    choose w hw using hf
    -- the sequence `w` is Cauchy
    have hfCauchy : CauchySeq f := hfp.cauchySeq
    have hwCauchy : CauchySeq fun n => ((w n : H)) := by
      rw [Metric.cauchySeq_iff] at hfCauchy ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hfCauchy ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      have key : ‖((w m : H)) - ((w n : H))‖ ≤ ‖f m - f n‖ := by
        have hsub : f m - f n = A (w m - w n) + Complex.I • ((w m : H) - (w n : H)) := by
          rw [← hw m, ← hw n, A.map_sub]
          simp only [smul_sub]
          abel
        have := norm_le_norm_add_I_smul hsymm (w m - w n)
        simpa [hsub] using this
      calc dist ((w m : H)) ((w n : H)) = ‖((w m : H)) - ((w n : H))‖ := dist_eq_norm _ _
        _ ≤ ‖f m - f n‖ := key
        _ = dist (f m) (f n) := (dist_eq_norm _ _).symm
        _ < ε := hN m hm n hn
    obtain ⟨w₀, hw₀⟩ := cauchySeq_tendsto_of_complete hwCauchy
    have hAw : Tendsto (fun n => A (w n)) atTop (𝓝 (p - Complex.I • w₀)) := by
      have h1 : Tendsto (fun n => f n - Complex.I • ((w n : H))) atTop
          (𝓝 (p - Complex.I • w₀)) := hfp.sub (hw₀.const_smul Complex.I)
      refine h1.congr (fun n => ?_)
      rw [← hw n]
      simp
    have hmem : (w₀, p - Complex.I • w₀) ∈ A.graph := by
      refine hclosed.mem_of_tendsto (hw₀.prodMk_nhds hAw) ?_
      filter_upwards with n
      exact A.mem_graph (w n)
    rw [LinearPMap.mem_graph_iff] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hy1 : (y : H) = w₀ := hy.1
    have hy2 : A y = p - Complex.I • w₀ := hy.2
    refine ⟨y, ?_⟩
    show A y + Complex.I • (y : H) = p
    rw [hy2, hy1]
    abel
  have : shiftedRange A Complex.I = Set.univ := by
    rw [← hclosedRange.closure_eq, hdense.closure_eq]
  have hv : v ∈ shiftedRange A Complex.I := by rw [this]; trivial
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, hw⟩

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
whose ranges `T + i` and `T - i` are dense has self-adjoint adjoint; equivalently, `T` is
essentially self-adjoint. -/
