/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem isClosed_shiftedRange_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ} (hz : |z.im| = 1) :
    IsClosed ((shiftedRange T.closure z : Submodule ℂ H) : Set H) := by
  have hcl := isClosable_of_isSymmetric hsym hd
  have hclosed : T.closure.IsClosed := hcl.closure_isClosed
  have hsymc := isSymmetric_closure hsym hd
  rw [← isSeqClosed_iff_isClosed]
  intro y ylim hy hlim
  choose v hv using fun n => (mem_shiftedRange_iff T.closure z (y n)).mp (hy n)
  have hbound : ∀ m n : ℕ, ‖(v m : H) - (v n : H)‖ ≤ ‖y m - y n‖ := by
    intro m n
    have h := norm_le_norm_shifted hsymc hz (v m - v n)
    have hcoe : ((v m - v n : T.closure.domain) : H) = (v m : H) - (v n : H) := rfl
    have hmap : T.closure (v m - v n) = T.closure (v m) - T.closure (v n) :=
      LinearPMap.map_sub _ _ _
    rw [hcoe, hmap] at h
    have hexp : T.closure (v m) - T.closure (v n) - z • ((v m : H) - (v n : H))
        = y m - y n := by
      rw [smul_sub, ← hv m, ← hv n]; abel
    rwa [hexp] at h
  -- `v` is Cauchy, hence converges
  have hyc : CauchySeq y := hlim.cauchySeq
  have hvc : CauchySeq (fun n => (v n : H)) := by
    rw [Metric.cauchySeq_iff] at hyc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hbound m n
    rw [dist_eq_norm]
    calc ‖(v m : H) - (v n : H)‖ ≤ ‖y m - y n‖ := this
      _ = dist (y m) (y n) := (dist_eq_norm _ _).symm
      _ < ε := hN m hm n hn
  obtain ⟨vlim, hvlim⟩ := cauchySeq_tendsto_of_complete hvc
  -- the images converge too
  have hTv : Tendsto (fun n => T.closure (v n)) atTop (𝓝 (ylim + z • vlim)) := by
    have h1 : ∀ n, T.closure (v n) = y n + z • (v n : H) := by
      intro n; rw [← hv n]; abel
    have h2 : Tendsto (fun n => y n + z • (v n : H)) atTop (𝓝 (ylim + z • vlim)) :=
      hlim.add ((hvlim.const_smul z))
    simpa only [h1] using h2
  -- the graph is closed, so the limit is in the domain
  have hgraph : ((vlim : H), ylim + z • vlim) ∈ T.closure.graph := by
    have hmem : ∀ n, ((v n : H), T.closure (v n)) ∈ T.closure.graph :=
      fun n => T.closure.mem_graph (v n)
    have hlimprod : Tendsto (fun n => ((v n : H), T.closure (v n))) atTop
        (𝓝 ((vlim : H), ylim + z • vlim)) := hvlim.prodMk_nhds hTv
    exact hclosed.mem_of_tendsto hlimprod (Filter.Eventually.of_forall hmem)
  obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff T.closure).mp hgraph
  refine (mem_shiftedRange_iff T.closure z ylim).mpr ⟨w, ?_⟩
  rw [hw2, hw1]
  simp

/-- Both shifted ranges of the closure are everything, under essential
self-adjointness. -/
