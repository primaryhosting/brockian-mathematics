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

theorem exists_seq_tendsto_closure {T : H →ₗ.[ℂ] H} (hcl : T.IsClosable)
    (x : T.closure.domain) :
    ∃ u : ℕ → T.domain, Tendsto (fun n => ((u n : H))) atTop (𝓝 (x : H)) ∧
      Tendsto (fun n => T (u n)) atTop (𝓝 (T.closure x)) := by
  have hmem : ((x : H), T.closure x) ∈ T.closure.graph := T.closure.mem_graph x
  rw [← hcl.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hmem
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose v hv1 hv2 using fun n => (LinearPMap.mem_graph_iff T).mp (hw n)
  refine ⟨v, ?_, ?_⟩
  · have h := (continuous_fst.tendsto ((x : H), T.closure x)).comp hlim
    simpa [Function.comp_def, hv1] using h
  · have h := (continuous_snd.tendsto ((x : H), T.closure x)).comp hlim
    simpa [Function.comp_def, hv2] using h

/-- The closure of a densely defined symmetric operator is symmetric. -/
