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

theorem exists_seq_schwartz_tendsto
    (u : (harmonicOscillatorPMap.closure).domain) :
    ∃ g : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n => schwartzToL2 (g n)) atTop (𝓝 ((u : L2R))) ∧
      Tendsto (fun n => oscillatorCoreMap (g n)) atTop
        (𝓝 (harmonicOscillatorPMap.closure u)) := by
  have hcl : harmonicOscillatorPMap.IsClosable :=
    isClosable_of_isSymmetric harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense
  obtain ⟨w, hw1, hw2⟩ := exists_seq_tendsto_closure hcl u
  choose g hg1 hg2 using fun n => exists_schwartz_of_mem_domain (w n)
  refine ⟨g, ?_, ?_⟩
  · simpa only [hg1] using hw1
  · simpa only [hg2] using hw2

/-- Domain elements with small norm and small image lie in the closure of the
good set. -/
