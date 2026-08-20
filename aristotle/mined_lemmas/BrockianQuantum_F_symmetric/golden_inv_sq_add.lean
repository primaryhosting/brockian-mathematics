import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

private lemma golden_inv_sq_add : goldenRatio⁻¹ ^ 2 + goldenRatio⁻¹ = 1 := by
  rw [golden_inv]; nlinarith [golden_sq]

