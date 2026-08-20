import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq

