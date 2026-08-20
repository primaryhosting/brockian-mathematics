import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

theorem golden_inv : goldenRatio⁻¹ = goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by nlinarith [golden_sq])

/-- The key scalar identity behind unitarity: `φ⁻¹ ^ 2 + φ⁻¹ = 1`. -/
