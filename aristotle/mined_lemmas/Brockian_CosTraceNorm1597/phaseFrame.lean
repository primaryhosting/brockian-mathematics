/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (x i - x j)` attached to phases `x : Fin n → ℝ`. -/

noncomputable def phaseFrame {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  fun k i => if k = 0 then Real.cos (x i) else Real.sin (x i)

