import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma fiedler_le_norm_one_sub_char {k : ZMod n} (hk : k ≠ 0) :
    2 - 2 * Real.cos (2 * Real.pi / n) ≤ ‖1 - ZMod.stdAddChar k‖ ^ 2 := by
  rw [norm_one_sub_sq (norm_stdAddChar k), stdAddChar_re]
  have hlt : k.val < n := ZMod.val_lt k
  have hpos : 1 ≤ k.val := by
    rcases Nat.eq_zero_or_pos k.val with h | h
    · exact absurd ((ZMod.val_eq_zero k).mp h) hk
    · exact h
  have := cos_le_cos_base (n := n) (m := k.val) hpos (by omega)
  linarith

end Gap

section LowerBound

open scoped ZMod

variable {n : ℕ} [NeZero n]

/-- Spectral gap inequality (complex form): for `u : ZMod n → ℂ` with vanishing mean,
the Dirichlet energy is at least the Fiedler value times the squared norm. -/
