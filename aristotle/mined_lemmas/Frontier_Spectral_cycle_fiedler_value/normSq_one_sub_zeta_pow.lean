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
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma normSq_one_sub_zeta_pow (hn : n ≠ 0) (k : ℕ) :
    Complex.normSq (1 - zeta n ^ k) = 2 - 2 * Real.cos (2 * Real.pi * k / n) := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    re_zeta_pow hn, im_zeta_pow hn]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi * k / n)
  nlinarith [this]

