/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius

namespace Math

/-- If `ζ` is a primitive `8`-th root of unity in `ℂ`, then `ζ ^ 4 = -1`. -/

lemma moebius_eight : μ 8 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  have h2 := hs 2 ⟨2, by norm_num⟩
  norm_num at h2

/-- **The sum of the primitive 8-th roots of unity equals `μ(8)`.** -/
