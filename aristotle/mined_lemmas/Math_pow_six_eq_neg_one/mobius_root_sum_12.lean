import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/

theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) (fun z _ => by ring) ?_
    (fun z hz => neg_mem_primitiveRoots_twelve hz) (fun z _ => neg_neg z)
  intro z hz hz0 hcon
  exact hz0 (by linear_combination (-1 / 2 : ℂ) * hcon)

/-- Sanity check: the sum above is over a nonempty set — there are exactly
`φ 12 = 4` primitive `12`-th roots of unity in `ℂ`. -/
