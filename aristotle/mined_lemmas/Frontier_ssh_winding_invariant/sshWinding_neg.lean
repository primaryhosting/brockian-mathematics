/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Complex Metric intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
model with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (i k)`.  Chiral symmetry forces the Bloch Hamiltonian to have the
form `![![0, h k], ![conj (h k), 0]]`, so the spectral gap is open exactly when `h k ≠ 0`
for all `k`. -/

lemma sshWinding_neg (v w : ℝ) : sshWinding v (-w) = sshWinding v w := by
  unfold sshWinding
  congr 1
  have hshift : ∀ k : ℝ,
      (Complex.I * ((-w : ℝ) : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v (-w) k
        = (Complex.I * (w : ℂ) * Complex.exp (((k + Real.pi : ℝ)) * Complex.I))
            / sshOffDiag v w (k + Real.pi) := by
    intro k
    have hexp : Complex.exp (((k + Real.pi : ℝ) : ℂ) * Complex.I)
        = -Complex.exp ((k : ℂ) * Complex.I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    simp only [sshOffDiag, hexp]
    push_cast
    ring_nf
  calc ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * ((-w : ℝ) : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v (-w) k
      = ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (((k + Real.pi : ℝ)) * Complex.I))
            / sshOffDiag v w (k + Real.pi) :=
        intervalIntegral.integral_congr (fun k _ => hshift k)
    _ = ∫ k in (0 + Real.pi : ℝ)..(2 * Real.pi + Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k :=
        intervalIntegral.integral_comp_add_right
          (fun k : ℝ => (Complex.I * (w : ℂ) * Complex.exp ((k : ℝ) * Complex.I))
            / sshOffDiag v w k) Real.pi
    _ = ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k := by
        have h := (sshIntegrand_periodic v w).intervalIntegral_add_eq Real.pi 0
        simpa [add_comm] using h

/-- **SSH winding invariant.**  For the SSH model with hoppings `v` (intracell) and
`w > 0` (intercell) and an open bulk gap (`|v| ≠ w`), the winding number of the
off-diagonal Bloch element around the origin is an *integer* topological invariant:
it equals `1` in the topological phase `|v| < w` and `0` in the trivial phase `w < |v|`. -/
