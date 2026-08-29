import Mathlib
/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Metric Set
open scoped Real Topology

namespace Frontier

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger) chain
with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (I * k)`. -/

theorem sshOffDiag_ne_zero_iff (v w : ℝ) (hw : 0 ≤ w) :
    (∀ k : ℝ, sshOffDiag v w k ≠ 0) ↔ |v| ≠ w := by
  constructor
  · intro h hv
    rcases eq_or_lt_of_le hw with hw0 | hw0
    · have hv0 : v = 0 := by
        have hva : |v| = 0 := by rw [hv, ← hw0]
        exact abs_eq_zero.mp hva
      exact h 0 (by simp [sshOffDiag, hv0, ← hw0])
    · rcases (abs_eq (le_of_lt hw0)).mp hv with hvw | hvw
      · refine h π ?_
        simp only [sshOffDiag, hvw]
        rw [show (Complex.I * ((π : ℝ) : ℂ)) = (π : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
        ring
      · refine h 0 ?_
        simp [sshOffDiag, hvw]
  · intro hv k hk
    apply hv
    have hvz : (v : ℂ) = -((w : ℂ) * Complex.exp (Complex.I * k)) := by
      have h0 : (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * k) = 0 := hk
      linear_combination h0
    have hnorm : ‖(v : ℂ)‖ = ‖(w : ℂ) * Complex.exp (Complex.I * k)‖ := by rw [hvz, norm_neg]
    simpa [Complex.norm_exp, abs_of_nonneg hw] using hnorm

/-- Away from the origin the map `z ↦ z⁻¹` is holomorphic; on a closed disc missing the origin
this gives the hypotheses needed for Cauchy's theorem. -/
