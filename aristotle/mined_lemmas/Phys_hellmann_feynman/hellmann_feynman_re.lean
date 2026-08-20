/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- **Key intermediate lemma.** If a curve `ψ : ℝ → E` in a complex inner product space stays on
the unit sphere and is differentiable at `l` with derivative `ψ'`, then
`⟪ψ l, ψ'⟫ + ⟪ψ', ψ l⟫ = 0`, i.e. the velocity is "orthogonal" to the state
(twice the real part of `⟪ψ l, ψ'⟫` vanishes). -/

theorem hellmann_feynman_re
    (H : ℝ → (E →L[ℂ] E)) (psi : ℝ → E) (Ev : ℝ → ℝ)
    (l : ℝ) (H' : E →L[ℂ] E) (psi' : E) (Ev' : ℝ)
    (hH : HasDerivAt H H' l)
    (hpsi : HasDerivAt psi psi' l)
    (hEv : HasDerivAt Ev Ev' l)
    (hsa : ∀ x y : E, (inner ℂ (H l x) y : ℂ) = (inner ℂ x (H l y) : ℂ))
    (heig : ∀ t, H t (psi t) = ((Ev t : ℂ)) • psi t)
    (hnorm : ∀ t, ‖psi t‖ = 1) :
    Ev' = (inner ℂ (psi l) (H' (psi l)) : ℂ).re := by
  rw [← hellmann_feynman H psi Ev l H' psi' Ev' hH hpsi hEv hsa heig hnorm]
  simp

end Phys

