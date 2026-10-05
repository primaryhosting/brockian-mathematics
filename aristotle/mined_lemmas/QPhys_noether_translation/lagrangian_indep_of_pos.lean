/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace QPhys

/-- If a Lagrangian `L q v` is invariant under spatial translations `q ↦ q + s`,
then it does not depend on the position variable at all. -/

lemma lagrangian_indep_of_pos {L : ℝ → ℝ → ℝ}
    (hinv : ∀ s x v, L (x + s) v = L x v) (x v : ℝ) :
    L x v = L 0 v := by
  have h := hinv x 0 v
  simpa using h

/-- Translation invariance forces the "generalized force" `∂L/∂q` to vanish. -/
