import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma exists_stall : ∃ i ≤ m, SS r s x i = SS r s x (i + 1) := by
  by_contra hcon
  push_neg at hcon
  have hgrow : ∀ j < m + 1, SS r s x j ≠ SS r s x (j + 1) := by
    intro j hj
    exact hcon j (by omega)
  have h1 : (m + 1) + 1 ≤ (SS r s x (m + 1)).ncard := SS_ncard_growth r s x (m + 1) hgrow
  have h2 := SS_ncard_le r s x (m + 1)
  omega

/-- The level sets stabilise at level `m + 1`. -/
