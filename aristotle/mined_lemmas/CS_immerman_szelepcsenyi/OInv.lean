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


def OInv (i c j c' : Fin (m + 2)) : Prop :=
  (c : ℕ) = cnt (RS r s x (i : ℕ)) ∧ (c' : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) (j : ℕ)

/-- Vertices of level `I` that neither are `v` nor have an edge to `v`. -/
