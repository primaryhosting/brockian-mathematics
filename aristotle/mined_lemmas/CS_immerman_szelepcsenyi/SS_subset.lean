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


lemma SS_subset {i j : ℕ} (hij : i ≤ j) : SS r s x i ⊆ SS r s x j :=
  fun _ hv => RS_mono r s x hij hv

