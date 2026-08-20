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


lemma SS_subset_succ (i : ℕ) : SS r s x i ⊆ SS r s x (i + 1) :=
  fun _ hv => RS_mono_one r s x hv

