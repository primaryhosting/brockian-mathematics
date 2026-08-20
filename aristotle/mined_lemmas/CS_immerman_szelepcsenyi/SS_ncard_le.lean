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


lemma SS_ncard_le (i : ℕ) : (SS r s x i).ncard ≤ m := by
  have h1 : (SS r s x i).ncard ≤ (Set.univ : Set (Fin m)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  simpa [Set.ncard_univ] using h1

/-- If two consecutive level sets agree, so do the next two. -/
