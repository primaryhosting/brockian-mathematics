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


lemma SS_ncard_growth (i : ℕ) (hgrow : ∀ j < i, SS r s x j ≠ SS r s x (j + 1)) :
    i + 1 ≤ (SS r s x i).ncard := by
  induction i with
  | zero => simp [SS_zero]
  | succ i ih =>
      have hih : i + 1 ≤ (SS r s x i).ncard := ih (fun j hj => hgrow j (by omega))
      have hss : SS r s x i ⊂ SS r s x (i + 1) :=
        ⟨SS_subset_succ r s x i, fun hsup =>
          hgrow i (by omega) (Set.Subset.antisymm (SS_subset_succ r s x i) hsup)⟩
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      omega

