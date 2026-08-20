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


lemma RS_stab (i : ℕ) {v : Fin m} (h : RS r s x i v) : RS r s x (m + 1) v := by
  obtain ⟨i0, hi0, hstall⟩ := exists_stall r s x
  rcases Nat.lt_or_ge (m + 1) i with hlt | hge
  · have e1 : SS r s x i = SS r s x i0 := by
      have : i = i0 + (i - i0) := by omega
      rw [this]; exact SS_stall_forever r s x i0 hstall _
    have e2 : SS r s x (m + 1) = SS r s x i0 := by
      have : m + 1 = i0 + (m + 1 - i0) := by omega
      rw [this]; exact SS_stall_forever r s x i0 hstall _
    have : v ∈ SS r s x i := h
    rw [e1, ← e2] at this
    exact this
  · exact RS_mono r s x hge h

/-- Reachability is exactly membership in the level set of index `m + 1`. -/
