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


lemma SS_stall_forever (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    ∀ d, SS r s x (i + d) = SS r s x i := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e, ← SS_stall_iter r s x i h d, ih]

/-- As long as the level sets keep growing, their cardinality grows. -/
