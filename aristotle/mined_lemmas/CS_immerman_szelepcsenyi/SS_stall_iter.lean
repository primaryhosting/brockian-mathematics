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


lemma SS_stall_iter (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    ∀ d, SS r s x (i + d) = SS r s x (i + d + 1) := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have := SS_stall r s x (i + d) ih
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e]
      exact this

