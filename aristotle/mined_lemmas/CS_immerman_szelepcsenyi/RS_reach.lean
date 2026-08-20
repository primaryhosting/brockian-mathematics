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


lemma RS_reach {i : ℕ} {v : Fin m} (h : RS r s x i v) :
    Relation.ReflTransGen (Rl r x) s v := by
  induction i generalizing v with
  | zero => exact ((RS_zero r s x v).mp h) ▸ Relation.ReflTransGen.refl
  | succ i ih =>
      obtain ⟨u, hu, hstep⟩ := h
      rcases hstep with rfl | hstep
      · exact ih hu
      · exact (ih hu).tail hstep

/-- Everything reachable lies in some level set. -/
