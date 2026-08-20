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


lemma not_next (I : ℕ) (v : Fin m) (N : ℕ) (hN : N = cnt (RS r s x I))
    (hle : N ≤ cntb (NPred r s x I v) m) : ¬ RS r s x (I + 1) v := by
  rw [cntb_full] at hle
  have h : cnt (RS r s x I) ≤ cnt (fun u => RS r s x I u ∧ ¬(u = v ∨ Rl r x u v)) := by
    rw [← hN]; exact hle
  have hall := forall_of_cnt_le _ _ h
  rintro ⟨u, hu, hstep⟩
  exact (hall u hu) hstep

