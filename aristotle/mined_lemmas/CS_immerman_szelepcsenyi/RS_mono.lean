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


lemma RS_mono {i j : ℕ} (hij : i ≤ j) {v : Fin m} (h : RS r s x i v) : RS r s x j v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simpa using h
  | succ d ih => exact RS_mono_one r s x ih

