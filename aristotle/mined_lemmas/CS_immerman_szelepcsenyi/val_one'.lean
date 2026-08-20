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


lemma val_one' (m : ℕ) : ((1 : Fin (m + 2)) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt]

variable {n m : ℕ} (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool)

/-! ### The individual transitions -/

