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


lemma card_St (m : ℕ) : Fintype.card (St m) ≤ 6 * (m + 2) ^ 9 := by
  have := Fintype.card_le_of_injective _ (enc_inj (m := m))
  simpa [Fintype.card_prod, pow_succ, Nat.mul_assoc] using this

/-! ### The transitions -/

/-- The guarded transitions of the counting machine. -/
