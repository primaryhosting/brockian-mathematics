/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every command, including module
-- docstrings (`/-! ... -/`), so the header is repeated below as the module docstring.
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Math2

/-- The maximal size of a cap set in `𝔽₃ⁿ`, i.e. of a subset of `(Fin n → ZMod 3)` containing
no three-term arithmetic progression. -/

theorem cap_set_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA ↦ ?_⟩
  have hcard : (Fintype.card (Fin n → ZMod 3) : ℝ) = 3 ^ n := by
    rw [card_space]; push_cast; ring
  have hbound : cornersTheoremBound ε ≤ Fintype.card (Fin n → ZMod 3) := by
    rw [card_space]
    exact hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  by_contra hlt
  push_neg at hlt
  exact roth_3ap_theorem ε hε hbound A (by rw [hcard]; exact hlt.le) hA

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression have
size `o(3ⁿ)`. -/
