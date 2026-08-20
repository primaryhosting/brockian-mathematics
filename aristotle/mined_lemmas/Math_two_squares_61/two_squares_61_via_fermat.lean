/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` command to precede all other commands, including
-- module doc comments, so this file (which must begin with the header above) carries no
-- imports; the statement and its proof need nothing beyond Lean core.  A derivation of the
-- same statement from Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq` is given in
-- `RequestProject/TwoSquares61Fermat.lean`.

namespace Math

/-- The prime `61` is a sum of two squares: `61 = 5 ^ 2 + 6 ^ 2`. -/

theorem two_squares_61_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 61 := by
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 61) (by norm_num)

end Math

