import Mathlib

/-!
# Two Squares 37 — via Mathlib's Fermat two-squares theorem

Companion to `RequestProject/Math.lean`.  The main target `Math.two_squares_37`
is stated and proved there without any imports (so that the required header
comment can begin the file); here we record the same existence statement as a
consequence of Mathlib's `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `37` is a sum of two squares, derived from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`) applied to the prime `37 ≡ 1 [MOD 4]`. -/

theorem two_squares_37_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 37) (by norm_num)

end Math

/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Every divisor of `37` below `38` is `1` or `37` (a finite check). -/
