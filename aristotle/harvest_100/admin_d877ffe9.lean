import Mathlib
import RequestProject.Main

/-!
# Two Squares 5 — Mathlib restatement

This companion file restates `Math.two_squares_5` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to occur before any other
command, including module documentation. Since this file is required to *begin* with the
header comment above, it cannot contain an `import` line, and is therefore stated and
proved using only Lean 4 core (which is a strict subset of the Mathlib environment).
The companion file `RequestProject/MathlibVersion.lean` imports Mathlib and restates the
same result using `Nat.Prime`.
-/

namespace Math

/-- **Two squares for 5.**  The number `5` is prime — here spelled out as
`2 ≤ 5` together with the fact that every divisor of `5` is `1` or `5` — and it is a sum
of two squares, namely `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5 :
    (2 ≤ 5 ∧ ∀ m : Nat, m ∣ 5 → m = 1 ∨ m = 5) ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 2, by decide⟩
  intro m hm
  have h : m ≤ 5 := Nat.le_of_dvd (by decide) hm
  have h6 : m < 6 := by omega
  revert h6 hm
  revert m
  decide

end Math

