/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` command to precede all other
commands in a file, so the mandated header comment above (a module docstring,
which is itself a command) rules out importing Mathlib in this file.  The
development below is therefore self-contained and uses only Lean core.

For reference, in Mathlib this statement follows from Fermat's two-squares
theorem `Nat.Prime.sq_add_sq : p.Prime → p % 4 ≠ 3 → ∃ a b, a ^ 2 + b ^ 2 = p`
applied to `p = 17` (since `17 % 4 = 1`); the explicit witnesses are `1` and `4`.
-/

namespace Math

/-- Primality of a natural number, spelled out without Mathlib:
`p` is at least `2` and its only divisors are `1` and `p`. -/

theorem isPrimeNat_17 : IsPrimeNat 17 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hbounded : ∀ e, e < 18 → (e ∣ 17 → e = 1 ∨ e = 17) := by decide
  exact hbounded d (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)) hd

/-- **The prime `17` is a sum of two squares**: `17 = 1 ^ 2 + 4 ^ 2`. -/
