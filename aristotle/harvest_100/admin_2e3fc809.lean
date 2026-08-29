/-!
# Sum Three Cubes 42
Category: Frontier — Prime Numbers
Target: Frontier.sum_three_cubes_42
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: the required header above is a module docstring, which Lean requires to precede
any `import` command; consequently this file is self-contained and uses no imports.
The statement is a closed arithmetic identity over `Int`, which the kernel verifies
directly by `rfl` (GMP-accelerated `Nat` arithmetic), so no Mathlib machinery is needed
and the proof depends on no axioms.
-/

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The known representation of `42` as a sum of three integer cubes
(Booker–Sutherland, 2019):
`42 = (-80538738812075974)^3 + 80435758145817515^3 + 12602123297335631^3`. -/
theorem sum_three_cubes_42 :
    (42 : Int) =
      (-80538738812075974) ^ 3 + 80435758145817515 ^ 3 + 12602123297335631 ^ 3 := by
  rfl

end Frontier

