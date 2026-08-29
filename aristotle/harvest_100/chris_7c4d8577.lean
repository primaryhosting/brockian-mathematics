/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean does not allow a module
-- docstring to precede the `import` commands; the same text appears as the module
-- docstring immediately below the imports.)

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A *Fermat solution* with exponent `n`: positive naturals `x, y, z` with
`x ^ n + y ^ n = z ^ n`. -/
def FermatSolution (n x y z : ℕ) : Prop := 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ n + y ^ n = z ^ n

/-- Fermat's Last Theorem for the exponent `n`: the equation `x ^ n + y ^ n = z ^ n`
has no solution in positive integers. -/
def FLTFor (n : ℕ) : Prop := ∀ x y z : ℕ, ¬ FermatSolution n x y z

/-- Fermat's Last Theorem: `x ^ n + y ^ n = z ^ n` has no positive-integer solution for `n > 2`. -/
def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

/-- `FLTFor` agrees with Mathlib's `FermatLastTheoremFor`. -/
theorem FLTFor_iff_fermatLastTheoremFor (n : ℕ) : FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h x y z hx hy hz hxyz
    exact h x y z ⟨Nat.pos_of_ne_zero hx, Nat.pos_of_ne_zero hy, Nat.pos_of_ne_zero hz, hxyz⟩
  · intro h x y z ⟨hx, hy, hz, hxyz⟩
    exact h x y z hx.ne' hy.ne' hz.ne' hxyz

/-- `FLT` agrees with Mathlib's `FermatLastTheorem`. -/
theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).1 (h n (by omega))
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).2 (h n (by omega))

/-- Base case `n = 3` (Euler): `x ³ + y ³ = z ³` has no positive-integer solution. -/
theorem FLT_three : FLTFor 3 :=
  (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4` (Fermat): `x ⁴ + y ⁴ = z ⁴` has no positive-integer solution. -/
theorem FLT_four : FLTFor 4 :=
  (FLTFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- If `m ∣ n` and Fermat's equation with exponent `m` has no positive solution, then neither
does the one with exponent `n`. -/
theorem FLTFor_of_dvd {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2
    (((FLTFor_iff_fermatLastTheoremFor m).1 hm).mono hmn)

/-- **Reduction of Fermat's Last Theorem to prime exponents `p ≥ 5`.**

Fermat's Last Theorem — the statement that `x ^ n + y ^ n = z ^ n` has no solution in positive
integers for any `n > 2` — is equivalent to its special case where the exponent is a prime
`p ≥ 5`.  The nontrivial direction uses the divisibility reduction together with the two base
cases `n = 4` (Fermat) and `n = 3` (Euler). -/
theorem FLT_statement :
    (∀ n : ℕ, 2 < n → FLTFor n) ↔ (∀ p : ℕ, p.Prime → 5 ≤ p → FLTFor p) := by
  constructor
  · intro h p _ hp5
    exact h p (by omega)
  · intro h n hn
    obtain hdvd | ⟨p, hp, hdvd, hpodd⟩ :=
      Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
    · exact FLTFor_of_dvd hdvd FLT_four
    · refine FLTFor_of_dvd hdvd ?_
      rcases eq_or_lt_of_le hp.two_le with h2 | h2
      · exact absurd (h2 ▸ hpodd) (by decide)
      · rcases eq_or_lt_of_le (show 3 ≤ p by omega) with h3 | h3
        · exact h3 ▸ FLT_three
        · have : p ≠ 4 := by
            rintro rfl
            exact absurd hpodd (by decide)
          exact h p hp (by omega)

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

