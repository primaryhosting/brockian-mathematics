/-
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module docstrings, so the
-- header above is written as an ordinary comment and repeated as a module docstring below.)

import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## The shape of the superrigidity conclusion -/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The conclusion of a superrigidity theorem: the *abstract* group homomorphism
`rho : Γ →* H`, defined on a subgroup `Γ` of a topological group `G`, is the restriction of a
*continuous* homomorphism defined on all of `G`. -/

theorem multiplicative_real_torsionFree :
    ∀ (h : Multiplicative ℝ) (n : ℕ), 0 < n → h ^ n = 1 → h = 1 := by
  intro h n hn hpow
  have h0 : (n : ℝ) * (Multiplicative.toAdd h) = 0 := by
    have := congrArg Multiplicative.toAdd hpow
    simpa [nsmul_eq_mul] using this
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hh : Multiplicative.toAdd h = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact absurd h1 hne
    · exact h2
  exact Multiplicative.toAdd.injective (by simpa using hh)

local instance : TopologicalSpace (Equiv.Perm (Fin 5)) := ⊥
local instance : TopologicalSpace (Multiplicative ℝ) := inferInstanceAs (TopologicalSpace ℝ)

/-- A sanity check that the hypotheses of `margulis_superrigidity` are satisfiable by a
nontrivial pair (group, target): here `Γ = S₅` (finite abelianization) and `H = (ℝ, +)` written
multiplicatively (abelian and torsion free). -/
example (Admissible : ((⊤ : Subgroup (Equiv.Perm (Fin 5))) →* Multiplicative ℝ) → Prop) :
    MargulisSuperrigid (⊤ : Subgroup (Equiv.Perm (Fin 5))) Admissible :=
  margulis_superrigidity multiplicative_real_torsionFree ⊤ Admissible

end Sanity

/-! ## A concrete instance of the extension phenomenon -/

/-- The archetypal (rank-one, abelian) example: every abstract homomorphism from the lattice
`ℤ ≤ ℝ` to `ℝ` is the restriction of a continuous homomorphism `ℝ →+ ℝ`. -/
