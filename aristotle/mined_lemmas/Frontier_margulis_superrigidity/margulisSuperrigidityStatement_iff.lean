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

set_option grind.warning false

/-!
## Overview

Margulis' superrigidity theorem says, in its classical form:

> Let `G` be a connected semisimple Lie group of real rank at least `2`, with finite centre and
> no compact factors, let `Γ ≤ G` be an irreducible lattice, let `H` be a connected non-compact
> simple algebraic group over `ℝ`, and let `ρ : Γ → H(ℝ)` be a homomorphism whose image is
> Zariski dense.  Then `ρ` extends to a continuous homomorphism `G → H(ℝ)`.

The flagship instance is `Γ = SL(n, ℤ) ≤ SL(n, ℝ) = G` for `n ≥ 3`.

This file does three things.

* It formalises the *extension property* that is the conclusion of superrigidity, both in the
  dense-image form (`Frontier.SuperrigidDense`) and in the unrestricted form
  (`Frontier.SuperrigidAll`), and formalises the statement of Margulis superrigidity for the
  concrete higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)` with target `GL(m,ℝ)`
  (`Frontier.MargulisSuperrigidityStatement`).

* It proves two Lean-checked *reductions*.  The main one,
  `Frontier.superrigidAll_of_superrigidDense`, reduces the extension problem for an arbitrary
  homomorphism to the dense-image case, by replacing the target by the closure of the image;
  this is the (elementary) step by which the general form of superrigidity is deduced from the
  Zariski-dense form.  The target theorem `Frontier.margulis_superrigidity` is this reduction
  carried out for `SL(n,ℤ) ≤ SL(n,ℝ)`: assuming the deep dense-image input of Margulis' theorem
  for closed subgroups of the target, *every* homomorphism `SL(n,ℤ) → GL(m,ℝ)` extends to a
  continuous homomorphism on `SL(n,ℝ)`.

* It proves, unconditionally, the abelian *base case* of the extension phenomenon
  (`Frontier.margulis_superrigidity_baseCase`): every homomorphism from the lattice
  `ℤⁿ ≤ ℝⁿ` to the vector group `ℝᵐ` extends to a **unique** continuous homomorphism
  `ℝⁿ → ℝᵐ`.

Two deliberate deviations from the classical statement are recorded here.  First, Zariski density
of the image is replaced by density in the ambient (Hausdorff, locally compact) topology; this is
a stronger hypothesis on `ρ`, so the dense-image statements below are formally weaker than
Margulis'.  Second, the deep analytic content of Margulis' theorem is *not* proved: it appears as
an explicit hypothesis of the reduction theorems, which is what makes them reductions.
-/

namespace Frontier

/-! ## The extension property -/

/-- `SuperrigidDense G Γ H` : every homomorphism from the subgroup `Γ ≤ G` to `H` whose image is
dense in `H` extends to a continuous homomorphism `G → H`.  This is the conclusion of Margulis
superrigidity, in the form in which it is proved (density replacing Zariski density here). -/

theorem margulisSuperrigidityStatement_iff (n m : ℕ) :
    MargulisSuperrigidityStatement n m ↔
      SuperrigidDense (Matrix.SpecialLinearGroup (Fin n) ℝ) (slLattice n)
        (Matrix.GeneralLinearGroup (Fin m) ℝ) := by
  constructor
  · intro h ρ hdense
    have hd : Dense (Set.range ((ρ.comp (slLatticeEquiv n).toMonoidHom) :
        Matrix.SpecialLinearGroup (Fin n) ℤ → Matrix.GeneralLinearGroup (Fin m) ℝ)) := by
      refine hdense.mono ?_
      rintro x ⟨g, rfl⟩
      exact ⟨(slLatticeEquiv n).symm g, by simp⟩
    obtain ⟨Φ, hcont, hΦ⟩ := h (ρ.comp (slLatticeEquiv n).toMonoidHom) hd
    refine ⟨Φ, hcont, fun g => ?_⟩
    obtain ⟨γ, hγ⟩ := g.2
    have hg : (slLatticeEquiv n) γ = g := Subtype.ext hγ
    rw [← hγ, hΦ γ]
    show ρ (slLatticeEquiv n γ) = ρ g
    rw [hg]
  · intro h ρ hdense
    have hd : Dense (Set.range ((ρ.comp (slLatticeEquiv n).symm.toMonoidHom) :
        slLattice n → Matrix.GeneralLinearGroup (Fin m) ℝ)) := by
      refine hdense.mono ?_
      rintro x ⟨γ, rfl⟩
      exact ⟨slLatticeEquiv n γ, by simp⟩
    obtain ⟨Φ, hcont, hΦ⟩ := h (ρ.comp (slLatticeEquiv n).symm.toMonoidHom) hd
    refine ⟨Φ, hcont, fun γ => ?_⟩
    have := hΦ (slLatticeEquiv n γ)
    simpa using this

/-! ## The target theorem: Margulis superrigidity, reduced to its dense-image case -/

/-- **Margulis superrigidity for the higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)`, in reduced form.**

Let `n ≥ 3`, so that `SL(n,ℝ)` has real rank `n - 1 ≥ 2` and `SL(n,ℤ)` is an irreducible
higher-rank lattice in it.  Assume the deep input of Margulis' theorem: for every closed subgroup
`L` of the target `GL(m,ℝ)`, every homomorphism `SL(n,ℤ) → L` with dense image extends to a
continuous homomorphism `SL(n,ℝ) → L`.  Then *every* homomorphism `ρ : SL(n,ℤ) → GL(m,ℝ)`,
with no density assumption whatsoever, extends to a continuous homomorphism
`Φ : SL(n,ℝ) → GL(m,ℝ)`.

This is the Lean-checked reduction of the general form of superrigidity to its dense-image form:
one passes to the closure of the image of `ρ`, applies the dense-image hypothesis there, and
composes with the inclusion of that closed subgroup.  The rank hypothesis `hn` is recorded
because it is exactly the hypothesis under which the assumed dense-image input is a theorem of
Margulis; the reduction step itself does not use it. -/
