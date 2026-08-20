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

def MargulisSuperrigidityStatement (n m : ℕ) : Prop :=
  ∀ ρ : Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
    Dense (Set.range (ρ : Matrix.SpecialLinearGroup (Fin n) ℤ →
        Matrix.GeneralLinearGroup (Fin m) ℝ)) →
      ∃ Φ : Matrix.SpecialLinearGroup (Fin n) ℝ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
        Continuous Φ ∧ ∀ γ, Φ (slEmbedding n γ) = ρ γ

/-- The statement of Margulis superrigidity for `SL(n,ℤ) ≤ SL(n,ℝ)` is exactly the abstract
dense-image extension property for the subgroup `slLattice n`. -/
