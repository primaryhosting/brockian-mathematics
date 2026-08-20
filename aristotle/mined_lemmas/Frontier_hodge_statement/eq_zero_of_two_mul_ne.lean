import Mathlib
import RequestProject.Hodge

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

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TensorProduct

namespace Frontier

/-! ## Rational Hodge structures -/

/-- A **rational Hodge structure of weight `w`** on a finite–dimensional `ℚ`-vector space `V`:
a decomposition of the complexification `ℂ ⊗[ℚ] V` into complex subspaces
`piece q = V^{q, w - q}`, together with the complex conjugation of `ℂ ⊗[ℚ] V`
(semilinear over `ℂ`, the identity on the rational points `1 ⊗ v`), subject to the
symmetry `conj (V^{q, w - q}) ⊆ V^{w - q, q}`.

This is the standard linear–algebra package carried by the singular cohomology
`H^w(X, ℚ)` of a smooth projective complex variety `X`. -/
structure HodgeStructure (w : ℤ) (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The Hodge piece `V^{q, w - q}` of the complexification. -/
  piece : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The Hodge decomposition `ℂ ⊗ V = ⨁_q V^{q, w - q}`. -/
  decomposition : DirectSum.IsInternal piece
  /-- Complex conjugation on the complexification. -/
  conj : (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V)
  /-- Conjugation acts on the first tensor factor. -/
  conj_tmul : ∀ (c : ℂ) (v : V), conj (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ c) ⊗ₜ[ℚ] v
  /-- The Hodge symmetry `conj (V^{q, w - q}) ⊆ V^{w - q, q}`. -/
  conj_piece : ∀ q, Submodule.map conj ((piece q).restrictScalars ℚ)
      ≤ (piece (w - q)).restrictScalars ℚ

namespace HodgeStructure

variable {w : ℤ} {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The rational classes of type `(q, w - q)`: those `v ∈ V` whose image `1 ⊗ v` in the
complexification lies in the Hodge piece `V^{q, w - q}`.  For `w = 2 p` and `q = p` these are
the **Hodge classes** of the Hodge structure. -/

theorem eq_zero_of_two_mul_ne (hs : HodgeStructure w V) {q : ℤ} (hq : 2 * q ≠ w) {v : V}
    (hv : v ∈ hs.hodgeClasses q) : v = 0 := by
  have hmem : (1 : ℂ) ⊗ₜ[ℚ] v ∈ hs.piece q := hv
  have hmem' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ hs.piece (w - q) := by
    have : hs.conj ((1 : ℂ) ⊗ₜ[ℚ] v) ∈ (hs.piece (w - q)).restrictScalars ℚ :=
      hs.conj_piece q ⟨(1 : ℂ) ⊗ₜ[ℚ] v, hmem, rfl⟩
    rwa [hs.conj_one_tmul] at this
  have hne : q ≠ w - q := by omega
  have hdisj : Disjoint (hs.piece q) (hs.piece (w - q)) :=
    hs.decomposition.submodule_iSupIndep.pairwiseDisjoint hne
  have hzero : (1 : ℂ) ⊗ₜ[ℚ] v = 0 :=
    (Submodule.disjoint_def.mp hdisj) _ hmem hmem'
  have hmk : (TensorProduct.mk ℚ ℂ V 1) v = (TensorProduct.mk ℚ ℂ V 1) 0 := by
    simpa using hzero
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℚ) (B := ℂ) V hmk

end HodgeStructure

/-! ## Hodge data and the Hodge conjecture -/

/-- The linear–algebra data attached to a smooth projective complex variety `X` and an integer
`p ≥ 0`: the finite–dimensional rational cohomology group `H^{2p}(X, ℚ)` with its Hodge
structure of weight `2 p`, together with the subspace `algebraic` spanned by the cycle classes
of the algebraic subvarieties of `X` of codimension `p`.  That these cycle classes are Hodge
classes is part of the data (`algebraic_le_hodgeClasses`); it is the standard fact that the
cycle class of a codimension-`p` subvariety is a rational class of type `(p, p)`. -/
structure HodgeDatum (p : ℤ) where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  coh : Type
  [addCommGroup : AddCommGroup coh]
  [module : Module ℚ coh]
  [finite : Module.Finite ℚ coh]
  /-- Its Hodge structure of weight `2 p`. -/
  hodge : HodgeStructure (2 * p) coh
  /-- The `ℚ`-span of the classes of algebraic cycles of codimension `p`. -/
  algebraic : Submodule ℚ coh
  /-- Algebraic cycle classes are Hodge classes. -/
  algebraic_le_hodgeClasses : algebraic ≤ hodge.hodgeClasses p

attribute [instance] HodgeDatum.addCommGroup HodgeDatum.module HodgeDatum.finite

/-- **The Hodge conjecture** for the datum `D` coming from a smooth projective complex variety
`X` in codimension `p`: every Hodge class in `H^{2p}(X, ℚ)`, i.e. every rational cohomology
class of type `(p, p)`, is a `ℚ`-linear combination of classes of algebraic cycles of
codimension `p`. -/
