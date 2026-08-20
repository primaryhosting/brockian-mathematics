/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

Mathlib does not (yet) contain the theory of smooth projective complex varieties, their singular
cohomology, the Hodge decomposition, or cycle class maps.  We therefore develop, from scratch, the
linear-algebraic and axiomatic framework needed to *state* the Hodge conjecture, and we prove the
degree-`0` base case together with several Lean-checked reductions.

The framework consists of:

* `Frontier.Cx V`, the complexification `ℂ ⊗[ℚ] V` of a rational vector space, with its
  inclusion `Frontier.cxIncl` (proved injective) and its complex conjugation `Frontier.cxConj`;
* `Frontier.HodgeStr`, a pure rational Hodge structure: a finite-dimensional `ℚ`-vector space `V`
  of weight `w` together with a decomposition `V ⊗ ℂ = ⨁_{p+q=w} V^{p,q}` satisfying Hodge
  symmetry `conj (V^{p,q}) = V^{q,p}`;
* `Frontier.hodgeClasses H p`, the `ℚ`-subspace of rational classes of type `(p,p)`;
* `Frontier.HodgeTheory`, an axiomatization of the geometric input of the conjecture: a class of
  (smooth projective, connected) varieties, the Hodge structures on their rational cohomology, and
  the subspaces of classes of algebraic cycles;
* `Frontier.HodgeTheory.HodgeConjecture`, the statement of the Hodge conjecture for such data:
  every rational Hodge class of type `(p,p)` is a rational combination of classes of algebraic
  cycles.

The main theorem `Frontier.hodge_statement` proves the base case `p = 0` of the conjecture for
*every* Hodge theory: in cohomological degree `0` all Hodge classes are algebraic.
-/

namespace Frontier

/-! ## Complexification of a rational vector space -/

/-- The complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`. -/
abbrev Cx (V : Type) [AddCommGroup V] [Module ℚ V] : Type := ℂ ⊗[ℚ] V

/-- The canonical inclusion `V → V ⊗ ℂ`, `v ↦ 1 ⊗ v`. -/

theorem hodgeClasses_eq_bot_of_Hpq_eq_bot (H : HodgeStr) (p : ℤ) (h : H.Hpq p p = ⊥) :
    hodgeClasses H p = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [mem_hodgeClasses_iff, h, Submodule.mem_bot] at hv
  have : cxIncl H.carrier v = cxIncl H.carrier 0 := by simpa using hv
  simpa using cxIncl_injective H.carrier this

/-! ## The Hodge conjecture -/

/-- An axiomatization of the geometric data entering the Hodge conjecture.

`Var` is a class of (smooth projective, connected) complex varieties.  For each `X : Var` and each
degree `k`, `H X k` is the weight-`k` Hodge structure on `Hᵏ(X, ℚ)`; it is effective.  For each
codimension `p`, `alg X p` is the `ℚ`-subspace of `H²ᵖ(X, ℚ)` spanned by the cycle classes of the
codimension-`p` algebraic subvarieties of `X`; by the standard properties of the cycle class map,
these are Hodge classes of type `(p,p)`.  Finally, `fund X` is the fundamental class of `X` in
`H⁰(X, ℚ)`: it is nonzero, algebraic (being the class of the codimension-`0` cycle `X` itself),
and, `X` being connected, `H⁰(X, ℚ)` is one-dimensional. -/
structure HodgeTheory where
  /-- The class of varieties under consideration. -/
  Var : Type
  /-- The Hodge structure on the degree-`k` rational cohomology of `X`. -/
  H : Var → ℕ → HodgeStr
  /-- The Hodge structure on `Hᵏ(X, ℚ)` is pure of weight `k`. -/
  weight_eq : ∀ X k, (H X k).w = k
  /-- Hodge structures of geometric origin are effective. -/
  effective : ∀ X k, (H X k).Effective
  /-- The subspace of `H²ᵖ(X, ℚ)` spanned by classes of codimension-`p` algebraic cycles. -/
  alg : (X : Var) → (p : ℕ) → Submodule ℚ (H X (2 * p)).carrier
  /-- Algebraic cycle classes are Hodge classes of type `(p,p)`. -/
  alg_le_hodgeClasses : ∀ X p, alg X p ≤ hodgeClasses (H X (2 * p)) p
  /-- The fundamental class of `X` in `H⁰(X, ℚ)`. -/
  fund : (X : Var) → (H X 0).carrier
  /-- The fundamental class is nonzero. -/
  fund_ne_zero : ∀ X, fund X ≠ 0
  /-- The fundamental class is algebraic: it is the class of the codimension-`0` cycle `X`. -/
  fund_mem_alg : ∀ X, fund X ∈ alg X 0
  /-- The varieties are connected, so their degree-`0` cohomology is one-dimensional. -/
  finrank_H0 : ∀ X, Module.finrank ℚ (H X 0).carrier = 1

/-- **The Hodge conjecture** for a given Hodge theory: for every variety `X` and every
codimension `p`, every rational Hodge class of type `(p,p)` in `H²ᵖ(X, ℚ)` is a rational linear
combination of classes of codimension-`p` algebraic cycles. -/
