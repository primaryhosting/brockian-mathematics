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

namespace Frontier

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/

lemma hodgeClasses_tate (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    hodgeClasses (tateHodgeStructure V p) p = ⊤ :=
  hodgeClasses_eq_top_of_piece_eq_top _ _ (tateHodgeStructure_piece_self V p)

/-! ## Cohomological data of a smooth projective complex variety -/

/-- The Hodge-theoretic data attached to a smooth projective complex variety `X` of complex
dimension `d`:

* for each `p`, the finite-dimensional `ℚ`-vector space `coh p = H^{2p}(X, ℚ)`, equipped with
  its pure rational Hodge structure of weight `2p`;
* the subspace `alg p ⊆ H^{2p}(X, ℚ)` spanned by the cohomology classes of algebraic cycles of
  codimension `p` (the image of the cycle class map);
* the (elementary, known) fact that classes of algebraic cycles are Hodge classes;
* the vanishing `H^{2p}(X, ℚ) = 0` for `p > d`.
-/
structure HodgeVarietyData (d : ℕ) where
  /-- `coh p` is the rational cohomology `H^{2p}(X, ℚ)`. -/
  coh : ℕ → Type
  [addCommGroup : ∀ p, AddCommGroup (coh p)]
  [isModule : ∀ p, Module ℚ (coh p)]
  [finite : ∀ p, Module.Finite ℚ (coh p)]
  /-- The weight-`2p` Hodge structure on `H^{2p}(X, ℚ)`. -/
  hs : ∀ p : ℕ, HodgeStructure (2 * (p : ℤ)) (coh p)
  /-- The subspace of classes of algebraic cycles of codimension `p`. -/
  alg : ∀ p : ℕ, Submodule ℚ (coh p)
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le_hodge : ∀ p : ℕ, alg p ≤ hodgeClasses (hs p) (p : ℤ)
  /-- Cohomology vanishes above the (real) dimension `2d`. -/
  vanishing : ∀ p : ℕ, d < p → (⊤ : Submodule ℚ (coh p)) = ⊥

attribute [instance] HodgeVarietyData.addCommGroup HodgeVarietyData.isModule
  HodgeVarietyData.finite

/-- **The Hodge conjecture** for a smooth projective complex variety with cohomological data `X`:
every Hodge class in `H^{2p}(X, ℚ)` is a rational linear combination of classes of algebraic
cycles of codimension `p`. -/
