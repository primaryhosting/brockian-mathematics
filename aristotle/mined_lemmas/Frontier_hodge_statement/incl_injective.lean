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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

lemma incl_injective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (incl V) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (by
      rw [LinearMap.ker_eq_bot]
      exact fun a b h => by simpa using h)
  have hg1 : g 1 = 1 := by
    have := congrArg (fun f : ℚ →ₗ[ℚ] ℚ => f 1) hg
    simpa using this
  refine Function.LeftInverse.injective
    (g := fun x => (TensorProduct.lid ℚ V) (LinearMap.rTensor V g x)) ?_
  intro v
  simp [hg1]

/-! ## Rational Hodge structures with a subspace of algebraic classes -/

/--
A `HodgeDatum` packages the Hodge-theoretic data attached to a smooth projective complex
variety `X` in a fixed even cohomological degree `2p`:

* a finite-dimensional `ℚ`-vector space `V` (playing the role of `H^{2p}(X, ℚ)`);
* a decomposition of the complexification `ℂ ⊗[ℚ] V` into subspaces `H^{a,b}` indexed by
  pairs of integers, concentrated in bidegrees with `a + b = 2p` (purity), forming an
  internal direct sum, and exchanged by complex conjugation `H^{a,b} = conj H^{b,a}`;
* a `ℚ`-subspace `alg ⊆ V` (playing the role of the span of the classes of algebraic cycles
  of codimension `p` on `X`), which is required to consist of Hodge classes, i.e. of rational
  classes whose image in `ℂ ⊗[ℚ] V` lies in `H^{p,p}`.

The last requirement is the elementary half of the story: cycle classes are always Hodge
classes.  The Hodge conjecture is the converse inclusion, `HodgeConjecture` below.
-/
structure HodgeDatum where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℚ V]
  /-- Half the weight: we look at `H^{2p}` and codimension `p` cycles. -/
  p : ℕ
  /-- The Hodge decomposition of the complexification. -/
  Hpq : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Purity: the Hodge structure is pure of weight `2p`. -/
  pure' : ∀ ab : ℤ × ℤ, ab.1 + ab.2 ≠ 2 * (p : ℤ) → Hpq ab = ⊥
  /-- The pieces `H^{a,b}` decompose the complexification as an internal direct sum. -/
  internal : DirectSum.IsInternal Hpq
  /-- Complex conjugation exchanges `H^{a,b}` and `H^{b,a}`. -/
  conj_mem : ∀ (a b : ℤ) (x : ℂ ⊗[ℚ] V), x ∈ Hpq (a, b) → conjTensor V x ∈ Hpq (b, a)
  /-- The subspace of classes of algebraic cycles of codimension `p`. -/
  alg : Submodule ℚ V
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le : alg ≤ ((Hpq ((p : ℤ), (p : ℤ))).restrictScalars ℚ).comap (incl V)

attribute [instance] HodgeDatum.addCommGroup HodgeDatum.module

namespace HodgeDatum

variable (X : HodgeDatum)

/-- The space of *Hodge classes*: rational classes `v ∈ H^{2p}(X, ℚ)` whose image
`1 ⊗ v` in `ℂ ⊗[ℚ] H^{2p}(X, ℚ)` lies in the `(p,p)`-part of the Hodge decomposition. -/
