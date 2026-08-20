/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/

lemma inner_generator_adjoint {y : H} (hy : y ∈ (generator U).adjoint.domain)
    (w : (generator U).domain) :
    inner ℂ (generator U w) y = inner ℂ (w : H) ((generator U).adjoint ⟨y, hy⟩) := by
  have hdense := dense_generatorDomain U hU0 hUadd hUcont
  have h := LinearPMap.adjoint_isFormalAdjoint (T := generator U) hdense ⟨y, hy⟩ w
  calc inner ℂ (generator U w) y
      = (starRingEnd ℂ) (inner ℂ y (generator U w)) := (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (inner ℂ ((generator U).adjoint ⟨y, hy⟩) (w : H)) := by rw [h]
    _ = inner ℂ (w : H) ((generator U).adjoint ⟨y, hy⟩) := inner_conj_symm _ _

include hU0 hUadd hUcont in
/-- The key differential identity: for `x` in the domain of the generator and `y` in the domain
of the adjoint, `t ↦ ⟪U t x, y⟫` is differentiable with derivative `i ⟪U t x, A† y⟫`. -/
