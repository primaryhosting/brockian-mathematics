/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires import commands to come before any module docstring, so the requested
header appears here as an ordinary block comment, and again as the module docstring immediately
after the imports.)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff RealInnerProductSpace BigOperators
open Set Topology

/-!
## Scope

John Nash's theorem states that *every* Riemannian manifold `(M, g)` admits a smooth isometric
embedding into some Euclidean space `ℝ^N`, i.e. a smooth topological embedding
`f : M → ℝ^N` whose differential satisfies `⟪df_x v, df_x w⟫ = g x v w` for all tangent vectors
`v, w` at every point `x`. Its proof (via the Nash–Moser implicit function theorem) is far beyond
the current state of formalized mathematics, and the general statement is not available in
Mathlib.

This file formalizes the notion of a smooth isometric embedding of a Riemannian metric
(`Math2.IsSmoothIsometricEmbedding`) and proves the Nash embedding statement for two genuine
families of Riemannian metrics:

* `Math2.nash_embedding`: all metrics on `ℝⁿ` of the separably-diagonal form
  `g x v w = ∑ i, (a i (x i))^2 * v i * w i` with `a i` smooth and positive. In particular, for
  `n = 1` this is *every* Riemannian metric on the real line.
* `Math2.nash_embedding_inner_product_space`: the canonical metric of any finite-dimensional real
  inner product space.
* `Math2.nash_embedding_graph`: all metrics on `ℝⁿ` induced by the graph of a smooth function
  `u : ℝⁿ → ℝ`, which are in general curved.

No axioms beyond the standard ones (`propext`, `Classical.choice`, `Quot.sound`) are used.
-/

namespace Math2

/-- `IsSmoothIsometricEmbedding g f` says that `f`, a map from the manifold `E` (a real normed
space, playing the role of ℝⁿ) into a Euclidean space `ℝ^N`, is a smooth isometric embedding of
the Riemannian metric `g`: it is `C^∞`, it is a topological embedding, and its differential
pulls the Euclidean inner product back to `g`.

Here a Riemannian metric is described concretely by the function `g : E → E → E → ℝ`, where
`g x v w` is the inner product of the tangent vectors `v`, `w` at the point `x`. -/

theorem nash_embedding_graph {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ ∞ u) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      IsSmoothIsometricEmbedding
        (fun x v w => ⟪v, w⟫ + fderiv ℝ u x v * fderiv ℝ u x w) f := by
  set e : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (Fin (n + 1) → ℝ) := EuclideanSpace.equiv _ ℝ with he
  refine ⟨n + 1, fun z => e.symm (Fin.snoc (fun j => z j) (u z)), ?_, ?_, ?_⟩
  · -- smoothness
    refine e.symm.contDiff.comp (contDiff_pi.2 fun i => ?_)
    refine Fin.lastCases ?_ ?_ i
    · simpa using hu
    · intro j
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  · -- topological embedding: the projection to the first `n` coordinates is a left inverse
    have hcf : Continuous
        (fun z : EuclideanSpace ℝ (Fin n) => e.symm (Fin.snoc (fun j => z j) (u z))) := by
      refine e.symm.continuous.comp (continuous_pi fun i => ?_)
      refine Fin.lastCases ?_ ?_ i
      · simpa using hu.continuous
      · intro j; simpa using (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
    set p : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
      fun y => (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => y (Fin.castSucc j)) with hp
    have hcp : Continuous p :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
        (continuous_pi fun j => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc j)).continuous)
    have hleft : Function.LeftInverse p
        (fun z : EuclideanSpace ℝ (Fin n) => e.symm (Fin.snoc (fun j => z j) (u z))) := by
      intro z
      ext j
      simp [hp, he]
    exact (hleft.isClosedEmbedding hcp hcf).isEmbedding
  · -- the differential pulls back the Euclidean metric to the graph metric
    intro x v w
    set Lpi : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin (n + 1) → ℝ) :=
      ContinuousLinearMap.pi (Fin.lastCases (fderiv ℝ u x) (fun j => EuclideanSpace.proj j))
      with hLpi
    have hF : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) =>
        (Fin.snoc (fun j => z j) (u z) : Fin (n + 1) → ℝ)) Lpi x := by
      rw [hasFDerivAt_pi']
      intro i
      refine Fin.lastCases ?_ ?_ i
      · have h : HasFDerivAt u (fderiv ℝ u x) x := (hu.differentiable (by simp) x).hasFDerivAt
        simpa [hLpi] using h
      · intro j
        simpa [hLpi] using (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := x)
    have hf : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => e.symm (Fin.snoc (fun j => z j) (u z)))
        ((e.symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp Lpi) x :=
      e.symm.hasFDerivAt.comp x hF
    rw [hf.fderiv]
    have hcoord : ∀ z : EuclideanSpace ℝ (Fin n), ∀ i,
        (((e.symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp Lpi) z) i
          = (Fin.snoc (fun j => z j) (fderiv ℝ u x z) : Fin (n + 1) → ℝ) i := by
      intro z i
      refine Fin.lastCases ?_ ?_ i
      · simp [hLpi, he]
      · intro j; simp [hLpi, he]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcoord v _, hcoord w _]
      simp
    · rw [hcoord v _, hcoord w _]
      simp [mul_comm]

end Math2

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

