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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open TensorProduct

/-! ## The linear-algebra set-up

For a smooth complex projective variety `X`, the singular cohomology group
`V = H^{2p}(X, ℚ)` is a finite-dimensional `ℚ`-vector space whose complexification
`ℂ ⊗[ℚ] V` carries the Hodge decomposition into subspaces `H^{r,s}` with `r + s = 2p`,
exchanged by complex conjugation.  A *Hodge class* is a rational class whose image in the
complexification lies in the `(p,p)`-part, and the Hodge conjecture asserts that every
Hodge class is a rational combination of classes of algebraic cycles of codimension `p`.

Below we axiomatise exactly this data: `HodgeStructure w` records the rational vector
space together with its Hodge decomposition of weight `w`, `CycleClasses S p` records the
subspace of classes of algebraic cycles (which is always contained in the space of Hodge
classes — this containment is a theorem of Hodge theory, taken here as part of the data),
and `HodgeConjectureFor` is the assertion that the two subspaces agree. -/

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`; it is `ℚ`-linear (and
`ℂ`-semilinear). -/

lemma finrank_hodgeClasses_le {w : ℤ} (S : HodgeStructure w) (p : ℤ) :
    Module.finrank ℚ (S.hodgeClasses p) ≤ Module.finrank ℂ (S.H (p, p)) := by
  classical
  set W : Submodule ℚ S.V := S.hodgeClasses p with hW
  -- the base-changed inclusion `ℂ ⊗ W → ℂ ⊗ V`
  set f : (ℂ ⊗[ℚ] W) →ₗ[ℂ] (ℂ ⊗[ℚ] S.V) := LinearMap.baseChange ℂ W.subtype with hf
  have hfinj : Function.Injective f := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap
      (M := ℂ) (W.subtype) (Submodule.injective_subtype W)
    simpa [hf, LinearMap.baseChange_eq_ltensor] using h
  have hrange : ∀ x : ℂ ⊗[ℚ] W, f x ∈ S.H (p, p) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
        have hv : (1 : ℂ) ⊗ₜ[ℚ] (v : S.V) ∈ S.H (p, p) := v.2
        have : f (c ⊗ₜ[ℚ] v) = c • ((1 : ℂ) ⊗ₜ[ℚ] (v : S.V)) := by
          simp [hf, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
        rw [this]
        exact (S.H (p, p)).smul_mem c hv
    | add x y hx hy => simpa [map_add] using (S.H (p, p)).add_mem hx hy
  set g : (ℂ ⊗[ℚ] W) →ₗ[ℂ] (S.H (p, p)) := LinearMap.codRestrict _ f hrange with hg
  have hginj : Function.Injective g := by
    intro x y hxy
    apply hfinj
    simpa [hg, LinearMap.codRestrict, Subtype.ext_iff] using congrArg Subtype.val hxy
  have h1 : Module.finrank ℂ (ℂ ⊗[ℚ] W) ≤ Module.finrank ℂ (S.H (p, p)) :=
    LinearMap.finrank_le_finrank_of_injective (f := g) hginj
  have h2 : Module.finrank ℂ (ℂ ⊗[ℚ] W) = Module.finrank ℚ W :=
    Module.finrank_baseChange (R := ℂ) (S := ℚ) (M' := W)
  rw [← h2]
  exact h1

/-- A numerical reduction: the conjecture holds as soon as the algebraic classes already
account for the full dimension of the space of Hodge classes. -/
