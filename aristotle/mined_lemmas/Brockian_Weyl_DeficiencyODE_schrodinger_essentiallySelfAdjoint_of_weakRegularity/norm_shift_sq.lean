import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

lemma norm_shift_sq {G : OperatorGraph H} (hsym : IsSymmetricGraph G) {p : H × H} (hp : p ∈ G)
    {c : ℂ} (hc : c.re = 0) :
    ‖p.2 + c • p.1‖ ^ 2 = ‖p.2‖ ^ 2 + ‖c‖ ^ 2 * ‖p.1‖ ^ 2 := by
  have hre : ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ := hsym hp p hp
  have hconj : (starRingEnd ℂ) ⟪p.2, p.1⟫_ℂ = ⟪p.2, p.1⟫_ℂ := by
    rw [inner_conj_symm]; exact hre.symm
  have him : (⟪p.2, p.1⟫_ℂ).im = 0 := by
    have h2 := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h2
    linarith
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have hzero : RCLike.re (c * ⟪p.2, p.1⟫_ℂ) = 0 := by
    simp [hc, him]
  rw [hzero]
  ring

