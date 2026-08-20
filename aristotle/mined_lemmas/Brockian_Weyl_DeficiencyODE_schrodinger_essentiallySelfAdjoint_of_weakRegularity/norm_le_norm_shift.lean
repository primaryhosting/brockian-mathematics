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

lemma norm_le_norm_shift {G : OperatorGraph H} (hsym : IsSymmetricGraph G) {p : H × H} (hp : p ∈ G)
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    ‖p‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
  have h := norm_shift_sq hsym hp hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hMpos : (0 : ℝ) ≤ max 1 ‖c‖⁻¹ := le_trans zero_le_one (le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ max 1 ‖c‖⁻¹ := le_max_left _ _
  have hM2 : ‖c‖⁻¹ ≤ max 1 ‖c‖⁻¹ := le_max_right _ _
  have hN : 0 ≤ ‖p.2 + c • p.1‖ := norm_nonneg _
  have h1 : ‖p.1‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
    have hkey : ‖c‖ * ‖p.1‖ ≤ ‖p.2 + c • p.1‖ := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2]
    have : ‖p.1‖ ≤ ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hcpos]
      linarith [hkey, mul_comm ‖c‖ ‖p.1‖]
    nlinarith
  have h2 : ‖p.2‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
    have : ‖p.2‖ ≤ ‖p.2 + c • p.1‖ := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2, sq_nonneg ‖c‖]
    nlinarith
  rw [Prod.norm_def]
  exact max_le h1 h2

/-! ### Closed range of the deficiency shifts -/

/-- For a *closed* symmetric operator and a nonzero purely imaginary `c`, the deficiency range
`ran (T + c)` is closed. -/
