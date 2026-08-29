import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a module, so
the mandated header comment appears immediately after the single `import Mathlib` line.

## What is formalised here

The Clay Millennium problem asks for the construction of a quantum Yang–Mills theory on `ℝ⁴`
with a compact simple gauge group `G`, satisfying the Wightman/Osterwalder–Schrader axioms,
and having a *mass gap* `Δ > 0`.

We formalise the statement in the Osterwalder–Schrader (Euclidean, transfer–matrix) picture:

* `TransferSystem` bundles the "gap-relevant" kinematical data of a reflection-positive
  quantum field theory: a complex Hilbert space `Space`, a unit vacuum vector `vacuum`,
  and the Euclidean-time transfer semigroup `transfer t = e^{-tH}` (a self-adjoint
  contraction semigroup fixing the vacuum), together with the requirement that the theory is
  not just the vacuum (`vacuum_ortho_nontrivial`).

* `TransferSystem.HasMassGap Δ` says that on the orthogonal complement of the vacuum the
  semigroup decays at rate at least `Δ`, i.e. `‖e^{-tH} ψ‖ ≤ e^{-Δ t} ‖ψ‖`.  For a
  self-adjoint contraction semigroup this is exactly the statement that
  `spec(H) ⊆ {0} ∪ [Δ, ∞)` with the vacuum spanning the zero-energy subspace, i.e.
  a mass gap of size at least `Δ`.

* `YangMillsTheory G` adds the Yang–Mills field content on `ℝ⁴`: a unitary representation of
  the group of spatial (equal-time) translations of `ℝ⁴` commuting with the Euclidean-time
  evolution and fixing the vacuum, and the gauge-invariant Wilson-loop observables
  `W(γ, χ)` indexed by a loop `γ` in spacetime and a continuous character `χ` of the compact
  gauge group `G` (additive in `χ`, since `χ_{ρ ⊕ σ} = χ_ρ + χ_σ`), covariant under spatial
  translations, and with the vacuum cyclic for the Wilson-loop observables.

* `ExistsYangMillsWithMassGap G` is the existence statement: there is such a theory with a
  strictly positive mass gap.

## What is proved

Constructing the Yang–Mills measure is out of reach; what is proved here is a
*Lean-checked reduction* together with a base case:

* `YangMills.massGap_of_exponentialClustering` (the mathematical core): if the vacuum
  correlations of a transfer system decay exponentially at rate `m` with **some** constant
  `C > 0`, then the theory has a mass gap of exactly `m`, i.e. the constant can be removed.
  This is the standard "self-improvement" of exponential clustering into a spectral gap, and
  is proved by the dyadic bootstrap `‖P_t ψ‖² ≤ ‖ψ‖ ‖P_{2t} ψ‖` iterated, yielding the bound
  with constant `C^{2^{-n}}` for every `n`, and then letting `n → ∞`.

* `Frontier.yang_mills_mass_gap`: the reduction at the level of the existence statements —
  the existence of a quantum Yang–Mills theory on `ℝ⁴` with exponentially clustering vacuum
  implies the existence of a quantum Yang–Mills theory on `ℝ⁴` with a positive mass gap.

* `YangMills.exists_transferSystem_hasMassGap` (base case): the axioms defining the
  gap-relevant structure are consistent — there is a transfer system with a mass gap.
  (This is a consistency check for the axiom system only; it makes no claim about
  Yang–Mills dynamics, which is *not* captured by `TransferSystem`.)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace YangMills

/-! ## Spacetime, spatial translations and loops -/

/-- Euclidean spacetime `ℝ⁴`. -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- The group of spatial (equal-time) translations of `ℝ⁴`: translations whose time
component (coordinate `0`) vanishes. -/

theorem TransferSystem.clustering_pow (S : TransferSystem) {C m : ℝ} (hC : 0 < C)
    (hcl : S.HasExponentialClustering C m) (n : ℕ) :
    ∀ t, 0 ≤ t → ∀ ψ : S.Space, inner ℂ S.vacuum ψ = (0 : ℂ) →
      ‖S.transfer t ψ‖ ≤ C ^ ((1 / 2 : ℝ) ^ n) * Real.exp (-m * t) * ‖ψ‖ := by
  induction n with
  | zero =>
    intro t ht ψ hψ
    simpa using hcl t ht ψ hψ
  | succ n ih =>
    intro t ht ψ hψ
    have h2t : (0 : ℝ) ≤ t + t := by linarith
    have hstep := S.sq_norm_transfer_le t ht ψ
    have hih := ih (t + t) h2t ψ hψ
    set e := Real.exp (-m * t) with he
    have he0 : 0 < e := Real.exp_pos _
    have hee : Real.exp (-m * (t + t)) = e * e := by
      rw [he, ← Real.exp_add]; ring_nf
    have hb0 : 0 ≤ C ^ ((1 / 2 : ℝ) ^ (n + 1)) * e * ‖ψ‖ :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hC.le _) he0.le) (norm_nonneg _)
    have hsq : ‖S.transfer t ψ‖ ^ 2 ≤ (C ^ ((1 / 2 : ℝ) ^ (n + 1)) * e * ‖ψ‖) ^ 2 := by
      have heq : (C ^ ((1 / 2 : ℝ) ^ (n + 1)) * e * ‖ψ‖) ^ 2
          = ‖ψ‖ * (C ^ ((1 / 2 : ℝ) ^ n) * Real.exp (-m * (t + t)) * ‖ψ‖) := by
        rw [hee, mul_pow, mul_pow, ← Real.rpow_natCast (C ^ ((1 / 2 : ℝ) ^ (n + 1))) 2,
          ← Real.rpow_mul hC.le]
        have h12 : (1 / 2 : ℝ) ^ (n + 1) * ((2 : ℕ) : ℝ) = (1 / 2 : ℝ) ^ n := by
          push_cast; ring
        rw [h12]; ring
      rw [heq]
      exact hstep.trans (mul_le_mul_of_nonneg_left hih (norm_nonneg _))
    exact (sq_le_sq₀ (norm_nonneg _) hb0).mp hsq

/-- **Exponential clustering implies a mass gap of the same rate.**  If the vacuum
correlations of a transfer system decay exponentially at rate `m` with some constant
`C > 0`, then the theory has a mass gap of size at least `m` (the constant disappears). -/
