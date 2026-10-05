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

theorem massGap_of_exponentialClustering (S : TransferSystem) {C m : ℝ} (hC : 0 < C)
    (hcl : S.HasExponentialClustering C m) : S.HasMassGap m := by
  intro t ht ψ hψ
  have hlim : Filter.Tendsto
      (fun n : ℕ => C ^ ((1 / 2 : ℝ) ^ n) * Real.exp (-m * t) * ‖ψ‖)
      Filter.atTop (nhds (Real.exp (-m * t) * ‖ψ‖)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Filter.Tendsto (fun x : ℝ => C ^ x) (nhds 0) (nhds 1) := by
      simpa using (Real.continuousAt_const_rpow (a := C) (b := 0) hC.ne').tendsto
    simpa using ((h2.comp h1).mul_const (Real.exp (-m * t))).mul_const ‖ψ‖
  exact ge_of_tendsto' hlim (fun n => S.clustering_pow hC hcl n t ht ψ hψ)

end YangMills

/-! ## The target statement -/

namespace Frontier

open YangMills

/-- **Yang–Mills mass gap (Lean-checked reduction).**

For a compact gauge group `G`: if there exists a quantum Yang–Mills theory on `ℝ⁴` with gauge
group `G` whose vacuum correlations cluster exponentially at some positive rate `m` (with an
arbitrary constant), then there exists a quantum Yang–Mills theory on `ℝ⁴` with gauge group
`G` possessing a strictly positive mass gap — indeed a mass gap of size at least `m`.

Here "quantum Yang–Mills theory on `ℝ⁴`" means a `YangMills.YangMillsTheory G`: a Hilbert
space with a unit vacuum, the Euclidean-time transfer semigroup `e^{-tH}` of a self-adjoint
positive Hamiltonian annihilating the vacuum, a unitary representation of spatial translations
of `ℝ⁴` commuting with the time evolution, and gauge-invariant Wilson-loop observables for
which the vacuum is cyclic; and "mass gap `Δ`" means `‖e^{-tH} ψ‖ ≤ e^{-Δ t} ‖ψ‖` for every
state `ψ` orthogonal to the vacuum, i.e. `spec(H) \ {0} ⊆ [Δ, ∞)`. -/
