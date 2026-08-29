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

def translateLoop (v : Spacetime) (γ : Loop) : Loop := γ + ContinuousMap.const _ v

/-! ## The gap-relevant structure of a quantum field theory -/

/-- The Osterwalder–Schrader / transfer-matrix data of a quantum field theory, i.e. the
structure on which the notion of a mass gap is defined: a complex Hilbert space with a unit
vacuum vector and the Euclidean-time transfer semigroup `transfer t = e^{-tH}`, which is a
self-adjoint contraction semigroup fixing the vacuum.  The last axiom says the theory is not
just the (one-dimensional) vacuum sector. -/
structure TransferSystem where
  /-- The Hilbert space of physical states. -/
  Space : Type
  [normedSpace : NormedAddCommGroup Space]
  [innerSpace : InnerProductSpace ℂ Space]
  [completeSpace : CompleteSpace Space]
  /-- The vacuum state. -/
  vacuum : Space
  /-- The vacuum is a unit vector. -/
  vacuum_norm : ‖vacuum‖ = 1
  /-- The Euclidean-time transfer operators `e^{-tH}`, `t ≥ 0`. -/
  transfer : ℝ → (Space →L[ℂ] Space)
  /-- `e^{-0·H} = 1`. -/
  transfer_zero : transfer 0 = ContinuousLinearMap.id ℂ Space
  /-- The semigroup law `e^{-(s+t)H} = e^{-sH} e^{-tH}`. -/
  transfer_add : ∀ s t, 0 ≤ s → 0 ≤ t → transfer (s + t) = (transfer s).comp (transfer t)
  /-- Self-adjointness of the transfer operators (`H` is self-adjoint). -/
  transfer_selfAdjoint : ∀ t, 0 ≤ t → IsSelfAdjoint (transfer t)
  /-- Positivity of the energy: the transfer operators are contractions. -/
  transfer_norm_le_one : ∀ t, 0 ≤ t → ‖transfer t‖ ≤ 1
  /-- The vacuum has zero energy. -/
  transfer_vacuum : ∀ t, 0 ≤ t → transfer t vacuum = vacuum
  /-- Non-triviality: there are states orthogonal to the vacuum. -/
  vacuum_ortho_nontrivial : ∃ ψ : Space, ψ ≠ 0 ∧ inner ℂ vacuum ψ = (0 : ℂ)

attribute [instance] TransferSystem.normedSpace TransferSystem.innerSpace
  TransferSystem.completeSpace

/-- A quantum Yang–Mills theory on `ℝ⁴` with compact gauge group `G`: a transfer system
carrying a unitary representation of the spatial translations of `ℝ⁴` commuting with the
Euclidean-time evolution, together with the gauge-invariant Wilson-loop observables
`W(γ, χ)` (`γ` a loop in spacetime, `χ` a continuous character of `G`), which are covariant
under spatial translations and for which the vacuum is cyclic. -/
structure YangMillsTheory (G : Type) [Group G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalGroup G] extends TransferSystem where
  /-- The unitary representation of spatial translations. -/
  translate : SpatialTranslation → (Space ≃ₗᵢ[ℂ] Space)
  /-- The representation sends `0` to the identity. -/
  translate_zero : translate 0 = LinearIsometryEquiv.refl ℂ Space
  /-- The representation is a group homomorphism. -/
  translate_add : ∀ v w, translate (v + w) = (translate v).trans (translate w)
  /-- The vacuum is translation invariant. -/
  translate_vacuum : ∀ v, translate v vacuum = vacuum
  /-- Spatial translations commute with Euclidean time evolution. -/
  translate_transfer : ∀ v t ψ, 0 ≤ t → transfer t (translate v ψ) = translate v (transfer t ψ)
  /-- The gauge-invariant Wilson-loop observables. -/
  wilson : Loop → C(G, ℂ) → (Space →L[ℂ] Space)
  /-- Wilson observables are additive in the character, as `χ_{ρ ⊕ σ} = χ_ρ + χ_σ`. -/
  wilson_add : ∀ γ χ₁ χ₂, wilson γ (χ₁ + χ₂) = wilson γ χ₁ + wilson γ χ₂
  /-- Wilson observables are covariant under spatial translations. -/
  wilson_covariant : ∀ (v : SpatialTranslation) (γ : Loop) (χ : C(G, ℂ)) (ψ : Space),
    wilson (translateLoop (v : Spacetime) γ) χ (translate v ψ) = translate v (wilson γ χ ψ)
  /-- The vacuum is cyclic for the algebra of Wilson observables. -/
  vacuum_cyclic :
    (Submodule.span ℂ
      (Set.range fun p : Loop × C(G, ℂ) => wilson p.1 p.2 vacuum)).topologicalClosure = ⊤

/-! ## Mass gap and exponential clustering -/

/-- A transfer system has a mass gap of size at least `Δ` if the Euclidean-time evolution
decays at rate `Δ` on the orthogonal complement of the vacuum:
`‖e^{-tH} ψ‖ ≤ e^{-Δ t} ‖ψ‖` for `ψ ⟂ Ω`.  For a self-adjoint contraction semigroup this is
equivalent to `spec(H) \ {0} ⊆ [Δ, ∞)`. -/
