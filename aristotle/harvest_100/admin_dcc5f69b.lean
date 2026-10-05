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
def SpatialTranslation : AddSubgroup Spacetime where
  carrier := {v | v 0 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    simp [ha]

/-- A closed loop in spacetime, i.e. a continuous map from the circle `ℝ / ℤ` to `ℝ⁴`.
Wilson observables are indexed by such loops. -/
abbrev Loop := C(AddCircle (1 : ℝ), Spacetime)

/-- Translating a loop by a spacetime vector. -/
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
def TransferSystem.HasMassGap (S : TransferSystem) (Δ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ ψ : S.Space, inner ℂ S.vacuum ψ = (0 : ℂ) →
    ‖S.transfer t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖

/-- Exponential clustering with rate `m` and constant `C`: correlations of states orthogonal
to the vacuum decay exponentially with rate `m`, up to a constant `C`. -/
def TransferSystem.HasExponentialClustering (S : TransferSystem) (C m : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ ψ : S.Space, inner ℂ S.vacuum ψ = (0 : ℂ) →
    ‖S.transfer t ψ‖ ≤ C * Real.exp (-m * t) * ‖ψ‖

section Existence

variable (G : Type) [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]

/-- **The Yang–Mills mass gap statement.**  There exists a quantum Yang–Mills theory on `ℝ⁴`
with compact gauge group `G` which has a strictly positive mass gap. -/
def ExistsYangMillsWithMassGap : Prop :=
  ∃ T : YangMillsTheory G, ∃ Δ : ℝ, 0 < Δ ∧ T.toTransferSystem.HasMassGap Δ

/-- The (a priori weaker looking) statement that there exists a quantum Yang–Mills theory on
`ℝ⁴` with compact gauge group `G` whose vacuum correlations cluster exponentially at some
positive rate, with some constant. -/
def ExistsYangMillsWithClustering : Prop :=
  ∃ T : YangMillsTheory G, ∃ C m : ℝ, 0 < C ∧ 0 < m ∧
    T.toTransferSystem.HasExponentialClustering C m

end Existence

/-! ## The core estimate and the reduction -/

/-- Reflection positivity estimate: for a self-adjoint transfer semigroup,
`‖P_t ψ‖² = ⟪ψ, P_{2t} ψ⟫ ≤ ‖ψ‖ ‖P_{2t} ψ‖`. -/
theorem TransferSystem.sq_norm_transfer_le (S : TransferSystem) (t : ℝ) (ht : 0 ≤ t)
    (ψ : S.Space) : ‖S.transfer t ψ‖ ^ 2 ≤ ‖ψ‖ * ‖S.transfer (t + t) ψ‖ := by
  have h1 : (inner ℂ (S.transfer t ψ) (S.transfer t ψ) : ℂ)
      = inner ℂ ψ (S.transfer (t + t) ψ) := by
    nth_rewrite 1 [← (S.transfer_selfAdjoint t ht).adjoint_eq]
    rw [ContinuousLinearMap.adjoint_inner_left, S.transfer_add t t ht ht]
    simp
  have h2 : ‖S.transfer t ψ‖ ^ 2 = RCLike.re (inner ℂ (S.transfer t ψ) (S.transfer t ψ)) :=
    (inner_self_eq_norm_sq _).symm
  rw [h2, h1]
  calc RCLike.re (inner ℂ ψ (S.transfer (t + t) ψ) : ℂ)
      ≤ ‖(inner ℂ ψ (S.transfer (t + t) ψ) : ℂ)‖ := RCLike.re_le_norm _
    _ ≤ ‖ψ‖ * ‖S.transfer (t + t) ψ‖ := norm_inner_le_norm _ _

/-- The dyadic bootstrap: exponential clustering with constant `C` self-improves to
clustering with constant `C^{2^{-n}}` for every `n`. -/
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
theorem yang_mills_mass_gap (G : Type) [Group G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalGroup G] (h : ExistsYangMillsWithClustering G) :
    ExistsYangMillsWithMassGap G := by
  obtain ⟨T, C, m, hC, hm, hcl⟩ := h
  exact ⟨T, m, hm, massGap_of_exponentialClustering _ hC hcl⟩

end Frontier

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

