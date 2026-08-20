import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Part I. Transfer matrices, mass gap, and exponential clustering -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The kinematical data extracted from a Euclidean quantum field theory by the
Osterwalder–Schrader reconstruction: a (complex) Hilbert space of physical states, a
normalised vacuum vector, and the self-adjoint contraction semigroup `T t = e^{-tH}`
of Euclidean time translations, which fixes the vacuum. -/
structure TransferMatrixTheory (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Euclidean time evolution semigroup `T t = e^{-t H}`. -/
  T : ℝ → (H →L[ℂ] H)
  /-- The vacuum state. -/
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  T_zero : T 0 = ContinuousLinearMap.id ℂ H
  T_add : ∀ ⦃s t : ℝ⦄, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  T_selfAdjoint : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x y : H, ⟪T t x, y⟫_ℂ = ⟪x, T t y⟫_ℂ
  T_contraction : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖
  T_vacuum : ∀ ⦃t : ℝ⦄, 0 ≤ t → T t vacuum = vacuum

namespace TransferMatrixTheory

variable (Th : TransferMatrixTheory H)

/-- The theory has a mass gap at least `Δ > 0`: on the orthogonal complement of the vacuum
the Euclidean evolution decays at least like `e^{-Δ t}`, uniformly in the state.  Equivalently,
the Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`. -/

def IsTimeZero (γ : ContinuumLoop) : Prop := ∀ s : ℝ, (γ s) 0 = 0

end ContinuumLoop

/-- A complex Hilbert space of physical states. -/
structure PhysicalHilbertSpace : Type 1 where
  /-- The underlying type of states. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] PhysicalHilbertSpace.normedAddCommGroup PhysicalHilbertSpace.innerProductSpace
  PhysicalHilbertSpace.completeSpace

/-- A compact gauge group: a nontrivial compact topological group with its normalised Haar
measure and a conjugation-invariant real character (for `SU(N)`, `chi = Re tr`). -/
structure GaugeGroup : Type 1 where
  /-- The underlying group of the gauge group, e.g. `SU(3)`. -/
  carrier : Type
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The gauge group is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The gauge group is nontrivial (otherwise the theory is empty). -/
  [nontrivial : Nontrivial carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  /-- Normalised Haar measure on the gauge group. -/
  haar : Measure carrier
  [isHaarMeasure : haar.IsHaarMeasure]
  [isProbabilityMeasure : IsProbabilityMeasure haar]
  /-- The real part of the character of a faithful representation, used in the Wilson action. -/
  chi : carrier → ℝ
  chi_conj : ∀ g h : carrier, chi (h * g * h⁻¹) = chi g

attribute [instance] GaugeGroup.group GaugeGroup.topologicalSpace GaugeGroup.isTopologicalGroup
  GaugeGroup.compactSpace GaugeGroup.nontrivial GaugeGroup.measurableSpace GaugeGroup.borelSpace
  GaugeGroup.isHaarMeasure GaugeGroup.isProbabilityMeasure

/-- **Quantum Yang–Mills theory on `ℝ⁴` with compact gauge group `Γ`.**

This bundles the data and axioms that constitute a solution of the existence half of the
Clay Millennium problem for the gauge group `Γ`:

* a Hilbert space of physical states with a vacuum vector and the self-adjoint contraction
  semigroup `e^{-tH}` of Euclidean time translations (`transfer`), i.e. a positive-energy
  quantum theory obtained by Osterwalder–Schrader reconstruction;
* gauge-invariant Wilson-loop field operators (`wilson`) whose vacuum expectations are the
  Schwinger functions (`vacuum_expectation`), which are invariant under the full Euclidean
  group of `ℝ⁴` (`euclidean_invariance`) and which reproduce the Euclidean time evolution
  (`reconstruction`);
* completeness of the Wilson observables: the vacuum is cyclic (`vacuum_cyclic`);
* and, crucially, the statement that these Schwinger functions are the continuum limit
  (`continuum_limit`) of the Wilson lattice gauge theory with gauge group `Γ`, along lattice
  spacings tending to `0` in boxes exhausting the lattice, with loops discretised
  consistently (`discretise_approx`). -/
structure YangMillsTheory (Γ : GaugeGroup) : Type 1 where
  /-- The Hilbert space of physical states. -/
  space : PhysicalHilbertSpace
  /-- The vacuum and the Euclidean time evolution semigroup `e^{-tH}`. -/
  transfer : TransferMatrixTheory space.carrier
  /-- The Wilson loop field operators. -/
  wilson : ContinuumLoop → (space.carrier →L[ℂ] space.carrier)
  /-- The Schwinger functions (Euclidean correlation functions of Wilson loops). -/
  schwinger : List ContinuumLoop → ℂ
  /-- The lattice spacings along which the continuum limit is taken. -/
  spacing : ℕ → ℝ
  /-- The bare inverse couplings along which the continuum limit is taken. -/
  coupling : ℕ → ℝ
  /-- The finite boxes exhausting the lattice. -/
  boxes : ℕ → Finset Site
  /-- The discretisation of a continuum loop at the `n`-th lattice spacing. -/
  discretise : ℕ → ContinuumLoop → LatticeLoop
  spacing_pos : ∀ n, 0 < spacing n
  spacing_tendsto_zero : Filter.Tendsto spacing Filter.atTop (nhds 0)
  boxes_mono : Monotone boxes
  boxes_exhaust : ∀ x : Site, ∃ n, x ∈ boxes n
  /-- The discretised loops converge to the continuum loops. -/
  discretise_approx : ∀ γ : ContinuumLoop, Filter.Tendsto
    (fun n => Metric.hausdorffDist (latticeLoopPoints (spacing n) (discretise n γ))
      (Set.range γ)) Filter.atTop (nhds 0)
  /-- The Schwinger functions are the continuum limit of Wilson lattice gauge theory. -/
  continuum_limit : ∀ loops : List ContinuumLoop, Filter.Tendsto
    (fun n => wilsonExpectation Γ.haar Γ.chi (coupling n) (boxes n)
      (fun U => (loops.map (fun γ => latticeWilsonLoop Γ.chi U (discretise n γ))).prod))
    Filter.atTop (nhds (schwinger loops).re)
  /-- Euclidean invariance of the Schwinger functions. -/
  euclidean_invariance : ∀ (g : Spacetime ≃ₗᵢ[ℝ] Spacetime) (v : Spacetime)
      (loops : List ContinuumLoop),
    schwinger (loops.map (fun γ => (γ.mapIsom g).translate v)) = schwinger loops
  /-- The Schwinger functions are the vacuum expectation values of the Wilson operators. -/
  vacuum_expectation : ∀ γ : ContinuumLoop,
    ⟪transfer.vacuum, wilson γ transfer.vacuum⟫_ℂ = schwinger [γ]
  /-- Osterwalder–Schrader reconstruction: Euclidean time evolution of time-zero Wilson
  observables is computed by the Schwinger functions. -/
  reconstruction : ∀ γ₁ γ₂ : ContinuumLoop, γ₁.IsTimeZero → γ₂.IsTimeZero → ∀ t : ℝ, 0 ≤ t →
    ⟪wilson γ₁ transfer.vacuum, transfer.T t (wilson γ₂ transfer.vacuum)⟫_ℂ
      = schwinger [γ₁.reflect, γ₂.timeShift t]
  /-- The vacuum is cyclic for the time-zero Wilson observables. -/
  vacuum_cyclic : Dense (X := space.carrier)
    ↑(Submodule.span ℂ
      {x | ∃ γ : ContinuumLoop, γ.IsTimeZero ∧ x = wilson γ transfer.vacuum})

variable (Γ : GaugeGroup)

/-- **Existence of quantum Yang–Mills on `ℝ⁴` with a positive mass gap** for the compact
gauge group `Γ`: there is a quantum Yang–Mills theory (a continuum limit of Wilson lattice
gauge theory satisfying the Osterwalder–Schrader/Wightman requirements) whose Hamiltonian
has a strictly positive spectral gap above the vacuum. -/
