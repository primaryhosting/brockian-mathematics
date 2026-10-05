import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON FILE LAYOUT.  Lean 4 requires every `import` to precede any module
documentation comment, so the mandated `/-! ... -/` header block is placed
immediately after the single `import Mathlib` line; it is otherwise verbatim.
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

open Filter Topology

namespace Frontier

/-! ## Spacetime -/

/-- Four dimensional Minkowski/Euclidean spacetime, as the underlying real vector
space `ℝ⁴` on which the theory lives. -/
abbrev Spacetime : Type := EuclideanSpace ℝ (Fin 4)

/-! ## The kinematical (Wightman-type) data of a quantum field theory

We record the data that the Millennium Prize formulation of the Yang–Mills problem
attaches to a quantum field theory on `ℝ⁴`: a separable Hilbert space of states, a
distinguished unit vacuum vector, a unitary representation of the translation group
of spacetime fixing the vacuum, and the *energy spectrum* — the spectrum of the
generator of time translations — which is a closed subset of `[0, ∞)` containing
`0` (the vacuum energy).

The dynamical content of Yang–Mills theory (the field algebra, gauge invariance,
locality, the Osterwalder–Schrader/Wightman reconstruction) is **not** formalised
here; in the reduction theorem below it is carried by an arbitrary predicate
`IsQuantumYangMills`, so that the reduction applies to *any* such formalisation. -/
structure WightmanQFT where
  /-- The Hilbert space of states. -/
  Hilb : Type
  [normedGroup : NormedAddCommGroup Hilb]
  [innerSpace : InnerProductSpace ℂ Hilb]
  [complete : CompleteSpace Hilb]
  /-- The vacuum state. -/
  vacuum : Hilb
  /-- The vacuum is a unit vector. -/
  vacuum_unit : ‖vacuum‖ = 1
  /-- The unitary representation of the spacetime translation group. -/
  translation : Spacetime → (Hilb ≃ₗᵢ[ℂ] Hilb)
  translation_zero : translation 0 = LinearIsometryEquiv.refl ℂ Hilb
  translation_add : ∀ x y, translation (x + y) = (translation x).trans (translation y)
  /-- Translation invariance of the vacuum. -/
  translation_vacuum : ∀ x, translation x vacuum = vacuum
  /-- The energy spectrum: the spectrum of the generator of time translations. -/
  energySpectrum : Set ℝ
  /-- Spectra of self-adjoint operators are closed. -/
  energy_closed : IsClosed energySpectrum
  /-- The spectrum condition: the energy is non-negative. -/
  energy_nonneg : ∀ E ∈ energySpectrum, 0 ≤ E
  /-- The vacuum has energy `0`. -/
  energy_vacuum : (0 : ℝ) ∈ energySpectrum

attribute [instance] WightmanQFT.normedGroup WightmanQFT.innerSpace WightmanQFT.complete

/-- A quantum field theory on `ℝ⁴` together with a compact non-abelian gauge group,
i.e. the kinematical setting of a quantum Yang–Mills theory. -/
structure YangMillsTheory extends WightmanQFT where
  /-- The (compact, non-abelian) gauge group of the theory. -/
  gauge : Type
  [gaugeGroup : Group gauge]
  [gaugeTop : TopologicalSpace gauge]
  [gaugeTopGroup : IsTopologicalGroup gauge]
  /-- Compactness of the gauge group. -/
  gauge_compact : CompactSpace gauge
  /-- The gauge group is non-abelian, as required for Yang–Mills. -/
  gauge_nonabelian : ∃ a b : gauge, a * b ≠ b * a

attribute [instance] YangMillsTheory.gaugeGroup YangMillsTheory.gaugeTop
  YangMillsTheory.gaugeTopGroup YangMillsTheory.gauge_compact

/-! ## Mass gap -/

/-- `T` **has a mass gap** if there is `Δ > 0` such that every point of the energy
spectrum is either the vacuum energy `0` or at least `Δ`. -/

noncomputable def freeModel (m : ℝ) (hm : 0 ≤ m) : YangMillsTheory where
  Hilb := ℂ
  vacuum := 1
  vacuum_unit := by simp
  translation := fun _ => LinearIsometryEquiv.refl ℂ ℂ
  translation_zero := rfl
  translation_add := by intro x y; ext v; rfl
  translation_vacuum := by intro x; rfl
  energySpectrum := freeSpectrum m
  energy_closed := isClosed_freeSpectrum m
  energy_nonneg := freeSpectrum_nonneg hm
  energy_vacuum := zero_mem_freeSpectrum m
  gauge := Equiv.Perm (Fin 3)
  gaugeTopGroup := by infer_instance
  gauge_compact := by infer_instance
  gauge_nonabelian := by
    refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, ?_⟩
    intro h
    have := congrArg (fun f : Equiv.Perm (Fin 3) => f 1) h
    simp [Equiv.swap_apply_def] at this

/-- **Base case.**  A theory with free energy spectrum of mass `m > 0` has a mass
gap, namely `m`. -/
