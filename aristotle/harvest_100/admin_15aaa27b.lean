import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A *quantum limit* of a sequence of probability measures `mu` is a weak-* limit of some
subsequence of `mu`.  In the arithmetic setting, `mu n` is the microlocal lift of the `n`-th Hecke
eigenform and its quantum limits are the measures classified by Lindenstrauss's measure rigidity
theorem. -/
def IsQuantumLimit (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure X) : Prop :=
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (fun k => mu (phi k)) atTop (𝓝 nu)

/-- **Arithmetic Quantum Unique Ergodicity (Lindenstrauss), reduction to measure rigidity.**

On a compact metric (Borel) space `X` — the model for a compact congruence surface, or, after the
microlocal lift, for its unit tangent bundle — let `vol` be the normalized volume measure and let
`mu n` be the sequence of probability measures attached to a sequence of eigenfunctions.

If the *measure classification* input holds, i.e. every quantum limit of the sequence `mu` is the
volume measure `vol` (this is exactly what Lindenstrauss's measure rigidity theorem provides for
Hecke–Maass eigenforms: any quantum limit is geodesic-flow invariant, Hecke recurrent and of
positive entropy on almost every ergodic component, hence equals the volume measure), then the whole
sequence `mu` converges weak-* to `vol`: quantum unique ergodicity holds. -/
theorem lindenstrauss_QUE (vol : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hrigid : ∀ nu : ProbabilityMeasure X, IsQuantumLimit mu nu → nu = vol) :
    Tendsto mu atTop (𝓝 vol) := by
  by_contra hcon
  -- Failure of convergence gives an open neighbourhood `U` of `vol` avoided infinitely often.
  rw [tendsto_iff_forall_eventually_mem] at hcon
  push_neg at hcon
  obtain ⟨s, hs, hns⟩ := hcon
  obtain ⟨U, hUs, hUopen, hUvol⟩ := mem_nhds_iff.mp hs
  have hfreq : ∃ᶠ n in atTop, mu n ∈ Uᶜ := by
    refine hns.mono ?_
    intro n hn hmem
    exact hn (hUs hmem)
  obtain ⟨phi, hphi, hphimem⟩ := Filter.extraction_of_frequently_atTop hfreq
  -- Weak-* sequential compactness of the space of probability measures on a compact metric space.
  obtain ⟨nu, -, psi, hpsi, hconv⟩ :=
    (isSeqCompact_univ (X := ProbabilityMeasure X)) (x := fun k => mu (phi k))
      (fun _ => Set.mem_univ _)
  -- The limit is a quantum limit, hence equals `vol` by measure rigidity.
  have hql : IsQuantumLimit mu nu := ⟨phi ∘ psi, hphi.comp hpsi, hconv⟩
  have hnu : nu = vol := hrigid nu hql
  -- But the limit lies in the closed set `Uᶜ`, which does not contain `vol`.
  have : nu ∈ Uᶜ :=
    (hUopen.isClosed_compl).mem_of_tendsto hconv (Filter.Eventually.of_forall
      (fun k => hphimem (psi k)))
  exact this (hnu ▸ hUvol)

/-- Integral form of quantum unique ergodicity: under the measure-rigidity hypothesis, the
expectations of every bounded continuous observable against `mu n` converge to its average against
the volume measure. -/
theorem lindenstrauss_QUE_integral (vol : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hrigid : ∀ nu : ProbabilityMeasure X, IsQuantumLimit mu nu → nu = vol)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop (𝓝 (∫ x, f x ∂(vol : Measure X))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (lindenstrauss_QUE vol mu hrigid)) f

omit [CompactSpace X] in
/-- Sanity check (base case): the only quantum limit of a constant sequence of probability
measures is that measure itself, so the hypothesis of `Frontier.lindenstrauss_QUE` is satisfiable
and the theorem indeed yields quantum unique ergodicity in that degenerate case. -/
theorem isQuantumLimit_const_iff (vol nu : ProbabilityMeasure X) :
    IsQuantumLimit (fun _ : ℕ => vol) nu ↔ nu = vol := by
  constructor
  · rintro ⟨phi, -, hconv⟩
    exact tendsto_nhds_unique hconv tendsto_const_nhds
  · rintro rfl
    exact ⟨id, strictMono_id, tendsto_const_nhds⟩

/-- Base case of `Frontier.lindenstrauss_QUE`: a constant sequence converges to its value. -/
theorem lindenstrauss_QUE_const (vol : ProbabilityMeasure X) :
    Tendsto (fun _ : ℕ => vol) atTop (𝓝 vol) :=
  lindenstrauss_QUE vol (fun _ => vol) fun _ h => (isQuantumLimit_const_iff vol _).mp h

/-- **Quantum unique ergodicity in eigenfunction form.**

Let `psi n : X → ℂ` be a sequence of `L²`-normalized (measurable) eigenfunctions, and let `mu n` be
the associated probability measures `|psi n|² dvol`.  If every quantum limit of `mu` is the volume
measure (the conclusion of Lindenstrauss's measure classification theorem in the arithmetic
setting), then the mass of the eigenfunctions equidistributes:
`∫ f · |psi n|² dvol → ∫ f dvol` for every continuous observable `f`. -/
theorem lindenstrauss_QUE_eigenfunctions (vol : ProbabilityMeasure X)
    (psi : ℕ → X → ℂ) (hpsi : ∀ n, Measurable (psi n)) (mu : ℕ → ProbabilityMeasure X)
    (hmu : ∀ n, (mu n : Measure X)
      = (vol : Measure X).withDensity (fun x => ((‖psi n x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)))
    (hrigid : ∀ nu : ProbabilityMeasure X, IsQuantumLimit mu nu → nu = vol) (f : C(X, ℝ)) :
    Tendsto (fun n => ∫ x, ‖psi n x‖ ^ 2 * f x ∂(vol : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(vol : Measure X))) := by
  have key := lindenstrauss_QUE_integral vol mu hrigid (BoundedContinuousFunction.mkOfCompact f)
  refine key.congr (fun n => ?_)
  have hmeas : Measurable (fun x => (‖psi n x‖₊ ^ 2 : ℝ≥0)) :=
    ((hpsi n).nnnorm).pow_const 2
  rw [hmu n, integral_withDensity_eq_integral_smul hmeas]
  simp [NNReal.smul_def]

end Frontier

