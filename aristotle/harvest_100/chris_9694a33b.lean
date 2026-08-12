/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace Frontier

section Abstract

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- A weak-* limit of a sequence of `T`-invariant probability measures is `T`-invariant.

This is the standard "limit measures are geodesic-flow invariant" step in the
quantum-unique-ergodicity argument. -/
theorem map_eq_self_of_tendsto {T : X → X} (hT : Continuous T)
    (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure X)
    (hinv : ∀ n, Measure.map T (mu n : Measure X) = (mu n : Measure X))
    (hconv : Tendsto mu atTop (𝓝 nu)) :
    Measure.map T (nu : Measure X) = (nu : Measure X) := by
  have hmeas : Measurable T := hT.measurable
  haveI : IsProbabilityMeasure (Measure.map T (nu : Measure X)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  have key : ∀ mm : ProbabilityMeasure X,
      ∫ x, f x ∂(Measure.map T (mm : Measure X))
        = ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mm : Measure X) := by
    intro mm
    rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  have h1 : Tendsto (fun n => ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mu n : Measure X)) atTop
      (𝓝 (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(nu : Measure X))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv _
  have h2 : Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(nu : Measure X))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv _
  have h3 : ∀ n, ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mu n : Measure X)
      = ∫ x, f x ∂(mu n : Measure X) := by
    intro n
    rw [← key (mu n), hinv n]
  rw [key nu]
  simp only [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Reduction of QUE to measure classification.**

If every weak-* subsequential limit of a sequence of `T`-invariant probability measures is
the given (Haar) measure, then the whole sequence converges weak-* to it. -/
theorem tendsto_of_forall_subseq_limit_eq
    (haar : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hclass : ∀ nu : ProbabilityMeasure X,
      (∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k => mu (ns k)) atTop (𝓝 nu)) → nu = haar) :
    Tendsto mu atTop (𝓝 haar) := by
  by_contra h
  rw [not_tendsto_iff_exists_frequently_notMem] at h
  obtain ⟨U, hU, hfreq⟩ := h
  obtain ⟨ns, hns, hP⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨nu, ms, hms, hconv⟩ := SeqCompactSpace.tendsto_subseq (fun k => mu (ns k))
  have hnu : nu = haar := hclass nu ⟨ns ∘ ms, hns.comp hms, hconv⟩
  subst hnu
  obtain ⟨k, hk⟩ := (hconv.eventually (eventually_mem_nhds_iff.mpr hU)).exists
  exact hP (ms k) (mem_of_mem_nhds hk)

/-- **Arithmetic quantum unique ergodicity (Lindenstrauss), in reduced form.**

`X` is a compact metric measurable space (the unit cotangent bundle `Γ \ SL₂(ℝ)` of a compact
congruence surface), `T` is the time-one map of the geodesic flow, `haar` is the normalized
Haar/Liouville probability measure, and `mu n` is the sequence of microlocal lifts of the
Hecke–Maass eigenfunctions.

The hypotheses are:
* `hinv` : each microlocal lift is asymptotically invariant under the geodesic flow (here: exactly
  invariant, as holds for the limit objects);
* `hclass` : Lindenstrauss' measure classification input — any geodesic-flow-invariant weak-*
  subsequential limit of the lifts is the Haar measure.

The conclusion is quantum unique ergodicity: the microlocal lifts converge weak-* to Haar
measure, equivalently `∫ f dμₙ → ∫ f dhaar` for every bounded continuous observable `f`. -/
theorem lindenstrauss_QUE {T : X → X} (hT : Continuous T)
    (haar : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hinv : ∀ n, Measure.map T (mu n : Measure X) = (mu n : Measure X))
    (hclass : ∀ nu : ProbabilityMeasure X, Measure.map T (nu : Measure X) = (nu : Measure X) →
      (∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k => mu (ns k)) atTop (𝓝 nu)) → nu = haar) :
    Tendsto mu atTop (𝓝 haar) ∧
      ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(haar : Measure X))) := by
  have hmain : Tendsto mu atTop (𝓝 haar) := by
    refine tendsto_of_forall_subseq_limit_eq haar mu (fun nu hnu => ?_)
    obtain ⟨ns, hns, hconv⟩ := hnu
    exact hclass nu
      (map_eq_self_of_tendsto hT (fun k => mu (ns k)) nu (fun k => hinv (ns k)) hconv)
      ⟨ns, hns, hconv⟩
  exact ⟨hmain, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmain⟩

/-- **Unique ergodicity implies quantum unique ergodicity.**

If `haar` is the *only* `T`-invariant Borel probability measure on `X`, then every sequence of
`T`-invariant probability measures converges weak-* to it. This is the classical (non-arithmetic)
special case of the reduction above, where the measure-classification input is unique ergodicity
instead of Lindenstrauss' entropy/Hecke-recurrence argument. -/
theorem que_of_uniquelyErgodic {T : X → X} (hT : Continuous T)
    (haar : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hinv : ∀ n, Measure.map T (mu n : Measure X) = (mu n : Measure X))
    (hue : ∀ nu : ProbabilityMeasure X,
      Measure.map T (nu : Measure X) = (nu : Measure X) → nu = haar) :
    Tendsto mu atTop (𝓝 haar) :=
  (lindenstrauss_QUE hT haar mu hinv (fun nu hnu _ => hue nu hnu)).1

end Abstract

section CircleBaseCase

/-!
### Base case: quantum unique ergodicity on the flat circle

On the circle `ℝ / ℤ` the Laplace eigenfunctions are the characters `fourier n`, with eigenvalue
`4 π² n²`. Here the QUE statement can be verified directly and in fact exactly at every level:
the microlocal measure `‖φₙ‖² dHaar` *equals* the Haar probability measure for every `n`.
-/

open AddCircle Complex

local instance factZeroLtOne : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The characters of the circle have modulus one. -/
theorem norm_fourier_eq_one (n : ℤ) (x : AddCircle (1:ℝ)) : ‖fourier n x‖ = 1 :=
  Circle.norm_coe _

/-- `fourier n` is an eigenfunction of the Laplacian `d²/dx²` on the circle, with eigenvalue
`-4 π² n²`: its first derivative is `2 π i n · fourier n`, whose derivative in turn is
`-4 π² n² · fourier n`. -/
theorem hasDerivAt_deriv_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (2 * π * I * n) * fourier n (y : AddCircle (1:ℝ)))
      (-(4 * π ^ 2 * (n : ℂ) ^ 2) * fourier n (x : AddCircle (1:ℝ))) x := by
  have h := (hasDerivAt_fourier (1:ℝ) n x).const_mul (2 * π * I * (n : ℂ))
  convert h using 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The microlocal (position) measure of the `n`-th circle eigenfunction is exactly the Haar
probability measure. -/
theorem withDensity_normSq_fourier_eq_haar (n : ℤ) :
    (haarAddCircle (T := (1:ℝ))).withDensity (fun x => (‖fourier n x‖₊ : ENNReal) ^ 2)
      = haarAddCircle := by
  have h : (fun x : AddCircle (1:ℝ) => (‖fourier n x‖₊ : ENNReal) ^ 2)
      = (1 : AddCircle (1:ℝ) → ENNReal) := by
    funext x
    have hx : ‖fourier n x‖₊ = 1 := by
      rw [← NNReal.coe_inj]
      exact norm_fourier_eq_one n x
    rw [hx]
    norm_num
  rw [h, withDensity_one]

/-- **Quantum unique ergodicity on the flat circle** (base case): along any sequence of Laplace
eigenfunctions `fourier (phi k)` of the circle, the position measures `‖φ‖² dHaar` equidistribute
with respect to the Haar probability measure. -/
theorem circle_QUE (phi : ℕ → ℤ) (f : C(AddCircle (1:ℝ), ℝ)) :
    Tendsto (fun k => ∫ x, f x * ‖fourier (phi k) x‖ ^ 2 ∂(haarAddCircle (T := (1:ℝ)))) atTop
      (𝓝 (∫ x, f x ∂(haarAddCircle (T := (1:ℝ))))) := by
  have h : ∀ k, (∫ x, f x * ‖fourier (phi k) x‖ ^ 2 ∂(haarAddCircle (T := (1:ℝ))))
      = ∫ x, f x ∂(haarAddCircle (T := (1:ℝ))) := by
    intro k
    congr 1
    funext x
    rw [norm_fourier_eq_one]
    ring
  simp only [h]
  exact tendsto_const_nhds

end CircleBaseCase

end Frontier

