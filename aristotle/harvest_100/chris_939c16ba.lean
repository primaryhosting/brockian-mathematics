/-
Classical `XY`-type models with a continuous (rotation) symmetry, and the
Mermin–Wagner / Pfister "two–shift" bound on the magnetization in terms of the
Dirichlet energy of a cut-off function.
-/
import Mathlib

open MeasureTheory Real

noncomputable section

namespace MerminWagner

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`.  The continuous symmetry group of the
models below is the rotation group of this circle acting diagonally on all spins. -/
abbrev Spin : Type := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/
def scos : Spin → ℝ := Real.Angle.cos

@[simp] lemma scos_coe (x : ℝ) : scos ((x : Spin)) = Real.cos x := Real.Angle.cos_coe x

lemma continuous_scos : Continuous scos := Real.Angle.continuous_cos

lemma scos_le_one (z : Spin) : scos z ≤ 1 := by
  induction z using QuotientAddGroup.induction_on with
  | _ s => rw [scos_coe]; exact Real.cos_le_one s

lemma abs_scos_le_one (z : Spin) : |scos z| ≤ 1 := by
  induction z using QuotientAddGroup.induction_on with
  | _ s => rw [scos_coe]; exact Real.abs_cos_le_one s

/-- The parallelogram identity `cos(d+t) + cos(d-t) = 2 cos d cos t` on the circle. -/
lemma scos_add_add_sub (z : Spin) (t : ℝ) :
    scos (z + (t : Spin)) + scos (z - (t : Spin)) = 2 * scos z * Real.cos t := by
  induction z using QuotientAddGroup.induction_on with
  | _ s =>
    have h1 : ((s : Spin) + (t : Spin)) = ((s + t : ℝ) : Spin) := by push_cast; ring
    have h2 : ((s : Spin) - (t : Spin)) = ((s - t : ℝ) : Spin) := by push_cast; ring
    rw [h1, h2, scos_coe, scos_coe, scos_coe, Real.cos_add, Real.cos_sub]
    ring

lemma scos_sub_pi (z : Spin) : scos (z - ((Real.pi : ℝ) : Spin)) = -scos z :=
  Real.Angle.cos_sub_pi z

lemma scos_add_pi (z : Spin) : scos (z + ((Real.pi : ℝ) : Spin)) = -scos z :=
  Real.Angle.cos_add_pi z

variable {V : Type*} [Fintype V]

/-- The a-priori (Haar) measure on configuration space: the product of the Haar
measures of the circle.  It is invariant under the diagonal rotation action, and
more generally under any translation of the configuration. -/
def refMeasure (V : Type*) [Fintype V] : Measure (V → Spin) := Measure.pi fun _ => volume

instance : IsFiniteMeasure (refMeasure V) := by unfold refMeasure; infer_instance

instance : (refMeasure V).IsAddLeftInvariant := by unfold refMeasure; infer_instance

lemma refMeasure_univ_pos : 0 < (refMeasure V) Set.univ := by
  unfold refMeasure
  rw [Measure.pi_univ]
  simp [AddCircle.measure_univ]
  positivity

lemma integrable_of_continuous {F : (V → Spin) → ℝ} (hF : Continuous F) :
    Integrable F (refMeasure V) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

lemma integral_shift (F : (V → Spin) → ℝ) (u : V → Spin) :
    ∫ θ, F (θ + u) ∂(refMeasure V) = ∫ θ, F θ ∂(refMeasure V) := by
  have := integral_add_left_eq_self (μ := refMeasure V) F u
  simpa [add_comm] using this

/-- The energy of a configuration: a (ferromagnetic) rotation invariant pair
interaction, together with arbitrary single–site terms `b`, which encode boundary
conditions and external fields (these are the symmetry-breaking terms). -/
def energy (J : V → V → ℝ) (b : V → Spin → ℝ) (θ : V → Spin) : ℝ :=
    -∑ x, ∑ y, J x y * scos (θ x - θ y) + ∑ x, b x (θ x)

/-- The Gibbs weight `exp (-β H)` at inverse temperature `β`. -/
def gibbsWeight (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) (θ : V → Spin) : ℝ :=
    Real.exp (-β * energy J b θ)

/-- The partition function. -/
def partition (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) : ℝ :=
    ∫ θ, gibbsWeight β J b θ ∂(refMeasure V)

/-- The (unnormalised) Gibbs integral of an observable. -/
def gibbsInt (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) (g : (V → Spin) → ℝ) : ℝ :=
    ∫ θ, g θ * gibbsWeight β J b θ ∂(refMeasure V)

/-- The Gibbs expectation of an observable. -/
def gibbsAvg (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) (g : (V → Spin) → ℝ) : ℝ :=
    gibbsInt β J b g / partition β J b

/-- The magnetization at the site `x₀` measured along the direction `φ`, i.e. the
Gibbs expectation of `cos (θ x₀ - φ)`. -/
def magnetization (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) (x₀ : V) (φ : Spin) : ℝ :=
    gibbsAvg β J b (fun θ => scos (θ x₀ - φ))

/-- The Dirichlet energy of a function `f` with respect to the couplings `J`. -/
def dirichletEnergy (J : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, ∑ y, J x y * (f x - f y) ^ 2

lemma dirichletEnergy_nonneg {J : V → V → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (f : V → ℝ) :
    0 ≤ dirichletEnergy J f :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by positivity

section Continuity

variable {J : V → V → ℝ} {b : V → Spin → ℝ}

lemma continuous_energy (hb : ∀ x, Continuous (b x)) : Continuous (energy J b) := by
  unfold energy
  refine Continuous.add (continuous_finset_sum _ fun x _ => ?_).neg
    (continuous_finset_sum _ fun x _ => (hb x).comp (continuous_apply x))
  exact continuous_finset_sum _ fun y _ =>
    continuous_const.mul (continuous_scos.comp
      (((continuous_apply x).sub (continuous_apply y))))

lemma continuous_gibbsWeight (β : ℝ) (hb : ∀ x, Continuous (b x)) :
    Continuous (gibbsWeight β J b) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_energy hb))

lemma gibbsWeight_pos (β : ℝ) (θ : V → Spin) : 0 < gibbsWeight β J b θ := Real.exp_pos _

lemma partition_pos (β : ℝ) (hb : ∀ x, Continuous (b x)) : 0 < partition β J b := by
  have hcont : Continuous (gibbsWeight β J b) := continuous_gibbsWeight β hb
  obtain ⟨θ₀, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := V → Spin)) hcont.continuousOn
  have hc : 0 < gibbsWeight β J b θ₀ := gibbsWeight_pos β θ₀
  have hle : ∀ θ, gibbsWeight β J b θ₀ ≤ gibbsWeight β J b θ := fun θ =>
    hmin (Set.mem_univ θ)
  have h1 : ∫ _ : V → Spin, gibbsWeight β J b θ₀ ∂(refMeasure V) ≤ partition β J b := by
    refine integral_mono (integrable_const _) (integrable_of_continuous hcont) ?_
    intro θ; exact hle θ
  have h2 : (0:ℝ) < ∫ _ : V → Spin, gibbsWeight β J b θ₀ ∂(refMeasure V) := by
    rw [integral_const, smul_eq_mul]
    have : 0 < ((refMeasure V) Set.univ).toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨refMeasure_univ_pos, measure_lt_top _ _⟩
    positivity
  linarith

end Continuity

section MainBound

variable {J : V → V → ℝ} {b : V → Spin → ℝ} {f : V → ℝ} {β : ℝ} {x₀ : V} {φ : Spin}

/-- The shift of a configuration by `π f`. -/
def shift (f : V → ℝ) : V → Spin := fun x => ((Real.pi * f x : ℝ) : Spin)

/-- The key pointwise "spin-wave" estimate: shifting the configuration by `± π f`
costs at most `π²` times the Dirichlet energy of `f`, on average. -/
lemma energy_shift_bound (hJ : ∀ x y, 0 ≤ J x y) (hbf : ∀ x, f x ≠ 0 → b x = 0)
    (θ : V → Spin) :
    energy J b (θ + shift f) + energy J b (θ - shift f)
      ≤ 2 * energy J b θ + Real.pi ^ 2 * dirichletEnergy J f := by
  have hb : ∀ x, b x ((θ + shift f) x) + b x ((θ - shift f) x) - 2 * b x (θ x) = 0 := by
    intro x
    by_cases hfx : f x = 0
    · have : shift f x = (0 : Spin) := by
        simp [shift, hfx]
      simp [this]
    · simp [hbf x hfx]
  have hpair : ∀ x y,
      -(J x y * scos ((θ + shift f) x - (θ + shift f) y))
        - J x y * scos ((θ - shift f) x - (θ - shift f) y)
        + 2 * (J x y * scos (θ x - θ y))
      ≤ J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) := by
    intro x y
    set d : Spin := θ x - θ y with hd
    set t : ℝ := Real.pi * (f x - f y) with ht
    have e1 : (θ + shift f) x - (θ + shift f) y = d + (t : Spin) := by
      simp only [Pi.add_apply, shift, hd, ht]
      push_cast
      ring
    have e2 : (θ - shift f) x - (θ - shift f) y = d - (t : Spin) := by
      simp only [Pi.sub_apply, shift, hd, ht]
      push_cast
      ring
    rw [e1, e2]
    have key : scos (d + (t : Spin)) + scos (d - (t : Spin)) = 2 * scos d * Real.cos t :=
      scos_add_add_sub d t
    have hcos : 1 - Real.cos t ≤ t ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hsd : scos d ≤ 1 := scos_le_one d
    have hJxy := hJ x y
    have expand :
        -(J x y * scos (d + (t : Spin))) - J x y * scos (d - (t : Spin))
          + 2 * (J x y * scos d)
          = 2 * J x y * scos d * (1 - Real.cos t) := by
      have : J x y * scos (d + (t : Spin)) + J x y * scos (d - (t : Spin))
          = J x y * (2 * scos d * Real.cos t) := by rw [← mul_add, key]
      nlinarith [this]
    rw [expand]
    have h1 : 2 * J x y * scos d * (1 - Real.cos t) ≤ 2 * J x y * (1 - Real.cos t) := by
      have h0 : 0 ≤ 1 - Real.cos t := by linarith
      nlinarith
    have h2 : 2 * J x y * (1 - Real.cos t) ≤ J x y * t ^ 2 := by nlinarith
    have h3 : J x y * t ^ 2 = J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) := by
      rw [ht]; ring
    linarith
  have hsum :
      (∑ x, ∑ y, (-(J x y * scos ((θ + shift f) x - (θ + shift f) y))
        - J x y * scos ((θ - shift f) x - (θ - shift f) y)
        + 2 * (J x y * scos (θ x - θ y))))
        ≤ ∑ x, ∑ y, J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
  have hbsum : ∑ x, (b x ((θ + shift f) x) + b x ((θ - shift f) x) - 2 * b x (θ x)) = 0 :=
    Finset.sum_eq_zero fun x _ => hb x
  have hD : ∑ x, ∑ y, J x y * (Real.pi ^ 2 * (f x - f y) ^ 2)
      = Real.pi ^ 2 * dirichletEnergy J f := by
    unfold dirichletEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  unfold energy
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at *
  nlinarith [hsum, hbsum, hD]

end MainBound

end MerminWagner

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

