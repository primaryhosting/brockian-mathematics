/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/
def xyEnergy (bonds : Finset ι) (src tgt : ι → S) (J h : ℝ) (θ : Cfg S) : ℝ :=
  -J * ∑ b ∈ bonds, cosC (θ (src b) - θ (tgt b)) - h * ∑ x, cosC (θ x)

/-- The configuration obtained by rotating the spin at `x` by the angle `v x`. -/
def spinWave (v : S → ℝ) : Cfg S := fun x => ((v x : ℝ) : Circ)

/-- The discrete Dirichlet energy of a profile `v`. -/
def dirichlet (bonds : Finset ι) (src tgt : ι → S) (v : S → ℝ) : ℝ :=
  ∑ b ∈ bonds, (v (src b) - v (tgt b)) ^ 2

/-- The squared `ℓ²` norm of a profile `v`. -/
def sqNorm (v : S → ℝ) : ℝ := ∑ x, (v x) ^ 2

omit [Fintype S] in
lemma dirichlet_nonneg (bonds : Finset ι) (src tgt : ι → S) (v : S → ℝ) :
    0 ≤ dirichlet bonds src tgt v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqNorm_nonneg (v : S → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_xyEnergy (bonds : Finset ι) (src tgt : ι → S) (J h : ℝ) :
    Continuous (xyEnergy bonds src tgt J h) := by
  unfold xyEnergy
  refine Continuous.sub (continuous_const.mul (continuous_finset_sum _ fun b _ => ?_))
    (continuous_const.mul (continuous_finset_sum _ fun x _ => ?_))
  · exact continuous_cosC.comp ((continuous_apply _).sub (continuous_apply _))
  · exact continuous_cosC.comp (continuous_apply _)

/-- The magnetization at the site `o`: the Gibbs expectation of `cos` of the spin there. -/
def magnetization (bonds : Finset ι) (src tgt : ι → S) (β J h : ℝ) (o : S) : ℝ :=
  gibbsAvg (xyEnergy bonds src tgt J h) β (fun θ => cosC (θ o))

section Shift

variable (bonds : Finset ι) (src tgt : ι → S) (J h : ℝ)

lemma spinWave_apply (v : S → ℝ) (x : S) : spinWave v x = ((v x : ℝ) : Circ) := rfl

/-- Second-difference bound for the XY energy under a spin-wave shift: the cost is at most
the Dirichlet energy of the profile plus the field term. -/
lemma xyEnergy_shift_bound (hJ : 0 ≤ J) (hh : 0 ≤ h) (v : S → ℝ) (θ : Cfg S) :
    xyEnergy bonds src tgt J h (θ + spinWave v)
      + xyEnergy bonds src tgt J h (θ - spinWave v)
      ≤ 2 * xyEnergy bonds src tgt J h θ
        + (J * dirichlet bonds src tgt v + h * sqNorm v) := by
  have hbond : -(dirichlet bonds src tgt v) ≤
      (∑ b ∈ bonds, cosC ((θ + spinWave v) (src b) - (θ + spinWave v) (tgt b)))
      + (∑ b ∈ bonds, cosC ((θ - spinWave v) (src b) - (θ - spinWave v) (tgt b)))
      - 2 * ∑ b ∈ bonds, cosC (θ (src b) - θ (tgt b)) := by
    rw [dirichlet, ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    have e1 : (θ + spinWave v) (src b) - (θ + spinWave v) (tgt b)
        = (θ (src b) - θ (tgt b)) + ((v (src b) - v (tgt b) : ℝ) : Circ) := by
      have hc : ((v (src b) - v (tgt b) : ℝ) : Circ)
          = ((v (src b) : ℝ) : Circ) - ((v (tgt b) : ℝ) : Circ) := rfl
      simp only [Pi.add_apply, spinWave_apply, hc]
      abel
    have e2 : (θ - spinWave v) (src b) - (θ - spinWave v) (tgt b)
        = (θ (src b) - θ (tgt b)) - ((v (src b) - v (tgt b) : ℝ) : Circ) := by
      have hc : ((v (src b) - v (tgt b) : ℝ) : Circ)
          = ((v (src b) : ℝ) : Circ) - ((v (tgt b) : ℝ) : Circ) := rfl
      simp only [Pi.sub_apply, spinWave_apply, hc]
      abel
    rw [e1, e2]
    exact cosC_second_difference _ _
  have hfield : -(sqNorm v) ≤
      (∑ x, cosC ((θ + spinWave v) x)) + (∑ x, cosC ((θ - spinWave v) x))
      - 2 * ∑ x, cosC (θ x) := by
    rw [sqNorm, ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have e1 : (θ + spinWave v) x = θ x + ((v x : ℝ) : Circ) := rfl
    have e2 : (θ - spinWave v) x = θ x - ((v x : ℝ) : Circ) := rfl
    rw [e1, e2]
    exact cosC_second_difference _ _
  unfold xyEnergy
  nlinarith [hbond, hfield, hJ, hh]

end Shift

/-- **Finite–volume Mermin–Wagner bound.**  For the classical XY model with nonnegative
coupling and field, the magnetization at a site `o` is bounded by the energy cost of a
spin-wave profile `v` that rotates the spin at `o` by the angle `π`. -/
theorem magnetization_bound (bonds : Finset ι) (src tgt : ι → S) (β J h : ℝ)
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (o : S) (v : S → ℝ) (hv : v o = Real.pi) :
    |magnetization bonds src tgt β J h o|
      ≤ β * (J * dirichlet bonds src tgt v + h * sqNorm v) / 2 := by
  set H := xyEnergy bonds src tgt J h with hH
  have hHc : Continuous H := continuous_xyEnergy bonds src tgt J h
  set K : ℝ := J * dirichlet bonds src tgt v + h * sqNorm v with hKdef
  have hK0 : 0 ≤ K := by
    have := dirichlet_nonneg bonds src tgt v
    have := sqNorm_nonneg v
    positivity
  set W : Cfg S := spinWave v with hW
  have hKshift : ∀ θ : Cfg S, H (θ + W) + H (θ - W) ≤ 2 * H θ + K :=
    fun θ => xyEnergy_shift_bound bonds src tgt J h hJ hh v θ
  set m : ℝ := magnetization bonds src tgt β J h o with hm
  have hmcos : gibbsAvg H β (fun θ => cosC (θ o)) = m := rfl
  have hcosC : Continuous fun θ : Cfg S => cosC (θ o) :=
    continuous_cosC.comp (continuous_apply _)
  -- the two shifted observables
  have hWo : W o = ((Real.pi : ℝ) : Circ) := by rw [hW, spinWave_apply, hv]
  have hshift_add : ∀ θ : Cfg S, cosC ((θ + W) o) = -cosC (θ o) := by
    intro θ
    have : (θ + W) o = θ o + ((Real.pi : ℝ) : Circ) := by
      simp only [Pi.add_apply, hWo]
    rw [this, cosC_add_pi]
  have hshift_sub : ∀ θ : Cfg S, cosC ((θ - W) o) = -cosC (θ o) := by
    intro θ
    have : (θ - W) o = θ o - ((Real.pi : ℝ) : Circ) := by
      simp only [Pi.sub_apply, hWo]
    rw [this, cosC_sub_pi]
  have hexp : 1 - β * K / 2 ≤ Real.exp (-(β * K) / 2) := by
    have := Real.add_one_le_exp (-(β * K) / 2)
    linarith
  have hexp1 : Real.exp (-(β * K) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ β * K := mul_nonneg hβ hK0
    linarith
  have hexppos : 0 < Real.exp (-(β * K) / 2) := Real.exp_pos _
  -- upper bound on m, using the observable 1 + cos
  have hupper : m ≤ β * K / 2 := by
    have hA : Continuous fun θ : Cfg S => 1 + cosC (θ o) := continuous_const.add hcosC
    have hA0 : ∀ θ : Cfg S, 0 ≤ 1 + cosC (θ o) := by
      intro θ
      have := abs_cosC_le_one (θ o)
      cases abs_le.mp this with
      | intro h1 h2 => linarith
    have hkey := gibbs_shift_ineq hHc hA hA0 (β := β) (K := K) hβ W hKshift
    have e0 : gibbsAvg H β (fun θ => 1 + cosC (θ o)) = 1 + m := by
      rw [gibbsAvg_add hHc continuous_const hcosC, gibbsAvg_const hHc, hmcos]
    have e1 : gibbsAvg H β (fun θ => 1 + cosC ((θ + W) o)) = 1 - m := by
      have : (fun θ : Cfg S => 1 + cosC ((θ + W) o)) = fun θ => 1 + -cosC (θ o) := by
        funext θ; rw [hshift_add]
      rw [this, gibbsAvg_add hHc continuous_const hcosC.neg, gibbsAvg_const hHc,
        gibbsAvg_neg, hmcos]
      ring
    have e2 : gibbsAvg H β (fun θ => 1 + cosC ((θ - W) o)) = 1 - m := by
      have : (fun θ : Cfg S => 1 + cosC ((θ - W) o)) = fun θ => 1 + -cosC (θ o) := by
        funext θ; rw [hshift_sub]
      rw [this, gibbsAvg_add hHc continuous_const hcosC.neg, gibbsAvg_const hHc,
        gibbsAvg_neg, hmcos]
      ring
    rw [e0, e1, e2] at hkey
    rcases le_or_gt m 0 with hneg | hpos
    · have : 0 ≤ β * K / 2 := by positivity
      linarith
    · nlinarith [hkey, hexp, hexppos, hpos]
  -- lower bound on m, using the observable 1 - cos
  have hlower : -(β * K / 2) ≤ m := by
    have hA : Continuous fun θ : Cfg S => 1 - cosC (θ o) := continuous_const.sub hcosC
    have hA0 : ∀ θ : Cfg S, 0 ≤ 1 - cosC (θ o) := by
      intro θ
      have := abs_cosC_le_one (θ o)
      cases abs_le.mp this with
      | intro h1 h2 => linarith
    have hkey := gibbs_shift_ineq hHc hA hA0 (β := β) (K := K) hβ W hKshift
    have e0 : gibbsAvg H β (fun θ => 1 - cosC (θ o)) = 1 - m := by
      have : (fun θ : Cfg S => 1 - cosC (θ o)) = fun θ => 1 + -cosC (θ o) := by
        funext θ; ring
      rw [this, gibbsAvg_add hHc continuous_const hcosC.neg, gibbsAvg_const hHc,
        gibbsAvg_neg, hmcos]
      ring
    have e1 : gibbsAvg H β (fun θ => 1 - cosC ((θ + W) o)) = 1 + m := by
      have : (fun θ : Cfg S => 1 - cosC ((θ + W) o)) = fun θ => 1 + cosC (θ o) := by
        funext θ; rw [hshift_add]; ring
      rw [this, gibbsAvg_add hHc continuous_const hcosC, gibbsAvg_const hHc, hmcos]
    have e2 : gibbsAvg H β (fun θ => 1 - cosC ((θ - W) o)) = 1 + m := by
      have : (fun θ : Cfg S => 1 - cosC ((θ - W) o)) = fun θ => 1 + cosC (θ o) := by
        funext θ; rw [hshift_sub]; ring
      rw [this, gibbsAvg_add hHc continuous_const hcosC, gibbsAvg_const hHc, hmcos]
    rw [e0, e1, e2] at hkey
    rcases le_or_gt 0 m with hpos | hneg
    · have : 0 ≤ β * K / 2 := by positivity
      linarith
    · nlinarith [hkey, hexp, hexppos, hneg]
  rw [abs_le]
  constructor
  · linarith [hlower]
  · linarith [hupper]

end

end Phys

/-
Core: the circle, configuration spaces, Gibbs averages, and the key
"approximate convexity under a spin wave shift" inequality.
-/
import Mathlib

open MeasureTheory Real

namespace Phys

noncomputable section

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The single–spin space of the classical XY model: the circle `ℝ / 2πℤ`. -/
abbrev Circ := AddCircle (2 * Real.pi)

/-- The space of spin configurations on a finite set of sites `S`. -/
abbrev Cfg (S : Type) [Fintype S] := S → Circ

/-- Cosine, viewed as a function on the circle. -/
def cosC : Circ → ℝ := Real.cos_periodic.lift

@[simp] lemma cosC_coe (a : ℝ) : cosC ((a : ℝ) : Circ) = Real.cos a :=
  Real.cos_periodic.lift_coe a

lemma continuous_cosC : Continuous cosC := by
  unfold cosC Function.Periodic.lift
  exact continuous_coinduced_dom.mpr Real.continuous_cos

lemma abs_cosC_le_one (z : Circ) : |cosC z| ≤ 1 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  simpa using Real.abs_cos_le_one a

/-- The elementary trigonometric inequality behind the spin–wave estimate:
shifting a spin by `± s` costs at most `s ^ 2` in second difference. -/
lemma cosC_second_difference (z : Circ) (s : ℝ) :
    -(s ^ 2) ≤ cosC (z + ((s : ℝ) : Circ)) + cosC (z - ((s : ℝ) : Circ)) - 2 * cosC z := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  have h1 : ((a : ℝ) : Circ) + ((s : ℝ) : Circ) = ((a + s : ℝ) : Circ) := rfl
  have h2 : ((a : ℝ) : Circ) - ((s : ℝ) : Circ) = ((a - s : ℝ) : Circ) := rfl
  show -(s ^ 2) ≤ cosC (((a : ℝ) : Circ) + _) + cosC (((a : ℝ) : Circ) - _) - 2 * cosC ((a : ℝ) : Circ)
  rw [h1, h2, cosC_coe, cosC_coe, cosC_coe]
  have hc : Real.cos (a + s) + Real.cos (a - s) = 2 * Real.cos a * Real.cos s := by
    rw [Real.cos_add, Real.cos_sub]; ring
  rw [hc]
  have h3 : 1 - s ^ 2 / 2 ≤ Real.cos s := one_sub_sq_div_two_le_cos
  have h4 : Real.cos s ≤ 1 := Real.cos_le_one s
  have h5 : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
  have h6 : -1 ≤ Real.cos a := (abs_le.mp h5).1
  have h7 : Real.cos a ≤ 1 := (abs_le.mp h5).2
  nlinarith [sq_nonneg s, sq_nonneg (Real.cos a - 1), sq_nonneg (Real.cos a + 1)]

lemma cosC_add_pi (z : Circ) : cosC (z + ((Real.pi : ℝ) : Circ)) = -cosC z := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  have h1 : ((a : ℝ) : Circ) + ((Real.pi : ℝ) : Circ) = ((a + Real.pi : ℝ) : Circ) := rfl
  show cosC (((a : ℝ) : Circ) + _) = -cosC ((a : ℝ) : Circ)
  rw [h1, cosC_coe, cosC_coe, Real.cos_add_pi]

lemma cosC_sub_pi (z : Circ) : cosC (z - ((Real.pi : ℝ) : Circ)) = -cosC z := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  have h1 : ((a : ℝ) : Circ) - ((Real.pi : ℝ) : Circ) = ((a - Real.pi : ℝ) : Circ) := rfl
  show cosC (((a : ℝ) : Circ) - _) = -cosC ((a : ℝ) : Circ)
  rw [h1, cosC_coe, cosC_coe, Real.cos_sub_pi]

section Gibbs

variable {S : Type} [Fintype S]

lemma integrable_of_continuous {g : Cfg S → ℝ} (hg : Continuous g) :
    Integrable g (volume : Measure (Cfg S)) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

lemma volume_univ_pos : 0 < (volume : Measure (Cfg S)) Set.univ := by
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  simp only [AddCircle.measure_univ]
  rw [Finset.prod_const]
  refine pos_iff_ne_zero.mpr ?_
  simp only [ne_eq, pow_eq_zero_iff', not_and, ENNReal.ofReal_eq_zero]
  intro h
  exact absurd h (not_le.mpr (by positivity))

/-- The partition function of a Hamiltonian `H` at inverse temperature `β`. -/
def gibbsZ (H : Cfg S → ℝ) (β : ℝ) : ℝ := ∫ θ, Real.exp (-β * H θ)

/-- The Gibbs expectation of an observable `A`. -/
def gibbsAvg (H : Cfg S → ℝ) (β : ℝ) (A : Cfg S → ℝ) : ℝ :=
  (∫ θ, A θ * Real.exp (-β * H θ)) / gibbsZ H β

lemma gibbsZ_pos {H : Cfg S → ℝ} (hH : Continuous H) (β : ℝ) : 0 < gibbsZ H β := by
  have hfc : Continuous fun θ : Cfg S => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hH)
  obtain ⟨θ₀, -, hθ₀'⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hfc.continuousOn
  have hθ₀ : ∀ y : Cfg S, Real.exp (-β * H θ₀) ≤ Real.exp (-β * H y) :=
    fun y => hθ₀' (Set.mem_univ y)
  have hvol : 0 < ((volume : Measure (Cfg S)) Set.univ).toReal :=
    ENNReal.toReal_pos (ne_of_gt volume_univ_pos) (measure_ne_top _ _)
  have hmono : ∫ _ : Cfg S, Real.exp (-β * H θ₀) ≤ ∫ θ, Real.exp (-β * H θ) :=
    integral_mono (integrable_const _) (integrable_of_continuous hfc) hθ₀
  have hconst : ∫ _ : Cfg S, Real.exp (-β * H θ₀)
      = ((volume : Measure (Cfg S)) Set.univ).toReal * Real.exp (-β * H θ₀) := by
    simp [integral_const, smul_eq_mul, measureReal_def]
  have : 0 < ((volume : Measure (Cfg S)) Set.univ).toReal * Real.exp (-β * H θ₀) := by
    have := Real.exp_pos (-β * H θ₀); positivity
  unfold gibbsZ
  linarith [hmono, hconst ▸ hmono]

lemma integrable_obs {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A) (β : ℝ) :
    Integrable (fun θ => A θ * Real.exp (-β * H θ)) (volume : Measure (Cfg S)) :=
  integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul hH)))

lemma gibbsAvg_add {H A B : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A)
    (hB : Continuous B) (β : ℝ) :
    gibbsAvg H β (fun θ => A θ + B θ) = gibbsAvg H β A + gibbsAvg H β B := by
  unfold gibbsAvg
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_obs hH hA β) (integrable_obs hH hB β)]
  congr 1 with θ
  ring

lemma gibbsAvg_const {H : Cfg S → ℝ} (hH : Continuous H) (β c : ℝ) :
    gibbsAvg H β (fun _ => c) = c := by
  have hZ := gibbsZ_pos hH β
  unfold gibbsAvg
  have hz : (∫ θ : Cfg S, Real.exp (-β * H θ)) = gibbsZ H β := rfl
  rw [integral_const_mul, hz, mul_div_assoc, div_self (ne_of_gt hZ), mul_one]

lemma gibbsAvg_neg {H A : Cfg S → ℝ} (β : ℝ) :
    gibbsAvg H β (fun θ => -A θ) = -gibbsAvg H β A := by
  unfold gibbsAvg
  rw [← neg_div]
  congr 1
  rw [← integral_neg]
  congr 1 with θ
  ring

/-- Two exponentials dominate twice the exponential of their midpoint (AM–GM). -/
lemma two_exp_mid_le (u v : ℝ) : 2 * Real.exp ((u + v) / 2) ≤ Real.exp u + Real.exp v := by
  have h := two_mul_le_add_sq (Real.exp (u / 2)) (Real.exp (v / 2))
  have hu : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hv : Real.exp (v / 2) ^ 2 = Real.exp v := by
    rw [sq, ← Real.exp_add]; ring_nf
  have huv : Real.exp (u / 2) * Real.exp (v / 2) = Real.exp ((u + v) / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hu, hv] at h
  calc 2 * Real.exp ((u + v) / 2) = 2 * Real.exp (u / 2) * Real.exp (v / 2) := by
        rw [mul_assoc, huv]
    _ ≤ Real.exp u + Real.exp v := h

/-- **Key inequality.**  If shifting a configuration by `± w` raises the energy, in second
difference, by at most `K`, then the Gibbs average of a nonnegative observable is almost
convex along the shift.  This is the finite–volume form of the spin–wave (Mermin–Wagner)
argument: it uses only translation invariance of the a priori measure. -/
lemma gibbs_shift_ineq {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A)
    (hA0 : ∀ θ, 0 ≤ A θ) {β K : ℝ} (hβ : 0 ≤ β) (w : Cfg S)
    (hK : ∀ θ, H (θ + w) + H (θ - w) ≤ 2 * H θ + K) :
    2 * Real.exp (-(β * K) / 2) * gibbsAvg H β A
      ≤ gibbsAvg H β (fun θ => A (θ + w)) + gibbsAvg H β (fun θ => A (θ - w)) := by
  have hZ := gibbsZ_pos hH β
  have hAw : Continuous fun θ : Cfg S => A (θ + w) := hA.comp (continuous_id.add continuous_const)
  have hAw' : Continuous fun θ : Cfg S => A (θ - w) := hA.comp (continuous_id.sub continuous_const)
  -- rewrite the two shifted numerators using translation invariance
  have key1 : ∫ θ, A (θ + w) * Real.exp (-β * H θ)
      = ∫ θ, A θ * Real.exp (-β * H (θ - w)) := by
    have := integral_add_right_eq_self
      (μ := (volume : Measure (Cfg S))) (fun θ => A θ * Real.exp (-β * H (θ - w))) w
    simpa using this
  have key2 : ∫ θ, A (θ - w) * Real.exp (-β * H θ)
      = ∫ θ, A θ * Real.exp (-β * H (θ + w)) := by
    have := integral_add_right_eq_self
      (μ := (volume : Measure (Cfg S))) (fun θ => A θ * Real.exp (-β * H (θ + w))) (-w)
    simpa [sub_eq_add_neg] using this
  -- the pointwise bound
  have hpt : ∀ θ : Cfg S,
      2 * Real.exp (-(β * K) / 2) * (A θ * Real.exp (-β * H θ))
        ≤ A θ * Real.exp (-β * H (θ - w)) + A θ * Real.exp (-β * H (θ + w)) := by
    intro θ
    have hmid := two_exp_mid_le (-β * H (θ - w)) (-β * H (θ + w))
    have hle : -(β * K) / 2 + -β * H θ ≤ (-β * H (θ - w) + -β * H (θ + w)) / 2 := by
      have := hK θ
      nlinarith [hK θ, hβ]
    have hexp : Real.exp (-(β * K) / 2) * Real.exp (-β * H θ)
        ≤ Real.exp ((-β * H (θ - w) + -β * H (θ + w)) / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hle
    have h2 : 2 * (Real.exp (-(β * K) / 2) * Real.exp (-β * H θ))
        ≤ Real.exp (-β * H (θ - w)) + Real.exp (-β * H (θ + w)) := by
      linarith [hmid, hexp]
    have := mul_le_mul_of_nonneg_left h2 (hA0 θ)
    nlinarith [this, hA0 θ]
  -- integrate
  have hint : 2 * Real.exp (-(β * K) / 2) * (∫ θ, A θ * Real.exp (-β * H θ))
      ≤ (∫ θ, A θ * Real.exp (-β * H (θ - w))) + ∫ θ, A θ * Real.exp (-β * H (θ + w)) := by
    have hi1 : Integrable (fun θ : Cfg S => A θ * Real.exp (-β * H (θ - w)))
        (volume : Measure (Cfg S)) :=
      integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul
        (hH.comp (continuous_id.sub continuous_const)))))
    have hi2 : Integrable (fun θ : Cfg S => A θ * Real.exp (-β * H (θ + w)))
        (volume : Measure (Cfg S)) :=
      integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul
        (hH.comp (continuous_id.add continuous_const)))))
    have hmono := integral_mono ((integrable_obs hH hA β).const_mul _) (hi1.add hi2) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_const_mul, integral_add hi1 hi2] at hmono
    exact hmono
  unfold gibbsAvg
  rw [key1, key2, ← add_div]
  calc 2 * Real.exp (-(β * K) / 2) * ((∫ θ, A θ * Real.exp (-β * H θ)) / gibbsZ H β)
      = (2 * Real.exp (-(β * K) / 2) * ∫ θ, A θ * Real.exp (-β * H θ)) / gibbsZ H β := by ring
    _ ≤ ((∫ θ, A θ * Real.exp (-β * H (θ - w))) + ∫ θ, A θ * Real.exp (-β * H (θ + w)))
          / gibbsZ H β := by gcongr

/-- The Gibbs average of an observable bounded by `1` is bounded by `1`: `gibbsAvg` really is
an average with respect to a probability measure. -/
lemma abs_gibbsAvg_le_one {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A) (β : ℝ)
    (hbound : ∀ θ, |A θ| ≤ 1) : |gibbsAvg H β A| ≤ 1 := by
  have hZ := gibbsZ_pos hH β
  have hfc : Continuous fun θ : Cfg S => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hH)
  have h1 : |∫ θ, A θ * Real.exp (-β * H θ)| ≤ ∫ θ, |A θ * Real.exp (-β * H θ)| :=
    abs_integral_le_integral_abs
  have h2 : ∫ θ, |A θ * Real.exp (-β * H θ)| ≤ gibbsZ H β := by
    refine integral_mono ((integrable_obs hH hA β).abs) (integrable_of_continuous hfc) ?_
    intro θ
    simp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hbound θ)
  unfold gibbsAvg
  rw [abs_div, abs_of_pos hZ, div_le_one hZ]
  linarith


end Gibbs

end

end Phys

/-
The harmonic spin-wave profile: it equals `1` at the centre, vanishes outside a ball of
radius `R`, and has Dirichlet energy `O(1 / log R)` in dimension `d ≤ 2`.
-/
import RequestProject.Lattice

open MeasureTheory Real Filter

namespace Phys

noncomputable section

/-- The harmonic sum `∑_{s=1}^{R} 1/s`. -/
def harm (R : ℕ) : ℝ := ∑ s ∈ Finset.range R, 1 / (s + 1 : ℝ)

lemma harm_nonneg (R : ℕ) : 0 ≤ harm R :=
  Finset.sum_nonneg fun s _ => by positivity

lemma harm_succ (m : ℕ) : harm (m + 1) = harm m + 1 / (m + 1 : ℝ) :=
  Finset.sum_range_succ _ _

lemma harm_mono : Monotone harm := by
  intro a b hab
  unfold harm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) ?_
  intro i _ _
  positivity

lemma one_le_harm {R : ℕ} (hR : 1 ≤ R) : 1 ≤ harm R := by
  have h1 : harm 1 = 1 := by norm_num [harm]
  calc (1 : ℝ) = harm 1 := h1.symm
    _ ≤ harm R := harm_mono hR

lemma harm_pos {R : ℕ} (hR : 1 ≤ R) : 0 < harm R := lt_of_lt_of_le zero_lt_one (one_le_harm hR)

lemma harm_tendsto : Tendsto harm atTop atTop := by
  have := Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact this

/-- The spin-wave profile: `1` at the centre, decaying harmonically to `0` at radius `R`. -/
def prof (R m : ℕ) : ℝ := max 0 (1 - harm m / harm R)

lemma prof_nonneg (R m : ℕ) : 0 ≤ prof R m := le_max_left _ _

lemma prof_le_one (R m : ℕ) : prof R m ≤ 1 := by
  unfold prof
  refine max_le zero_le_one ?_
  have : 0 ≤ harm m / harm R := div_nonneg (harm_nonneg m) (harm_nonneg R)
  linarith

@[simp] lemma prof_zero (R : ℕ) : prof R 0 = 1 := by
  unfold prof harm
  simp

lemma prof_eq_zero_of_le {R m : ℕ} (hR : 1 ≤ R) (h : R ≤ m) : prof R m = 0 := by
  unfold prof
  have h1 : harm R ≤ harm m := harm_mono h
  have h2 : 1 ≤ harm m / harm R := (one_le_div (harm_pos hR)).mpr h1
  exact max_eq_left (by linarith)

lemma max_sub_max_le {u v : ℝ} (h : v ≤ u) : max 0 u - max 0 v ≤ u - v := by
  rcases le_or_gt u 0 with hu | hu
  · have hv : v ≤ 0 := le_trans h hu
    rw [max_eq_left hu, max_eq_left hv]
    linarith
  · rcases le_or_gt v 0 with hv | hv
    · rw [max_eq_left hv, max_eq_right hu.le]
      linarith
    · rw [max_eq_right hv.le, max_eq_right hu.le]

lemma prof_antitone {R : ℕ} : Antitone (prof R) := by
  intro a b hab
  unfold prof
  refine max_le_max le_rfl ?_
  have : harm a ≤ harm b := harm_mono hab
  have hR := harm_nonneg R
  rcases eq_or_lt_of_le hR with h | h
  · simp [← h]
  · apply sub_le_sub_left
    gcongr

/-- One-step decay of the profile. -/
lemma prof_step {R : ℕ} (hR : 1 ≤ R) (m : ℕ) :
    prof R m - prof R (m + 1) ≤ 1 / ((m + 1 : ℝ) * harm R) := by
  have hH := harm_pos hR
  have hkey : (1 - harm (m + 1) / harm R) ≤ (1 - harm m / harm R) := by
    have hmm : harm m ≤ harm (m + 1) := harm_mono (Nat.le_succ m)
    have h2 : harm m / harm R ≤ harm (m + 1) / harm R := by gcongr
    linarith
  have := max_sub_max_le hkey
  have hdiff : (1 - harm m / harm R) - (1 - harm (m + 1) / harm R)
      = 1 / ((m + 1 : ℝ) * harm R) := by
    rw [harm_succ]
    field_simp
    ring
  unfold prof
  linarith [hdiff ▸ this]

/-- The profile is `1`-Lipschitz at scale `1 / (m · harm R)`. -/
lemma prof_diff_le {R : ℕ} (hR : 1 ≤ R) {a b : ℕ} (hab : b ≤ a + 1) (hba : a ≤ b + 1) :
    |prof R a - prof R b| ≤ 1 / (((max a 1 : ℕ) : ℝ) * harm R) := by
  have hH := harm_pos hR
  rcases Nat.lt_trichotomy a b with h | h | h
  · -- b = a + 1
    have hb : b = a + 1 := by omega
    subst hb
    have h1 : 0 ≤ prof R a - prof R (a + 1) :=
      sub_nonneg.mpr (prof_antitone (Nat.le_succ a))
    rw [abs_of_nonneg h1]
    refine le_trans (prof_step hR a) ?_
    have hmax : ((max a 1 : ℕ) : ℝ) ≤ (a + 1 : ℝ) := by
      have : (max a 1 : ℕ) ≤ a + 1 := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((max a 1 : ℕ) : ℝ) := by
      have : 1 ≤ (max a 1 : ℕ) := by omega
      have : (1 : ℝ) ≤ ((max a 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_right hmax hH.le
  · subst h
    simp
    positivity
  · -- a = b + 1
    have ha : a = b + 1 := by omega
    subst ha
    have h1 : 0 ≤ prof R b - prof R (b + 1) :=
      sub_nonneg.mpr (prof_antitone (Nat.le_succ b))
    rw [abs_of_nonpos (by linarith), neg_sub]
    refine le_trans (prof_step hR b) ?_
    have hmax : ((max (b + 1) 1 : ℕ) : ℝ) = (b + 1 : ℝ) := by
      have : (max (b + 1) 1 : ℕ) = b + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [hmax]

end

end Phys

/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a Lean module docstring just below the imports, since
Lean 4 does not permit a docstring comment to precede the import commands.)
-/
import RequestProject.Profile

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open MeasureTheory Real Filter

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Phys

noncomputable section

/-! ### The classical XY model in a box of `ℤ^d` -/

/-- The nearest–neighbour bonds of the box: a bond is a pair `(x, i)` where the bond joins
`x` to `x + e_i`, and it is present when `x + e_i` still lies in the box. -/
def bondSet (d L : ℕ) : Finset (Site d L × Fin d) :=
  Finset.univ.filter fun p => (p.1 p.2 : ℕ) + 1 ≤ 2 * L

/-- The first endpoint of a bond. -/
def bsrc {d L : ℕ} (p : Site d L × Fin d) : Site d L := p.1

/-- The second endpoint of a bond. -/
def btgt {d L : ℕ} (p : Site d L × Fin d) : Site d L :=
  Function.update p.1 p.2 (p.1 p.2 + 1)

/-- The spin-wave profile on the box: it rotates the central spin by `π` and vanishes at
distance `R` from the centre. -/
def swProfile (d L R : ℕ) : Site d L → ℝ := fun x => Real.pi * prof R (rad x)

/-- The magnetization at the centre of the box `{0,…,2L}^d` for the classical XY model
with inverse temperature `β`, coupling `J` and external field `h`. -/
def latticeMag (d L : ℕ) (β J h : ℝ) : ℝ :=
  magnetization (bondSet d L) bsrc btgt β J h (center d L)

lemma swProfile_center (d L R : ℕ) : swProfile d L R (center d L) = Real.pi := by
  unfold swProfile
  rw [rad_center, prof_zero, mul_one]

/-! ### Geometry of a bond -/

lemma dist1_btgt {d L : ℕ} {p : Site d L × Fin d} (hp : p ∈ bondSet d L) (j : Fin d) :
    dist1 L (btgt p j) ≤ dist1 L (p.1 j) + 1 ∧ dist1 L (p.1 j) ≤ dist1 L (btgt p j) + 1 := by
  simp only [bondSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  by_cases hj : j = p.2
  · have hlt : p.1 p.2 < Fin.last (2 * L) := by
      rw [Fin.lt_def]
      simpa using hp
    have hval : ((p.1 p.2 + 1 : Fin (2 * L + 1)) : ℕ) = (p.1 p.2 : ℕ) + 1 :=
      Fin.val_add_one_of_lt hlt
    have hbt : btgt p j = p.1 p.2 + 1 := by
      unfold btgt
      rw [hj, Function.update_self]
    rw [hbt, hj]
    unfold dist1
    rw [hval]
    omega
  · have hbt : btgt p j = p.1 j := by
      unfold btgt
      rw [Function.update_of_ne hj]
    rw [hbt]
    omega

lemma rad_btgt_close {d L : ℕ} {p : Site d L × Fin d} (hp : p ∈ bondSet d L) :
    rad (btgt p) ≤ rad p.1 + 1 ∧ rad p.1 ≤ rad (btgt p) + 1 := by
  constructor
  · exact rad_le_succ fun j => (dist1_btgt hp j).1
  · exact rad_le_succ fun j => (dist1_btgt hp j).2

/-! ### The two energy estimates -/

/-- The bound on the contribution of one bond to the Dirichlet energy. -/
def bnd (R m : ℕ) : ℝ := if m ≤ R then (2 / (((m : ℝ) + 1) * harm R)) ^ 2 else 0

lemma bnd_nonneg (R m : ℕ) : 0 ≤ bnd R m := by
  unfold bnd
  split
  · positivity
  · exact le_rfl

lemma sum_bnd_le {R : ℕ} (hR : 1 ≤ R) :
    ∑ m ∈ Finset.range (R + 1), (12 * m + 1 : ℝ) * bnd R m ≤ 96 / harm R := by
  have hH := harm_pos hR
  have hH1 := one_le_harm hR
  have hstep : ∀ m ∈ Finset.range (R + 1),
      (12 * m + 1 : ℝ) * bnd R m ≤ 48 / (((m : ℝ) + 1) * harm R ^ 2) := by
    intro m hm
    simp only [Finset.mem_range] at hm
    unfold bnd
    rw [if_pos (by omega : m ≤ R)]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsq : (2 / (((m : ℝ) + 1) * harm R)) ^ 2 = 4 / (((m : ℝ) + 1) ^ 2 * harm R ^ 2) := by
      rw [div_pow]
      norm_num [mul_pow]
    rw [hsq, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (12 * (m : ℝ) + 1) * 4 ≤ 48 * ((m : ℝ) + 1) := by linarith
    have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) * harm R ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hEq : ∑ m ∈ Finset.range (R + 1), 48 / (((m : ℝ) + 1) * harm R ^ 2)
      = (48 / harm R ^ 2) * harm (R + 1) := by
    unfold harm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hEq]
  have hharm : harm (R + 1) ≤ 2 * harm R := by
    rw [harm_succ]
    have : 1 / ((R : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith
    linarith
  have hpos : (0 : ℝ) < 48 / harm R ^ 2 := by positivity
  calc (48 / harm R ^ 2) * harm (R + 1) ≤ (48 / harm R ^ 2) * (2 * harm R) :=
        mul_le_mul_of_nonneg_left hharm hpos.le
    _ = 96 / harm R := by field_simp; ring

/-- **Dirichlet energy of the spin-wave profile.**  In dimension `d ≤ 2` it is
`O(1 / harm R)`, hence tends to `0` as `R → ∞`: this is exactly where `d ≤ 2` enters. -/
theorem dirichlet_bound {d L R : ℕ} (hd : d ≤ 2) (hR : 1 ≤ R) :
    dirichlet (bondSet d L) bsrc btgt (swProfile d L R) ≤ Real.pi ^ 2 * 192 / harm R := by
  have hH := harm_pos hR
  have hstep : ∀ p ∈ bondSet d L,
      (swProfile d L R (bsrc p) - swProfile d L R (btgt p)) ^ 2
        ≤ Real.pi ^ 2 * bnd R (rad p.1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := rad_btgt_close hp
    unfold swProfile bsrc
    rw [← mul_sub, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    by_cases hcase : rad p.1 ≤ R
    · unfold bnd
      rw [if_pos hcase]
      have habs := prof_diff_le (R := R) hR (a := rad p.1) (b := rad (btgt p)) h1 h2
      have hmax : (((rad p.1 : ℝ) + 1) * harm R) / 2 ≤ ((max (rad p.1) 1 : ℕ) : ℝ) * harm R := by
        have hm : ((rad p.1 : ℝ) + 1) / 2 ≤ ((max (rad p.1) 1 : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (rad p.1) with h0 | h0
          · rw [h0]
            norm_num
          · have : (max (rad p.1) 1 : ℕ) = rad p.1 := by omega
            rw [this]
            have : (1 : ℝ) ≤ (rad p.1 : ℝ) := by exact_mod_cast h0
            linarith
        calc (((rad p.1 : ℝ) + 1) * harm R) / 2 = (((rad p.1 : ℝ) + 1) / 2) * harm R := by ring
          _ ≤ ((max (rad p.1) 1 : ℕ) : ℝ) * harm R := mul_le_mul_of_nonneg_right hm hH.le
      have hpos : (0 : ℝ) < (((rad p.1 : ℝ) + 1) * harm R) / 2 := by positivity
      have hle2 : 1 / (((max (rad p.1) 1 : ℕ) : ℝ) * harm R)
          ≤ 2 / (((rad p.1 : ℝ) + 1) * harm R) := by
        rw [div_le_div_iff₀ (by linarith [hpos, hmax]) (by positivity)]
        linarith [hmax]
      calc (prof R (rad p.1) - prof R (rad (btgt p))) ^ 2
          = |prof R (rad p.1) - prof R (rad (btgt p))| ^ 2 := (sq_abs _).symm
        _ ≤ (2 / (((rad p.1 : ℝ) + 1) * harm R)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (le_trans habs hle2) 2
    · push_neg at hcase
      have hz1 : prof R (rad p.1) = 0 := prof_eq_zero_of_le hR (le_of_lt hcase)
      have hz2 : prof R (rad (btgt p)) = 0 := prof_eq_zero_of_le hR (by omega)
      rw [hz1, hz2]
      simpa using bnd_nonneg R (rad p.1)
  have hsum1 : dirichlet (bondSet d L) bsrc btgt (swProfile d L R)
      ≤ ∑ p ∈ bondSet d L, Real.pi ^ 2 * bnd R (rad p.1) :=
    Finset.sum_le_sum hstep
  have hsum2 : ∑ p ∈ bondSet d L, Real.pi ^ 2 * bnd R (rad p.1)
      ≤ ∑ p : Site d L × Fin d, Real.pi ^ 2 * bnd R (rad p.1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro p _ _
    have := bnd_nonneg R (rad p.1)
    positivity
  have hsum3 : ∑ p : Site d L × Fin d, Real.pi ^ 2 * bnd R (rad p.1)
      = (d : ℝ) * (Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x)) := by
    rw [Fintype.sum_prod_type]
    have hin : ∀ x : Site d L, ∑ _y : Fin d, Real.pi ^ 2 * bnd R (rad x)
        = (d : ℝ) * (Real.pi ^ 2 * bnd R (rad x)) := by
      intro x
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [Finset.sum_congr rfl fun x _ => hin x, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum4 : ∑ x : Site d L, bnd R (rad x)
      ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * bnd R m :=
    sum_shell_le hd (bnd R) (bnd_nonneg R)
  have hsum5 : ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * bnd R m ≤ 96 / harm R := by
    have hTsub : Finset.range (L + 1) ∩ Finset.range (R + 1) ⊆ Finset.range (L + 1) :=
      Finset.inter_subset_left
    have hvanish : ∀ m ∈ Finset.range (L + 1), m ∉ Finset.range (L + 1) ∩ Finset.range (R + 1) →
        (12 * m + 1 : ℝ) * bnd R m = 0 := by
      intro m hm hmT
      have hmR : ¬ m < R + 1 := fun hlt =>
        hmT (Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hlt⟩)
      unfold bnd
      rw [if_neg (by omega)]
      ring
    rw [← Finset.sum_subset hTsub hvanish]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_)
      (sum_bnd_le hR)
    intro m _ _
    have := bnd_nonneg R m
    positivity
  have hd' : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have hbnn : 0 ≤ ∑ x : Site d L, bnd R (rad x) :=
    Finset.sum_nonneg fun x _ => bnd_nonneg R (rad x)
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
  have hfin : ∑ x : Site d L, bnd R (rad x) ≤ 96 / harm R := hsum4.trans hsum5
  calc dirichlet (bondSet d L) bsrc btgt (swProfile d L R)
      ≤ (d : ℝ) * (Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x)) := by
        rw [← hsum3]; exact hsum1.trans hsum2
    _ ≤ 2 * (Real.pi ^ 2 * (96 / harm R)) := by
        have h1 : Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x) ≤ Real.pi ^ 2 * (96 / harm R) :=
          mul_le_mul_of_nonneg_left hfin hpi
        have h2 : (0 : ℝ) ≤ Real.pi ^ 2 * (96 / harm R) := by positivity
        nlinarith [mul_nonneg hpi hbnn]
    _ = Real.pi ^ 2 * 192 / harm R := by ring

/-- The `ℓ²` norm of the spin-wave profile is controlled by the volume of the ball of
radius `R`. -/
theorem sqNorm_bound {d L R : ℕ} (hd : d ≤ 2) (hR : 1 ≤ R) :
    sqNorm (swProfile d L R) ≤ Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hstep : sqNorm (swProfile d L R)
      = Real.pi ^ 2 * ∑ x : Site d L, (prof R (rad x)) ^ 2 := by
    unfold sqNorm swProfile
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hshell : ∑ x : Site d L, (prof R (rad x)) ^ 2
      ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * (prof R m) ^ 2 :=
    sum_shell_le hd (fun m => (prof R m) ^ 2) (fun _ => sq_nonneg _)
  have hcut : ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * (prof R m) ^ 2
      ≤ 13 * ((R : ℝ) + 1) ^ 2 := by
    have hTsub : Finset.range (L + 1) ∩ Finset.range (R + 1) ⊆ Finset.range (L + 1) :=
      Finset.inter_subset_left
    have hvanish : ∀ m ∈ Finset.range (L + 1), m ∉ Finset.range (L + 1) ∩ Finset.range (R + 1) →
        (12 * m + 1 : ℝ) * (prof R m) ^ 2 = 0 := by
      intro m hm hmT
      have hmR : ¬ m < R + 1 := fun hlt =>
        hmT (Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hlt⟩)
      have : prof R m = 0 := prof_eq_zero_of_le hR (by omega)
      rw [this]
      ring
    rw [← Finset.sum_subset hTsub hvanish]
    have hterm : ∀ m ∈ Finset.range (L + 1) ∩ Finset.range (R + 1),
        (12 * m + 1 : ℝ) * (prof R m) ^ 2 ≤ 12 * (R : ℝ) + 1 := by
      intro m hm
      have hmR : m ≤ R := by
        have := (Finset.mem_inter.mp hm).2
        simp only [Finset.mem_range] at this
        omega
      have hmR' : (m : ℝ) ≤ (R : ℝ) := by exact_mod_cast hmR
      have h0 := prof_nonneg R m
      have h1 := prof_le_one R m
      have hp2 : prof R m ^ 2 ≤ 1 := by nlinarith
      have hcoef : (0 : ℝ) ≤ 12 * (m : ℝ) + 1 := by positivity
      calc (12 * (m : ℝ) + 1) * prof R m ^ 2 ≤ (12 * (m : ℝ) + 1) * 1 :=
            mul_le_mul_of_nonneg_left hp2 hcoef
        _ ≤ 12 * (R : ℝ) + 1 := by linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range (L + 1) ∩ Finset.range (R + 1)).card : ℝ) ≤ (R : ℝ) + 1 := by
      have : (Finset.range (L + 1) ∩ Finset.range (R + 1)).card ≤ R + 1 := by
        calc (Finset.range (L + 1) ∩ Finset.range (R + 1)).card
            ≤ (Finset.range (R + 1)).card := Finset.card_le_card Finset.inter_subset_right
          _ = R + 1 := Finset.card_range _
      exact_mod_cast this
    nlinarith [hcard]
  rw [hstep]
  nlinarith [hshell.trans hcut, hpi]

/-- Sanity check: the magnetization is an average of `cos`, hence lies in `[-1, 1]`. -/
lemma abs_latticeMag_le_one (d L : ℕ) (β J h : ℝ) : |latticeMag d L β J h| ≤ 1 :=
  abs_gibbsAvg_le_one (continuous_xyEnergy _ _ _ _ _)
    (continuous_cosC.comp (continuous_apply _)) β (fun _ => abs_cosC_le_one _)

/-! ### The Mermin–Wagner theorem -/

/-- **Mermin–Wagner theorem.**  There is no spontaneous breaking of the continuous `O(2)`
symmetry in dimension `d ≤ 2` at any positive temperature.  For the classical XY model in
the box `{0,…,2L}^d` with nonnegative coupling `J`, at inverse temperature `β` (that is, at
any temperature `T = 1/β > 0`), the magnetization at the centre of the box in the presence of
a symmetry breaking field `h ≥ 0` is smaller than any prescribed `ε > 0` as soon as the field
is small enough — and this uniformly in the volume.  In particular the spontaneous
magnetization `lim_{h ↓ 0} lim_{L → ∞} m(β, J, h, L)` vanishes. -/
theorem mermin_wagner (d : ℕ) (hd : d ≤ 2) (β J : ℝ) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 ≤ h → h < δ → ∀ L : ℕ, |latticeMag d L β J h| ≤ ε := by
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  -- choose the scale `R` so that the Dirichlet energy term is small
  obtain ⟨R₀, hR₀⟩ := (harm_tendsto.eventually_ge_atTop
    (192 * β * J * Real.pi ^ 2 / ε + 1)).exists
  set R : ℕ := max R₀ 1 with hRdef
  have hR : 1 ≤ R := le_max_right _ _
  have hharm : 192 * β * J * Real.pi ^ 2 / ε + 1 ≤ harm R :=
    le_trans hR₀ (harm_mono (le_max_left _ _))
  have hH : (0 : ℝ) < harm R := harm_pos hR
  -- the Dirichlet (spin-wave) term is small, uniformly in the volume
  have hdir : ∀ L : ℕ, β * (J * dirichlet (bondSet d L) bsrc btgt (swProfile d L R)) / 2
      ≤ ε / 2 := by
    intro L
    have h1 := dirichlet_bound (d := d) (L := L) (R := R) hd hR
    have hnn : 0 ≤ β * J := mul_nonneg hβ hJ
    have hkey : β * J * (Real.pi ^ 2 * 192 / harm R) ≤ ε := by
      have hharm' : 192 * β * J * Real.pi ^ 2 / ε ≤ harm R := by linarith
      rw [div_le_iff₀ hε] at hharm'
      rw [mul_div_assoc', div_le_iff₀ hH]
      nlinarith [hharm']
    have hdirnn : 0 ≤ dirichlet (bondSet d L) bsrc btgt (swProfile d L R) :=
      dirichlet_nonneg _ _ _ _
    nlinarith [mul_le_mul_of_nonneg_left h1 hnn, hkey]
  -- choose the field threshold
  refine ⟨ε / (β * (Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2) + 1), by positivity, ?_⟩
  intro h hh0 hhδ L
  have hsq := sqNorm_bound (d := d) (L := L) (R := R) hd hR
  have hsqnn : 0 ≤ sqNorm (swProfile d L R) := sqNorm_nonneg _
  -- the field term is small once `h` is small
  have hfield : β * (h * sqNorm (swProfile d L R)) / 2 ≤ ε / 2 := by
    have hC : (0 : ℝ) < β * (Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2) + 1 := by positivity
    have h1 : h * (β * (Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2)) ≤ ε := by
      have h2 : h * (β * (Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2) + 1) ≤ ε := by
        rw [← le_div_iff₀ hC]
        exact hhδ.le
      nlinarith [hh0]
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hβ hh0), h1]
  -- the finite-volume Mermin-Wagner bound
  have hmain := magnetization_bound (bondSet d L) bsrc btgt β J h hβ hJ hh0 (center d L)
    (swProfile d L R) (swProfile_center d L R)
  have hfinal : β * (J * dirichlet (bondSet d L) bsrc btgt (swProfile d L R)
      + h * sqNorm (swProfile d L R)) / 2 ≤ ε := by
    have hd1 := hdir L
    nlinarith [hfield]
  exact le_trans hmain hfinal

/-- **No spontaneous magnetization.**  In dimension `d ≤ 2`, at any positive temperature, the
magnetization of the classical XY model tends to `0` along any sequence of vanishing external
fields, no matter how the volumes are chosen: the spontaneous magnetization vanishes. -/
theorem mermin_wagner_tendsto (d : ℕ) (hd : d ≤ 2) (β J : ℝ) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (hs : ℕ → ℝ) (Ls : ℕ → ℕ) (hpos : ∀ n, 0 ≤ hs n) (hh : Tendsto hs atTop (nhds 0)) :
    Tendsto (fun n => latticeMag d (Ls n) β J (hs n)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := mermin_wagner d hd β J hβ hJ (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hlt : hs n < δ := by
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero] at hdist
    exact lt_of_le_of_lt (le_abs_self _) hdist
  have hbound := hmain (hs n) (hpos n) hlt (Ls n)
  rw [Real.dist_eq, sub_zero]
  have : |latticeMag d (Ls n) β J (hs n)| ≤ ε / 2 := hbound
  linarith

end

end Phys

/-
The square lattice box in dimension `d`, its `ℓ^∞` shells, and the harmonic
spin-wave profile with small Dirichlet energy when `d ≤ 2`.
-/
import RequestProject.XY

open MeasureTheory Real

namespace Phys

noncomputable section

/-- The sites of the box `{0,…,2L}^d` in `ℤ^d`. -/
abbrev Site (d L : ℕ) := Fin d → Fin (2 * L + 1)

/-- Distance of a coordinate to the centre `L` of the box. -/
def dist1 (L : ℕ) (a : Fin (2 * L + 1)) : ℕ := max ((a : ℕ) - L) (L - (a : ℕ))

/-- The `ℓ^∞` distance of a site to the centre of the box. -/
def rad {d L : ℕ} (x : Site d L) : ℕ := Finset.univ.sup fun i => dist1 L (x i)

/-- The centre of the box. -/
def center (d L : ℕ) : Site d L := fun _ => ⟨L, by omega⟩

lemma dist1_le (L : ℕ) (a : Fin (2 * L + 1)) : dist1 L a ≤ L := by
  have := a.isLt
  unfold dist1
  omega

lemma rad_le {d L : ℕ} (x : Site d L) : rad x ≤ L :=
  Finset.sup_le fun i _ => dist1_le L (x i)

@[simp] lemma rad_center (d L : ℕ) : rad (center d L) = 0 := by
  unfold rad center dist1
  simp

lemma rad_le_succ {d L : ℕ} {x y : Site d L} (h : ∀ j, dist1 L (y j) ≤ dist1 L (x j) + 1) :
    rad y ≤ rad x + 1 :=
  Finset.sup_le fun j _ => le_trans (h j) (by
    exact Nat.add_le_add_right (Finset.le_sup (f := fun i => dist1 L (x i)) (Finset.mem_univ j)) 1)

section Shells

variable (d L : ℕ)

/-- Coordinates at distance at most `m` from the centre. -/
def Tball (L m : ℕ) : Finset (Fin (2 * L + 1)) := Finset.univ.filter fun a => dist1 L a ≤ m

/-- Coordinates at distance exactly `m` from the centre. -/
def Ecrit (L m : ℕ) : Finset (Fin (2 * L + 1)) := Finset.univ.filter fun a => dist1 L a = m

lemma card_Tball (L m : ℕ) : (Tball L m).card ≤ 2 * m + 1 := by
  classical
  have : ∀ a ∈ Tball L m, (a : ℕ) + m - L ∈ Finset.range (2 * m + 1) := by
    intro a ha
    simp only [Tball, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]
    unfold dist1 at ha
    omega
  have hinj : ∀ a ∈ Tball L m, ∀ b ∈ Tball L m, (a : ℕ) + m - L = (b : ℕ) + m - L → a = b := by
    intro a ha b hb hab
    simp only [Tball, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    unfold dist1 at ha hb
    have : (a : ℕ) = (b : ℕ) := by omega
    exact Fin.ext this
  calc (Tball L m).card ≤ (Finset.range (2 * m + 1)).card :=
        Finset.card_le_card_of_injOn _ this hinj
    _ = 2 * m + 1 := Finset.card_range _

lemma card_Ecrit (L m : ℕ) : (Ecrit L m).card ≤ 2 := by
  classical
  have hmaps : ∀ a ∈ Ecrit L m, (if (a : ℕ) ≤ L then 0 else 1) ∈ Finset.range 2 := by
    intro a _
    simp only [Finset.mem_range]
    split <;> omega
  have hinj : ∀ a ∈ Ecrit L m, ∀ b ∈ Ecrit L m,
      (if (a : ℕ) ≤ L then 0 else 1) = (if (b : ℕ) ≤ L then 0 else 1) → a = b := by
    intro a ha b hb hab
    simp only [Ecrit, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    unfold dist1 at ha hb
    refine Fin.ext ?_
    by_cases h1 : (a : ℕ) ≤ L <;> by_cases h2 : (b : ℕ) ≤ L <;>
      simp [h1, h2] at hab ⊢ <;> omega
  calc (Ecrit L m).card ≤ (Finset.range 2).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 := Finset.card_range _

/-- The number of sites of the box at `ℓ^∞` distance exactly `m ≥ 1` from the centre is at
most `12 m + 1`, in any dimension `d ≤ 2`. -/
lemma card_shell_le {d L : ℕ} (hd : d ≤ 2) (m : ℕ) :
    (Finset.univ.filter fun x : Site d L => rad x = m).card ≤ 12 * m + 1 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- only the centre has radius `0`
    have hsub : (Finset.univ.filter fun x : Site d L => rad x = 0) ⊆ {center d L} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_singleton]
      funext i
      have : dist1 L (x i) ≤ 0 := by
        rw [← hx]
        exact Finset.le_sup (f := fun j => dist1 L (x j)) (Finset.mem_univ i)
      have h0 : dist1 L (x i) = 0 := Nat.le_zero.mp this
      unfold dist1 at h0
      have := (x i).isLt
      exact Fin.ext (by unfold center; simp; omega)
    calc (Finset.univ.filter fun x : Site d L => rad x = 0).card ≤ ({center d L} : Finset _).card :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ ≤ 12 * 0 + 1 := by omega
  · -- some coordinate realises the maximum
    have hsub : (Finset.univ.filter fun x : Site d L => rad x = m) ⊆
        Finset.univ.biUnion fun i : Fin d =>
          Fintype.piFinset (Function.update (fun _ => Tball L m) i (Ecrit L m)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · exfalso
          have : rad x = 0 := by
            unfold rad
            simp
          omega
        · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd0)
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun j => dist1 L (x j)
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
      refine Fintype.mem_piFinset.mpr fun j => ?_
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Ecrit, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hi]
        exact hx
      · simp only [Function.update_of_ne hji, Tball, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hx]
        exact Finset.le_sup (f := fun k => dist1 L (x k)) (Finset.mem_univ j)
    have hcard_each : ∀ i : Fin d,
        (Fintype.piFinset (Function.update (fun _ => Tball L m) i (Ecrit L m))).card
          ≤ 2 * (2 * m + 1) ^ (d - 1) := by
      intro i
      rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        Function.update_self]
      have hrest : ∏ j ∈ Finset.univ.erase i,
          (Function.update (fun _ => Tball L m) i (Ecrit L m) j).card
          = ∏ _j ∈ Finset.univ.erase i, (Tball L m).card :=
        Finset.prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest, Finset.prod_const]
      have hcard : (Finset.univ.erase i : Finset (Fin d)).card = d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
      rw [hcard]
      exact Nat.mul_le_mul (card_Ecrit L m) (Nat.pow_le_pow_left (card_Tball L m) _)
    calc (Finset.univ.filter fun x : Site d L => rad x = m).card
        ≤ ∑ _i : Fin d, 2 * (2 * m + 1) ^ (d - 1) :=
          le_trans (Finset.card_le_card hsub)
            (le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun i _ => hcard_each i))
      _ = d * (2 * (2 * m + 1) ^ (d - 1)) := by rw [Finset.sum_const]; simp [mul_comm]
      _ ≤ 12 * m + 1 := by
          have hpow : (2 * m + 1) ^ (d - 1) ≤ 2 * m + 1 := by
            have h : (2 * m + 1) ^ (d - 1) ≤ (2 * m + 1) ^ 1 :=
              Nat.pow_le_pow_right (by omega) (by omega)
            simpa using h
          have h2 : d * (2 * (2 * m + 1) ^ (d - 1)) ≤ 2 * (2 * (2 * m + 1)) :=
            Nat.mul_le_mul hd (by omega)
          have h3 : 2 * (2 * (2 * m + 1)) ≤ 12 * m + 1 := by omega
          exact le_trans h2 h3

/-- Shell decomposition of a sum over the box. -/
lemma sum_shell_le {d L : ℕ} (hd : d ≤ 2) (psi : ℕ → ℝ) (hpsi : ∀ m, 0 ≤ psi m) :
    ∑ x : Site d L, psi (rad x) ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * psi m := by
  classical
  have hmaps : ∀ x : Site d L, x ∈ (Finset.univ : Finset (Site d L)) →
      rad x ∈ Finset.range (L + 1) := by
    intro x _
    simp only [Finset.mem_range]
    have := rad_le x
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcong : ∀ x ∈ Finset.univ.filter (fun x : Site d L => rad x = m), psi (rad x) = psi m := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hpsi m)
  exact_mod_cast Nat.cast_le.mpr (card_shell_le (L := L) hd m)

end Shells

end

end Phys

