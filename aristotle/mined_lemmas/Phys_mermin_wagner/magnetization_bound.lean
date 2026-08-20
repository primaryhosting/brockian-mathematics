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
