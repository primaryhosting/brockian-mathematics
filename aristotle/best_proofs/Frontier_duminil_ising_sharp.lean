/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

/--
Abstract data describing the finite-volume connectivity/correlation functions of the
Ising model together with the Duminil-Copin–Tassion differential inequality.

Here `theta n β` should be thought of as the finite-volume order parameter
`θ_n(β) = ⟨σ_0 ; σ_{∂Λ_n}⟩_β` (equivalently, in the random-current / FK representation, the
probability that the origin is connected to the boundary of the box of radius `n`) at inverse
temperature `β`.

The fields record the standard structural properties of this family:

* `theta` takes values in `[0,1]` and is nondecreasing in the inverse temperature `β`
  (Griffiths / FKG monotonicity);
* the key input, `diff_ineq`, is the Duminil-Copin–Tassion differential inequality obtained
  from the OSSS inequality (Duminil-Copin–Raoufi–Tassion),
  `θ_n'(β) ≥ (n / ∑_{k<n} θ_k(β)) · θ_n(β)(1 - θ_n(β))`,
  written here in the equivalent product form which avoids division;
* `summable_zero` records that at infinite temperature (`β = 0`) correlations are summable;
* `exists_not_summable` records that at sufficiently low temperature they are not
  (existence of a low-temperature ordered regime).
-/
structure IsingSharpnessData where
  /-- Finite-volume order parameter `θ_n(β)`. -/
  theta : ℕ → ℝ → ℝ
  /-- Each `θ_n` is a differentiable function of the inverse temperature. -/
  differentiable : ∀ n, Differentiable ℝ (theta n)
  /-- `θ_n(β) ≥ 0`. -/
  nonneg : ∀ n β, 0 ≤ theta n β
  /-- `θ_n(β) ≤ 1`. -/
  le_one : ∀ n β, theta n β ≤ 1
  /-- `θ_n` is nondecreasing in `β`. -/
  mono_beta : ∀ n, Monotone (theta n)
  /-- The Duminil-Copin–Tassion differential inequality. -/
  diff_ineq : ∀ (n : ℕ) (β : ℝ), 0 ≤ β →
      (n : ℝ) * theta n β * (1 - theta n β)
        ≤ (∑ k ∈ Finset.range n, theta k β) * deriv (theta n) β
  /-- At `β = 0` the correlations are summable. -/
  summable_zero : Summable (fun n => theta n 0)
  /-- There is an inverse temperature at which the correlations fail to be summable. -/
  exists_not_summable : ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ¬ Summable (fun n => theta n β₀)

namespace IsingSharpnessData

variable (D : IsingSharpnessData)

/-- The set of inverse temperatures at which the correlations are summable
(the "subcritical" regime). -/
def subcritical : Set ℝ := {β : ℝ | 0 ≤ β ∧ Summable (fun n => D.theta n β)}

/-- The critical inverse temperature `β_c`, defined as the supremum of the subcritical
regime. -/
noncomputable def betaC : ℝ := sSup D.subcritical

lemma zero_mem_subcritical : (0 : ℝ) ∈ D.subcritical := ⟨le_rfl, D.summable_zero⟩

lemma subcritical_nonempty : D.subcritical.Nonempty := ⟨0, D.zero_mem_subcritical⟩

lemma deriv_nonneg (n : ℕ) (β : ℝ) : 0 ≤ deriv (D.theta n) β :=
  (D.mono_beta n).deriv_nonneg

lemma subcritical_bddAbove : BddAbove D.subcritical := by
  obtain ⟨β₀, hβ₀, hns⟩ := D.exists_not_summable
  refine ⟨β₀, ?_⟩
  intro β hβ
  by_contra hlt
  push_neg at hlt
  exact hns <| hβ.2.of_nonneg_of_le (fun n => D.nonneg n β₀)
    (fun n => D.mono_beta n hlt.le)

lemma betaC_nonneg : 0 ≤ D.betaC :=
  le_csSup D.subcritical_bddAbove D.zero_mem_subcritical

/-- Key comparison step: if the partial sums `∑_{k<n} θ_k` are bounded by `L` on `[β, β₁]`
and `θ_n(β₁) ≤ 1/2`, then the differential inequality forces exponential decay of
`θ_n` when going down from `β₁` to `β`. -/
lemma exp_decay_step {n : ℕ} {L β β₁ : ℝ} (hβ : 0 ≤ β) (hββ₁ : β ≤ β₁) (hL : 0 < L)
    (hS : ∀ x ∈ Set.Icc β β₁, (∑ k ∈ Finset.range n, D.theta k x) ≤ L)
    (hhalf : D.theta n β₁ ≤ 1 / 2) :
    D.theta n β ≤ D.theta n β₁ * Real.exp (-((n : ℝ) * (β₁ - β) / (2 * L))) := by
  set a : ℝ := (n : ℝ) / (2 * L) with ha
  set g : ℝ → ℝ := fun x => D.theta n x * Real.exp (-(a * x)) with hg
  have hderiv : ∀ x : ℝ, HasDerivAt g
      (deriv (D.theta n) x * Real.exp (-(a * x))
        + D.theta n x * (Real.exp (-(a * x)) * (-a))) x := by
    intro x
    have h1 : HasDerivAt (D.theta n) (deriv (D.theta n) x) x :=
      (D.differentiable n x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (Real.exp (-(a * x)) * (-a)) x := by
      have : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        simpa using ((hasDerivAt_id x).const_mul a).neg
      simpa using this.exp
    exact h1.mul h2
  have hmono : MonotoneOn g (Set.Icc β β₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun x _ => ((hderiv x).differentiableAt).continuousAt.continuousWithinAt
    · exact fun x _ => ((hderiv x).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Set.Icc β β₁ := ⟨hx.1.le, hx.2.le⟩
      have hx0 : 0 ≤ x := hβ.trans hx.1.le
      have hθhalf : D.theta n x ≤ 1 / 2 := le_trans (D.mono_beta n hx.2.le) hhalf
      have hDI := D.diff_ineq n x hx0
      have hSle : (∑ k ∈ Finset.range n, D.theta k x) * deriv (D.theta n) x
          ≤ L * deriv (D.theta n) x :=
        mul_le_mul_of_nonneg_right (hS x hxI) (D.deriv_nonneg n x)
      have hkey : (n : ℝ) * D.theta n x * (1 / 2) ≤ L * deriv (D.theta n) x := by
        refine le_trans ?_ (hDI.trans hSle)
        have h1 : (1 : ℝ) / 2 ≤ 1 - D.theta n x := by linarith
        have h2 : (0 : ℝ) ≤ (n : ℝ) * D.theta n x :=
          mul_nonneg (Nat.cast_nonneg n) (D.nonneg n x)
        exact mul_le_mul_of_nonneg_left h1 h2
      have hderiv_ge : a * D.theta n x ≤ deriv (D.theta n) x := by
        rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith [hkey]
      have hgd : deriv g x = deriv (D.theta n) x * Real.exp (-(a * x))
          + D.theta n x * (Real.exp (-(a * x)) * (-a)) := (hderiv x).deriv
      rw [hgd]
      have hexp : 0 < Real.exp (-(a * x)) := Real.exp_pos _
      nlinarith [hexp, hderiv_ge]
  have hle : g β ≤ g β₁ :=
    hmono (Set.left_mem_Icc.2 hββ₁) (Set.right_mem_Icc.2 hββ₁) hββ₁
  have hexpβ : (0 : ℝ) < Real.exp (-(a * β)) := Real.exp_pos _
  have : D.theta n β ≤ D.theta n β₁ * Real.exp (-(a * β₁)) / Real.exp (-(a * β)) := by
    rw [le_div_iff₀ hexpβ]
    simpa [hg] using hle
  refine this.trans_eq ?_
  rw [div_eq_iff (ne_of_gt hexpβ), mul_assoc, ← Real.exp_add]
  congr 1
  rw [ha]
  congr 1
  field_simp
  ring

/-- **Exponential decay in the subcritical regime.**  For `0 ≤ β < β_c` the finite-volume
order parameter decays exponentially fast. -/
theorem exp_decay_of_lt_betaC {β : ℝ} (hβ : 0 ≤ β) (hlt : β < D.betaC) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, D.theta n β ≤ C * Real.exp (-c * n) := by
  obtain ⟨β₁, hβ₁mem, hββ₁⟩ :=
    exists_lt_of_lt_csSup D.subcritical_nonempty hlt
  obtain ⟨hβ₁0, hsum⟩ := hβ₁mem
  set L : ℝ := max 1 (∑' n, D.theta n β₁) with hLdef
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hS : ∀ (n : ℕ), ∀ x ∈ Set.Icc β β₁, (∑ k ∈ Finset.range n, D.theta k x) ≤ L := by
    intro n x hx
    have h1 : (∑ k ∈ Finset.range n, D.theta k x)
        ≤ ∑ k ∈ Finset.range n, D.theta k β₁ :=
      Finset.sum_le_sum fun k _ => D.mono_beta k hx.2
    have h2 : (∑ k ∈ Finset.range n, D.theta k β₁) ≤ ∑' k, D.theta k β₁ :=
      Summable.sum_le_tsum _ (fun k _ => D.nonneg k β₁) hsum
    exact (h1.trans h2).trans (le_max_right _ _)
  -- eventually `θ_n(β₁) ≤ 1/2`
  have htend : Filter.Tendsto (fun n => D.theta n β₁) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev : ∀ᶠ n in Filter.atTop, D.theta n β₁ ≤ 1 / 2 := by
    exact htend.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(β₁ - β) / (2 * L), div_pos (by linarith) (by linarith), Real.exp ((β₁ - β) / (2 * L) * N),
    Real.exp_pos _, ?_⟩
  intro n
  set c : ℝ := (β₁ - β) / (2 * L) with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos (by linarith) (by linarith)
  by_cases hn : N ≤ n
  · have hstep := D.exp_decay_step hβ hββ₁.le hL (hS n) (hN n hn)
    have h1 : D.theta n β ≤ Real.exp (-(c * n)) := by
      refine hstep.trans ?_
      have : (n : ℝ) * (β₁ - β) / (2 * L) = c * n := by rw [hc]; ring
      rw [this]
      calc D.theta n β₁ * Real.exp (-(c * n)) ≤ 1 * Real.exp (-(c * n)) :=
            mul_le_mul_of_nonneg_right (D.le_one n β₁) (Real.exp_pos _).le
        _ = Real.exp (-(c * n)) := one_mul _
    refine h1.trans ?_
    have h2 : (1 : ℝ) ≤ Real.exp (c * N) :=
      Real.one_le_exp (mul_nonneg hcpos.le (Nat.cast_nonneg N))
    calc Real.exp (-(c * n)) = 1 * Real.exp (-c * n) := by ring_nf
      _ ≤ Real.exp (c * N) * Real.exp (-c * n) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  · push_neg at hn
    have h1 : D.theta n β ≤ 1 := D.le_one n β
    refine h1.trans ?_
    have : Real.exp (c * N) * Real.exp (-c * n) = Real.exp (c * (N - n)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact Real.one_le_exp (by nlinarith [hcpos, (Nat.cast_lt (α := ℝ)).2 hn])

end IsingSharpnessData

open IsingSharpnessData in
/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin, abstract form).

Given the Duminil-Copin–Tassion differential inequality for the finite-volume order
parameters `θ_n` of the Ising model, the critical inverse temperature `β_c` is sharp:

* `β_c ≥ 0`;
* for every `0 ≤ β < β_c` the correlations decay exponentially fast
  (there is no intermediate regime of slow decay);
* for every `β > β_c` the correlations are not summable (long-range order).
-/
theorem duminil_ising_sharp (D : IsingSharpnessData) :
    0 ≤ D.betaC ∧
    (∀ β : ℝ, 0 ≤ β → β < D.betaC →
      ∃ c > 0, ∃ C > 0, ∀ n : ℕ, D.theta n β ≤ C * Real.exp (-c * n)) ∧
    (∀ β : ℝ, D.betaC < β → ¬ Summable (fun n => D.theta n β)) := by
  refine ⟨D.betaC_nonneg, fun β hβ hlt => D.exp_decay_of_lt_betaC hβ hlt, ?_⟩
  intro β hβ hsum
  have : β ∈ D.subcritical := ⟨le_trans D.betaC_nonneg hβ.le, hsum⟩
  exact absurd (le_csSup D.subcritical_bddAbove this) (not_le.2 hβ)

/-! ### Non-vacuity: the hypotheses are consistent

We exhibit an explicit family `θ_n(β) = φ(β)^n`, with `φ(β) = exp (-(max (1-β) 0)^2)`,
satisfying all the assumptions of `Frontier.IsingSharpnessData`.  In particular the
sharpness theorem above is not vacuous. -/

namespace Model

open Filter

/-- The auxiliary profile `v β = (max (1 - β) 0) ^ 2`. -/
noncomputable def vfun (β : ℝ) : ℝ := (max (1 - β) 0) ^ 2

/-- The base of the model family, `φ β = exp (-v β) ∈ (0, 1]`. -/
noncomputable def phi (β : ℝ) : ℝ := Real.exp (-(vfun β))

/-- The model family `θ_n(β) = φ(β)^n`. -/
noncomputable def theta (n : ℕ) (β : ℝ) : ℝ := (phi β) ^ n

lemma vfun_nonneg (β : ℝ) : 0 ≤ vfun β := by rw [vfun]; positivity

lemma vfun_le_sq (x : ℝ) : vfun x ≤ (x - 1) ^ 2 := by
  rcases le_total (1 - x) 0 with h | h
  · rw [vfun, max_eq_right h]; simpa using sq_nonneg (x - 1)
  · rw [vfun, max_eq_left h]; exact le_of_eq (by ring)

lemma vfun_antitone : Antitone vfun := by
  intro a b hab
  have h : max (1 - b) 0 ≤ max (1 - a) 0 := max_le_max (by linarith) le_rfl
  exact pow_le_pow_left₀ (le_max_right _ _) h 2

lemma vfun_hasDerivAt (β : ℝ) : HasDerivAt vfun (-2 * max (1 - β) 0) β := by
  rcases lt_trichotomy β 1 with h | h | h
  · have heq : vfun =ᶠ[nhds β] fun x : ℝ => (1 - x) ^ 2 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [Set.mem_Iio] at hx
      simp [vfun, max_eq_left (by linarith : (0:ℝ) ≤ 1 - x)]
    have hd : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (-2 * (1 - β)) β := by
      have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) β := by
        simpa using (hasDerivAt_id β).const_sub 1
      simpa [mul_comm, mul_assoc, mul_left_comm] using h1.pow 2
    rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - β)]
    exact hd.congr_of_eventuallyEq heq
  · subst h
    rw [show max (1 - (1:ℝ)) 0 = 0 by norm_num, mul_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    have hsq : ∀ x : ℝ, ‖slope vfun 1 x‖ ≤ ‖x - 1‖ := by
      intro x
      rcases eq_or_ne x 1 with rfl | hx
      · simp [slope]
      · have hv1 : vfun 1 = 0 := by simp [vfun]
        have hs : slope vfun 1 x = vfun x / (x - 1) := by
          rw [slope_def_field]; simp [hv1]
        have habs : (0:ℝ) < |x - 1| := abs_pos.2 (sub_ne_zero.2 hx)
        rw [hs, Real.norm_eq_abs, abs_div, abs_of_nonneg (vfun_nonneg x),
          div_le_iff₀ habs, Real.norm_eq_abs]
        calc vfun x ≤ (x - 1) ^ 2 := vfun_le_sq x
          _ = |x - 1| * |x - 1| := by rw [abs_mul_abs_self]; ring
    have hg : Tendsto (fun x : ℝ => ‖x - 1‖) (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
      have hc : Continuous (fun x : ℝ => ‖x - 1‖) := (continuous_id.sub continuous_const).norm
      have hct : Tendsto (fun x : ℝ => ‖x - 1‖) (nhds 1) (nhds 0) := by
        simpa using hc.tendsto (1:ℝ)
      exact hct.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm (fun x => hsq x) hg
  · have heq : vfun =ᶠ[nhds β] fun _ : ℝ => (0:ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [Set.mem_Ioi] at hx
      simp [vfun, max_eq_right (by linarith : (1:ℝ) - x ≤ 0)]
    rw [max_eq_right (by linarith : (1:ℝ) - β ≤ 0), mul_zero]
    exact (hasDerivAt_const β (0:ℝ)).congr_of_eventuallyEq heq

lemma phi_pos (β : ℝ) : 0 < phi β := Real.exp_pos _

lemma phi_le_one (β : ℝ) : phi β ≤ 1 := by
  rw [phi, Real.exp_le_one_iff]
  simpa using vfun_nonneg β

lemma phi_monotone : Monotone phi := by
  intro a b hab
  rw [phi, phi, Real.exp_le_exp]
  simpa using vfun_antitone hab

lemma phi_hasDerivAt (β : ℝ) : HasDerivAt phi (phi β * (2 * max (1 - β) 0)) β := by
  have h := ((vfun_hasDerivAt β).neg).exp
  simpa [phi, mul_comm, mul_assoc, mul_left_comm] using h

lemma theta_hasDerivAt (n : ℕ) (β : ℝ) :
    HasDerivAt (theta n) ((n : ℝ) * phi β ^ (n - 1) * (phi β * (2 * max (1 - β) 0))) β :=
  (phi_hasDerivAt β).pow n

lemma theta_deriv (n : ℕ) (β : ℝ) :
    deriv (theta n) β = (n : ℝ) * phi β ^ (n - 1) * (phi β * (2 * max (1 - β) 0)) :=
  (theta_hasDerivAt n β).deriv

lemma one_sub_phi_le (β : ℝ) : 1 - phi β ≤ vfun β := by
  have := Real.add_one_le_exp (-(vfun β))
  rw [phi]
  linarith

/-- The explicit model satisfies the Duminil-Copin–Tassion differential inequality. -/
lemma theta_diff_ineq (n : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    (n : ℝ) * theta n β * (1 - theta n β)
      ≤ (∑ k ∈ Finset.range n, theta k β) * deriv (theta n) β := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set p : ℝ := phi β with hp
  set s : ℝ := max (1 - β) 0 with hs
  have hs0 : 0 ≤ s := le_max_right _ _
  have hs1 : s ≤ 1 := max_le (by linarith) (by norm_num)
  have hp0 : 0 < p := phi_pos β
  have hp1 : p ≤ 1 := phi_le_one β
  have hS : (∑ k ∈ Finset.range n, theta k β) = ∑ k ∈ Finset.range n, p ^ k := rfl
  have hgeom : (∑ k ∈ Finset.range n, p ^ k) * (p - 1) = p ^ n - 1 := geom_sum_mul p n
  have hSnn : 0 ≤ ∑ k ∈ Finset.range n, p ^ k :=
    Finset.sum_nonneg fun k _ => pow_nonneg hp0.le k
  -- the key pointwise inequality `1 - p ≤ 2 s`
  have hkey : 1 - p ≤ 2 * s := by
    have h1 : 1 - p ≤ vfun β := one_sub_phi_le β
    have h2 : vfun β = s ^ 2 := by rw [vfun, hs]
    nlinarith [hs0, hs1]
  have hpow : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hS, theta_deriv n β]
  have hleft : (n : ℝ) * theta n β * (1 - theta n β)
      = (n : ℝ) * p ^ n * ((1 - p) * (∑ k ∈ Finset.range n, p ^ k)) := by
    have : (1 - p ^ n) = (1 - p) * ∑ k ∈ Finset.range n, p ^ k := by
      have := hgeom
      nlinarith [hgeom]
    rw [theta, ← hp, this]
  rw [hleft]
  have hfac : (∑ k ∈ Finset.range n, p ^ k) * ((n : ℝ) * p ^ (n - 1) * (p * (2 * s)))
      = (n : ℝ) * p ^ n * ((2 * s) * (∑ k ∈ Finset.range n, p ^ k)) := by
    rw [hpow]; ring
  rw [hfac]
  have hnn : 0 ≤ (n : ℝ) * p ^ n := by positivity
  have := mul_le_mul_of_nonneg_right hkey hSnn
  exact mul_le_mul_of_nonneg_left this hnn

/-- The explicit family assembles into a valid `IsingSharpnessData`. -/
noncomputable def data : IsingSharpnessData where
  theta := theta
  differentiable := fun n β => (theta_hasDerivAt n β).differentiableAt
  nonneg := fun n β => pow_nonneg (phi_pos β).le n
  le_one := fun n β => pow_le_one₀ (phi_pos β).le (phi_le_one β)
  mono_beta := fun n a b hab => pow_le_pow_left₀ (phi_pos a).le (phi_monotone hab) n
  diff_ineq := theta_diff_ineq
  summable_zero := by
    have h : ∀ n : ℕ, theta n 0 = (phi 0) ^ n := fun n => rfl
    simpa [h] using summable_geometric_of_lt_one (phi_pos 0).le
      (by
        have : vfun 0 = 1 := by norm_num [vfun]
        rw [phi, this]
        simp)
  exists_not_summable := by
    refine ⟨1, by norm_num, ?_⟩
    have h1 : ∀ n : ℕ, theta n 1 = 1 := by
      intro n
      have : vfun 1 = 0 := by norm_num [vfun]
      simp [theta, phi, this]
    intro hsum
    have := hsum.tendsto_atTop_zero
    rw [show (fun n : ℕ => theta n 1) = fun _ : ℕ => (1:ℝ) from funext h1] at this
    have h0 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds this
    norm_num at h0

/-- The assumptions of `Frontier.IsingSharpnessData` are satisfiable. -/
theorem nonempty_isingSharpnessData : Nonempty IsingSharpnessData := ⟨data⟩

lemma summable_theta_iff (β : ℝ) : Summable (fun n => theta n β) ↔ phi β < 1 := by
  have h : (fun n : ℕ => theta n β) = fun n : ℕ => (phi β) ^ n := rfl
  rw [h, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_pos (phi_pos β)]

lemma phi_lt_one_iff (β : ℝ) : phi β < 1 ↔ β < 1 := by
  rw [phi, Real.exp_lt_one_iff, neg_neg_iff_pos]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rw [vfun, max_eq_right (by linarith)] at h
    simp at h
  · intro h
    rw [vfun, max_eq_left (by linarith)]
    exact pow_pos (by linarith) 2

/-- For the explicit model the subcritical regime is exactly `[0, 1)`. -/
lemma data_subcritical : data.subcritical = Set.Ico (0:ℝ) 1 := by
  ext β
  constructor
  · rintro ⟨h0, hsum⟩
    exact ⟨h0, (phi_lt_one_iff β).1 ((summable_theta_iff β).1 hsum)⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, (summable_theta_iff β).2 ((phi_lt_one_iff β).2 h1)⟩

/-- For the explicit model the critical inverse temperature equals `1`. -/
lemma data_betaC : data.betaC = 1 := by
  rw [IsingSharpnessData.betaC, data_subcritical]
  exact csSup_Ico (by norm_num)

/-- A non-vacuous instance of the sharpness theorem: in the explicit model the correlations
decay exponentially at every inverse temperature below the critical value `1`, and fail to
be summable above it. -/
theorem model_sharp :
    (∀ β : ℝ, 0 ≤ β → β < 1 →
      ∃ c > 0, ∃ C > 0, ∀ n : ℕ, theta n β ≤ C * Real.exp (-c * n)) ∧
    (∀ β : ℝ, 1 < β → ¬ Summable (fun n => theta n β)) := by
  obtain ⟨-, hdecay, hdiv⟩ := duminil_ising_sharp data
  rw [data_betaC] at hdecay hdiv
  exact ⟨hdecay, hdiv⟩

end Model

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

