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

/-- Exponential decay from a strict contraction over a fixed scale `L`:
if `0 ≤ a n ≤ 1` and `a (n + L) ≤ c * a n` with `0 < c < 1`, then `a` decays exponentially. -/
theorem exp_decay_of_contraction {a : ℕ → ℝ} (hle : ∀ n : ℕ, a n ≤ 1)
    {L : ℕ} (hL : 0 < L) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hstep : ∀ n : ℕ, a (n + L) ≤ c * a n) :
    ∃ C > 0, ∃ γ > 0, ∀ n : ℕ, a n ≤ C * Real.exp (-γ * n) := by
  have key : ∀ k r : ℕ, a (k * L + r) ≤ c ^ k * a r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
      intro r
      have h1 : (k + 1) * L + r = (k * L + r) + L := by ring
      rw [h1]
      calc a ((k * L + r) + L) ≤ c * a (k * L + r) := hstep _
        _ ≤ c * (c ^ k * a r) := mul_le_mul_of_nonneg_left (ih r) hc0.le
        _ = c ^ (k + 1) * a r := by ring
  have hlogc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  refine ⟨c⁻¹, by positivity, (-Real.log c) / L, div_pos (by linarith) hLpos, ?_⟩
  intro n
  have hnL : n = (n / L) * L + n % L := (Nat.div_add_mod' n L).symm
  have h1 : a n ≤ c ^ (n / L) := by
    calc a n = a ((n / L) * L + n % L) := by rw [← hnL]
      _ ≤ c ^ (n / L) * a (n % L) := key _ _
      _ ≤ c ^ (n / L) * 1 := mul_le_mul_of_nonneg_left (hle _) (by positivity)
      _ = c ^ (n / L) := by ring
  have hkr : ((n:ℝ) / L) - 1 ≤ ((n / L : ℕ) : ℝ) := by
    have hmod : n % L < L := Nat.mod_lt _ hL
    have h2 : (n : ℝ) < ((n / L : ℕ) : ℝ) * L + L := by
      have hn : n < (n / L) * L + L := by omega
      exact_mod_cast hn
    rw [sub_le_iff_le_add, div_le_iff₀ hLpos]
    nlinarith
  have h2 : (c : ℝ) ^ ((n / L : ℕ) : ℝ) ≤ c ^ (((n:ℝ) / L) - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le hkr
  rw [Real.rpow_natCast] at h2
  have hexp : -((-Real.log c) / L) * (n : ℝ) = Real.log c * ((n : ℝ) / L) := by
    field_simp
  have h4 : (c : ℝ) ^ (((n:ℝ) / L) - 1) = c⁻¹ * Real.exp (-((-Real.log c) / L) * n) := by
    rw [Real.rpow_sub hc0, Real.rpow_one, Real.rpow_def_of_pos hc0, hexp]
    ring
  calc a n ≤ c ^ (n / L) := h1
    _ ≤ (c : ℝ) ^ (((n:ℝ) / L) - 1) := h2
    _ = c⁻¹ * Real.exp (-((-Real.log c) / L) * n) := h4

/-- Grönwall-type lower bound: from the differential inequality `m' ≥ c₀ (1 - m)` above `b`
and `m b ≥ 0` one gets `m β ≥ 1 - exp (-c₀ (β - b))`. -/
theorem gronwall_lower {m : ℝ → ℝ} {b c0 : ℝ}
    (hcont : ContinuousOn m (Set.Ici b))
    (hdiff : ∀ x : ℝ, b < x → DifferentiableAt ℝ m x)
    (hder : ∀ x : ℝ, b < x → c0 * (1 - m x) ≤ deriv m x)
    (hm0 : 0 ≤ m b) :
    ∀ β : ℝ, b < β → 1 - Real.exp (-(c0 * (β - b))) ≤ m β := by
  intro β hβ
  set h : ℝ → ℝ := fun x => (1 - m x) * Real.exp (c0 * (x - b)) with hh
  have hderiv : ∀ x ∈ Set.Ioo b β, HasDerivAt h
      (-(deriv m x) * Real.exp (c0 * (x - b)) + (1 - m x) * (Real.exp (c0 * (x - b)) * c0)) x := by
    intro x hx
    have hm : HasDerivAt m (deriv m x) x := (hdiff x hx.1).hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => 1 - m y) (-(deriv m x)) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub hm
    have hlin : HasDerivAt (fun y : ℝ => c0 * (y - b)) c0 x := by
      simpa using ((hasDerivAt_id x).sub_const b).const_mul c0
    exact h1.mul hlin.exp
  have hcontIcc : ContinuousOn h (Set.Icc b β) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.sub (hcont.mono Set.Icc_subset_Ici_self)
    · fun_prop
  have hanti : AntitoneOn h (Set.Icc b β) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc b β) hcontIcc
    · rw [interior_Icc]
      intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      have hexp : 0 < Real.exp (c0 * (x - b)) := Real.exp_pos _
      nlinarith [hder x hx.1]
  have hle : h β ≤ h b := hanti (Set.left_mem_Icc.2 hβ.le) (Set.right_mem_Icc.2 hβ.le) hβ.le
  simp only [hh] at hle
  simp at hle
  have hexp : 0 < Real.exp (c0 * (β - b)) := Real.exp_pos _
  have h5 : (1 - m β) ≤ (1 - m b) * Real.exp (-(c0 * (β - b))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
    exact hle
  nlinarith [Real.exp_pos (-(c0 * (β - b))), hm0, h5]

/-- Abstract data describing an Ising-type model on a transitive graph:
`corr β n` is the two-point function `⟨σ₀ σₓ⟩_β` at distance `n`, `mag β` the
spontaneous magnetisation `⟨σ₀⟩⁺_β`, and `betaC` the threshold produced by the
Duminil-Copin–Tassion argument.  The fields record the two key inputs of that
argument: a strict contraction of the two-point function below `betaC`, and a
differential inequality for the magnetisation above `betaC`. -/
structure IsingSharpData where
  /-- the two-point function `⟨σ₀ σₓ⟩_β` for `x` at distance `n` from the origin -/
  corr : ℝ → ℕ → ℝ
  /-- the spontaneous magnetisation `⟨σ₀⟩⁺_β` -/
  mag : ℝ → ℝ
  /-- the critical parameter -/
  betaC : ℝ
  /-- constant in the differential inequality -/
  c0 : ℝ
  c0_pos : 0 < c0
  corr_nonneg : ∀ (β : ℝ) (n : ℕ), 0 ≤ corr β n
  corr_le_one : ∀ (β : ℝ) (n : ℕ), corr β n ≤ 1
  mag_nonneg : ∀ β : ℝ, 0 ≤ mag β
  mag_cont : ContinuousOn mag (Set.Ici betaC)
  /-- squared magnetisation is dominated by the two-point function -/
  mag_sq_le_corr : ∀ (β : ℝ) (n : ℕ), (mag β) ^ 2 ≤ corr β n
  /-- subcritical input: strict contraction of the two-point function at some scale -/
  subcritical : ∀ β : ℝ, 0 ≤ β → β < betaC →
    ∃ L : ℕ, 0 < L ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ n : ℕ, corr β (n + L) ≤ c * corr β n
  /-- supercritical input: the Duminil-Copin–Tassion differential inequality -/
  supercritical : ∀ β : ℝ, betaC < β →
    DifferentiableAt ℝ mag β ∧ c0 * (1 - mag β) ≤ deriv mag β

/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin), stated
as a Lean-checked reduction to the two inputs of the Duminil-Copin–Tassion argument.

Below the critical parameter the two-point function decays exponentially and the
spontaneous magnetisation vanishes; above it the magnetisation grows at least
linearly in `β - βc`. -/
theorem duminil_ising_sharp (D : IsingSharpData) :
    (∀ β : ℝ, 0 ≤ β → β < D.betaC →
        ∃ C > 0, ∃ γ > 0, ∀ n : ℕ, D.corr β n ≤ C * Real.exp (-γ * n)) ∧
    (∀ β : ℝ, 0 ≤ β → β < D.betaC → D.mag β = 0) ∧
    (∃ c > 0, ∀ β : ℝ, D.betaC < β → β ≤ D.betaC + 1 → c * (β - D.betaC) ≤ D.mag β) := by
  -- Subcritical regime: exponential decay of the two-point function.
  have hdecay : ∀ β : ℝ, 0 ≤ β → β < D.betaC →
      ∃ C > 0, ∃ γ > 0, ∀ n : ℕ, D.corr β n ≤ C * Real.exp (-γ * n) := by
    intro β hβ0 hβ
    obtain ⟨L, hL, c, hc0, hc1, hstep⟩ := D.subcritical β hβ0 hβ
    exact exp_decay_of_contraction (fun n => D.corr_le_one β n) hL hc0 hc1 hstep
  refine ⟨hdecay, ?_, ?_⟩
  · -- Subcritical regime: the spontaneous magnetisation vanishes.
    intro β hβ0 hβ
    obtain ⟨C, _, γ, hγ, hCγ⟩ := hdecay β hβ0 hβ
    set M := D.mag β with hM
    have hM0 : 0 ≤ M := D.mag_nonneg β
    have hbnd : ∀ n : ℕ, M ^ 2 ≤ C * Real.exp (-γ * n) := fun n =>
      le_trans (D.mag_sq_le_corr β n) (hCγ n)
    have hr : Real.exp (-γ) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    have hr0 : (0:ℝ) ≤ Real.exp (-γ) := (Real.exp_pos _).le
    have hpow : ∀ n : ℕ, Real.exp (-γ * n) = (Real.exp (-γ)) ^ n := by
      intro n
      rw [← Real.exp_nat_mul]
      ring_nf
    have htend : Filter.Tendsto (fun n : ℕ => C * (Real.exp (-γ)) ^ n) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr
      simpa using h.const_mul C
    have hsq : M ^ 2 ≤ 0 := by
      refine ge_of_tendsto htend ?_
      filter_upwards with n
      have h := hbnd n
      rwa [hpow n] at h
    have hzero : M ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    nlinarith [hzero]
  · -- Supercritical regime: linear lower bound on the magnetisation.
    have hc0 : 0 < D.c0 := D.c0_pos
    refine ⟨D.c0 / (1 + D.c0), div_pos hc0 (by linarith), ?_⟩
    intro β hβ hβ1
    have hgr := gronwall_lower (m := D.mag) (b := D.betaC) (c0 := D.c0)
      D.mag_cont (fun x hx => (D.supercritical x hx).1)
      (fun x hx => (D.supercritical x hx).2) (D.mag_nonneg _) β hβ
    set t := β - D.betaC with ht
    have htpos : 0 < t := by simp only [ht]; linarith
    have ht1 : t ≤ 1 := by simp only [ht]; linarith
    set x := D.c0 * t with hx
    have hxpos : 0 < x := mul_pos hc0 htpos
    have hxle : x ≤ D.c0 := by nlinarith
    have hE : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hEpos : 0 < Real.exp x := Real.exp_pos x
    have hinv : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
    have hmul : Real.exp x * (Real.exp x)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hEpos)
    have hu : 0 < (Real.exp x)⁻¹ := by positivity
    have hkey : x / (1 + D.c0) ≤ 1 - Real.exp (-x) := by
      rw [hinv, div_le_iff₀ (by linarith)]
      nlinarith [hu, hmul, hE, hxle]
    have heq : D.c0 / (1 + D.c0) * t = x / (1 + D.c0) := by rw [hx]; ring
    linarith [hkey, hgr, heq.le, heq.ge]

end Frontier

