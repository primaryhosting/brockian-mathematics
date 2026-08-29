import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

namespace Phys

/-! ## The two–dimensional XY model -/

/-- Sites of the two-dimensional square lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- The XY-model Hamiltonian `H(θ) = -J ∑_{⟨xy⟩} cos (θ x - θ y)` for a finite collection
of nearest-neighbour bonds. -/
noncomputable def xyEnergy (J : ℝ) (bonds : Finset (Site × Site)) (θ : Site → ℝ) : ℝ :=
  -J * ∑ b ∈ bonds, Real.cos (θ b.1 - θ b.2)

/-- The XY Hamiltonian is invariant under the global `O(2)` rotation `θ ↦ θ + α`: the model
has a continuous internal symmetry (which, by Mermin–Wagner, cannot be broken in two
dimensions — the BKT transition is therefore *topological*, not a symmetry-breaking one). -/
theorem xyEnergy_rotation_invariant (J : ℝ) (bonds : Finset (Site × Site)) (θ : Site → ℝ)
    (α : ℝ) : xyEnergy J bonds (fun x => θ x + α) = xyEnergy J bonds θ := by
  simp [xyEnergy, add_sub_add_right_eq_sub]

/-- The energy of the fully aligned configuration is `-J * (number of bonds)`. -/
theorem xyEnergy_const (J : ℝ) (bonds : Finset (Site × Site)) (c : ℝ) :
    xyEnergy J bonds (fun _ => c) = -J * bonds.card := by
  simp [xyEnergy]

/-- For a ferromagnetic coupling `J > 0` the aligned configuration is a ground state. -/
theorem xyEnergy_ground_state (J : ℝ) (hJ : 0 ≤ J) (bonds : Finset (Site × Site))
    (θ : Site → ℝ) : -J * bonds.card ≤ xyEnergy J bonds θ := by
  have h : ∑ b ∈ bonds, Real.cos (θ b.1 - θ b.2) ≤ (bonds.card : ℝ) := by
    calc ∑ b ∈ bonds, Real.cos (θ b.1 - θ b.2) ≤ ∑ _b ∈ bonds, (1 : ℝ) :=
          Finset.sum_le_sum (fun b _ => Real.cos_le_one _)
      _ = (bonds.card : ℝ) := by simp
  have := mul_le_mul_of_nonneg_left h hJ
  simp only [xyEnergy, neg_mul]
  linarith

/-! ## Quantised vorticity: the topological charge -/

/-- The representative of an angle difference in `(-π, π]`, i.e. the lattice "gradient"
used to define the vorticity. -/
noncomputable def wrap (x : ℝ) : ℝ := Real.Angle.toReal (x : Real.Angle)

/-- The vorticity (topological charge, up to the factor `2π`) of a configuration `θ`
around an oriented elementary plaquette `p : Fin 4 → Site`. -/
noncomputable def vorticity (θ : Site → ℝ) (p : Fin 4 → Site) : ℝ :=
  ∑ i : Fin 4, wrap (θ (p (i + 1)) - θ (p i))

/-- **Quantisation of vorticity.** The circulation of the phase around a plaquette is always
an integer multiple of `2π`; this integer is the topological charge of the vortex sitting in
the plaquette. It is the existence of this ℤ-valued invariant which makes the BKT transition
possible. -/
theorem vorticity_quantized (θ : Site → ℝ) (p : Fin 4 → Site) :
    ∃ k : ℤ, vorticity θ p = 2 * Real.pi * k := by
  have hsum : ∑ i : Fin 4, (θ (p (i + 1)) - θ (p i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i : Fin 4, θ (p (i + 1)) = ∑ i : Fin 4, θ (p i) :=
      Fintype.sum_equiv (Equiv.addRight (1 : Fin 4)) _ _ (fun i => rfl)
    rw [this, sub_self]
  have hcoe : ((vorticity θ p : ℝ) : Real.Angle) = 0 := by
    have hs : ((vorticity θ p : ℝ) : Real.Angle)
        = ∑ i : Fin 4, ((wrap (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle) := by
      rw [vorticity]; rfl
    rw [hs]
    have h2 : ∀ i : Fin 4, ((wrap (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle)
        = ((θ (p (i + 1)) - θ (p i) : ℝ) : Real.Angle) := by
      intro i
      simp [wrap, Real.Angle.coe_toReal]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have : ∑ i : Fin 4, ((θ (p (i + 1)) - θ (p i) : ℝ) : Real.Angle)
        = ((∑ i : Fin 4, (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle) :=
      (map_sum Real.Angle.coeHom _ Finset.univ).symm
    rw [this, hsum]
    simp
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  exact ⟨n, by rw [← hn]; simp [zsmul_eq_mul]; ring⟩

/-! ## Energy and entropy of an isolated vortex -/

/-- The (spin-wave) energy of a single unit vortex in a box of linear size `L`, measured in
units of the lattice spacing: the energy density is `(J/2)|∇θ|²` with `|∇θ| = 1/r`, so that
integrating over the annulus `1 ≤ r ≤ L` gives `∫ (J/2) r⁻² · 2π r dr`. -/
noncomputable def vortexEnergy (J L : ℝ) : ℝ := ∫ r in (1 : ℝ)..L, Real.pi * J / r

/-- **Logarithmic vortex energy**: `E = π J log L`. -/
theorem vortexEnergy_eq (J L : ℝ) (hL : 0 < L) :
    vortexEnergy J L = Real.pi * J * Real.log L := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) L := by
    intro hmem
    rcases Set.mem_uIcc.mp hmem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have h : ∀ r : ℝ, Real.pi * J / r = (Real.pi * J) * (1 / r) := by intro r; ring
  simp only [vortexEnergy, h]
  rw [intervalIntegral.integral_const_mul, integral_one_div h0, div_one]

/-- The entropy of a single vortex in a box of linear size `L`: its core can be placed in any
of the `L²` plaquettes, so `S = log (L²)`. -/
noncomputable def vortexEntropy (L : ℝ) : ℝ := Real.log (L ^ 2)

theorem vortexEntropy_eq (L : ℝ) : vortexEntropy L = 2 * Real.log L := by
  simp [vortexEntropy, Real.log_pow]

/-- The free energy `F = E - T S` of a single vortex in a box of linear size `L`. -/
noncomputable def vortexFreeEnergy (J T L : ℝ) : ℝ :=
  vortexEnergy J L - T * vortexEntropy L

/-- **Kosterlitz–Thouless energy–entropy balance**: `F = (πJ - 2T) log L`. -/
theorem vortexFreeEnergy_eq (J T L : ℝ) (hL : 0 < L) :
    vortexFreeEnergy J T L = (Real.pi * J - 2 * T) * Real.log L := by
  rw [vortexFreeEnergy, vortexEnergy_eq J L hL, vortexEntropy_eq]
  ring

/-! ## The BKT critical temperature -/

/-- The Berezinskii–Kosterlitz–Thouless critical temperature `T_c = πJ/2`
(in units with `k_B = 1`), i.e. the temperature at which the energy of an isolated vortex is
exactly balanced by its entropy. -/
noncomputable def bktTemp (J : ℝ) : ℝ := Real.pi * J / 2

theorem bktTemp_pos {J : ℝ} (hJ : 0 < J) : 0 < bktTemp J := by
  have := Real.pi_pos
  simp only [bktTemp]
  positivity

/-- The spin-wave (Kosterlitz–Thouless) anomalous exponent `η(T) = T / (2πJ)`, governing the
power-law decay `⟨s₀ · s_r⟩ ∼ r^{-η}` of correlations in the quasi-long-range-ordered phase. -/
noncomputable def spinWaveExponent (J T : ℝ) : ℝ := T / (2 * Real.pi * J)

/-- **Universal value of the exponent at the transition**: `η(T_c) = 1/4`. -/
theorem spinWaveExponent_at_bktTemp {J : ℝ} (hJ : 0 < J) :
    spinWaveExponent J (bktTemp J) = 1 / 4 := by
  have hpi := Real.pi_pos
  rw [spinWaveExponent, bktTemp]
  field_simp
  ring

/-- **Universal jump of the helicity modulus (spin stiffness)**: at the transition the ratio of
the stiffness `ρ_s = J` to the temperature equals `2/π`. -/
theorem universal_jump {J : ℝ} (hJ : 0 < J) : J / bktTemp J = 2 / Real.pi := by
  have hpi := Real.pi_pos
  rw [bktTemp]
  field_simp

/-- The two-point function of the quasi-long-range-ordered phase, `r ↦ r^{-η(T)}`. -/
noncomputable def correlation (J T r : ℝ) : ℝ := r ^ (-spinWaveExponent J T)

theorem correlation_at_bktTemp {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    correlation J (bktTemp J) r = r ^ (-(1 / 4) : ℝ) := by
  rw [correlation, spinWaveExponent_at_bktTemp hJ]

/-- The BKT correlation length above the transition, `ξ(T) = exp (b / √(T - T_c))`: instead of
a power law it has an *essential* singularity at `T_c`. -/
noncomputable def correlationLength (J b T : ℝ) : ℝ :=
  Real.exp (b / Real.sqrt (T - bktTemp J))

/-! ## Auxiliary limits -/

private theorem tendsto_sub_nhdsWithin (c : ℝ) :
    Filter.Tendsto (fun T : ℝ => T - c) (nhdsWithin c (Set.Ioi c))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Filter.Tendsto (fun T : ℝ => T - c) (nhds c) (nhds (c - c)) :=
      (continuous_sub_right c).tendsto c
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with T hT
    simpa [sub_pos] using hT

private theorem tendsto_inv_sqrt {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun u : ℝ => b / Real.sqrt u) (nhdsWithin 0 (Set.Ioi 0))
      Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun u : ℝ => Real.sqrt u) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Filter.Tendsto (fun u : ℝ => Real.sqrt u) (nhds 0) (nhds (Real.sqrt 0)) :=
        (Real.continuous_sqrt).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simpa using Real.sqrt_pos.2 hu
  have hinv : Filter.Tendsto (fun v : ℝ => b / v) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Filter.Tendsto.const_mul_atTop hb tendsto_inv_nhdsGT_zero)
  exact hinv.comp hsqrt

private theorem tendsto_exp_inv_sqrt_mul_pow {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Filter.Tendsto (fun u : ℝ => Real.exp (b / Real.sqrt u) * u ^ n)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have key : Filter.Tendsto
      (fun v : ℝ => b ^ (2 * n) * (Real.exp v / v ^ (2 * n))) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.const_mul_atTop (by positivity) ?_
    exact Real.tendsto_exp_div_pow_atTop (2 * n)
  have hcomp := key.comp (tendsto_inv_sqrt hb)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : (0 : ℝ) < u := hu
  have hs : Real.sqrt u > 0 := Real.sqrt_pos.2 hu'
  have hsq : (Real.sqrt u) ^ (2 * n) = u ^ n := by
    rw [pow_mul, Real.sq_sqrt hu'.le]
  simp only [Function.comp_apply]
  rw [div_pow, hsq]
  field_simp

/-! ## The BKT transition -/

/-- **The Berezinskii–Kosterlitz–Thouless topological phase transition of the two-dimensional
XY model.**

For a ferromagnetic coupling `J > 0` the model, whose Hamiltonian
`H(θ) = -J ∑_{⟨xy⟩} cos(θ_x - θ_y)` is invariant under the global rotation `θ ↦ θ + α`,
carries a `ℤ`-valued topological charge (the plaquette vorticity, quantised in units of `2π`).
There is a unique critical temperature `T_c = πJ/2` such that:

* below `T_c` the free energy `F = πJ log L - T log L²` of an isolated vortex diverges to
  `+∞` with the system size: isolated vortices are suppressed and vortices stay bound in
  neutral pairs (quasi-long-range order, power-law correlations with exponent
  `η(T) = T/(2πJ)`);
* above `T_c` it diverges to `-∞`: free vortices proliferate and destroy the quasi-order
  (exponential decay with correlation length `ξ`);
* at `T = T_c` energy and entropy balance exactly, `F ≡ 0`, the exponent takes the universal
  value `η(T_c) = 1/4` and the stiffness-to-temperature ratio the universal value `2/π`;
* the correlation length has an essential singularity at `T_c`: it diverges as `T ↓ T_c`
  faster than any power of `T - T_c`. -/
theorem bkt_transition (J : ℝ) (hJ : 0 < J) :
    -- continuous symmetry of the XY Hamiltonian
    (∀ (bonds : Finset (Site × Site)) (θ : Site → ℝ) (α : ℝ),
        xyEnergy J bonds (fun x => θ x + α) = xyEnergy J bonds θ) ∧
    -- quantised topological charge
    (∀ (θ : Site → ℝ) (p : Fin 4 → Site), ∃ k : ℤ, vorticity θ p = 2 * Real.pi * k) ∧
    -- energy–entropy balance of an isolated vortex
    (∀ T L : ℝ, 0 < L → vortexFreeEnergy J T L = (Real.pi * J - 2 * T) * Real.log L) ∧
    -- the low-temperature phase: isolated vortices cost infinite free energy
    (∀ T : ℝ, T < bktTemp J →
        Filter.Tendsto (fun L => vortexFreeEnergy J T L) Filter.atTop Filter.atTop) ∧
    -- the high-temperature phase: free vortices proliferate
    (∀ T : ℝ, bktTemp J < T →
        Filter.Tendsto (fun L => vortexFreeEnergy J T L) Filter.atTop Filter.atBot) ∧
    -- exactly at the transition energy and entropy cancel
    (∀ L : ℝ, 0 < L → vortexFreeEnergy J (bktTemp J) L = 0) ∧
    -- `T_c = πJ/2` is the unique such transition temperature
    (∃! Tc : ℝ, 0 < Tc ∧
        (∀ T L : ℝ, T < Tc → 1 < L → 0 < vortexFreeEnergy J T L) ∧
        (∀ T L : ℝ, Tc < T → 1 < L → vortexFreeEnergy J T L < 0)) ∧
    -- universal values at the transition
    spinWaveExponent J (bktTemp J) = 1 / 4 ∧
    J / bktTemp J = 2 / Real.pi ∧
    (∀ r : ℝ, correlation J (bktTemp J) r = r ^ (-(1 / 4) : ℝ)) ∧
    -- essential singularity of the correlation length at `T_c`
    (∀ b : ℝ, 0 < b →
        Filter.Tendsto (fun T => correlationLength J b T)
          (nhdsWithin (bktTemp J) (Set.Ioi (bktTemp J))) Filter.atTop) ∧
    (∀ b : ℝ, 0 < b → ∀ n : ℕ,
        Filter.Tendsto (fun T => correlationLength J b T * (T - bktTemp J) ^ n)
          (nhdsWithin (bktTemp J) (Set.Ioi (bktTemp J))) Filter.atTop) := by
  have hpi := Real.pi_pos
  refine ⟨fun bonds θ α => xyEnergy_rotation_invariant J bonds θ α, vorticity_quantized,
    fun T L hL => vortexFreeEnergy_eq J T L hL, ?_, ?_, ?_, ?_,
    spinWaveExponent_at_bktTemp hJ, universal_jump hJ, correlation_at_bktTemp hJ, ?_, ?_⟩
  · -- low temperature
    intro T hT
    have hc : 0 < Real.pi * J - 2 * T := by
      simp only [bktTemp] at hT; linarith
    have : Filter.Tendsto (fun L : ℝ => (Real.pi * J - 2 * T) * Real.log L)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hc Real.tendsto_log_atTop
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    exact (vortexFreeEnergy_eq J T L hL).symm
  · -- high temperature
    intro T hT
    have hc : Real.pi * J - 2 * T < 0 := by
      simp only [bktTemp] at hT; linarith
    have h1 : Filter.Tendsto (fun L : ℝ => (-(Real.pi * J - 2 * T)) * Real.log L)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) Real.tendsto_log_atTop
    have : Filter.Tendsto (fun L : ℝ => (Real.pi * J - 2 * T) * Real.log L)
        Filter.atTop Filter.atBot :=
      (Filter.tendsto_neg_atTop_atBot.comp h1).congr (fun x => by
        simp only [Function.comp_apply]; ring)
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    exact (vortexFreeEnergy_eq J T L hL).symm
  · -- at the transition
    intro L hL
    rw [vortexFreeEnergy_eq J _ L hL, bktTemp]
    ring
  · -- uniqueness of the critical temperature
    refine ⟨bktTemp J, ⟨bktTemp_pos hJ, ?_, ?_⟩, ?_⟩
    · intro T L hT hL
      rw [vortexFreeEnergy_eq J T L (by linarith)]
      have hc : 0 < Real.pi * J - 2 * T := by simp only [bktTemp] at hT; linarith
      have : 0 < Real.log L := Real.log_pos hL
      positivity
    · intro T L hT hL
      rw [vortexFreeEnergy_eq J T L (by linarith)]
      have hc : Real.pi * J - 2 * T < 0 := by simp only [bktTemp] at hT; linarith
      have hlog : 0 < Real.log L := Real.log_pos hL
      nlinarith
    · rintro Tc ⟨hTc, hlow, hhigh⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · -- Tc < bktTemp J : take T strictly between, contradiction with hhigh
        obtain ⟨T, hT1, hT2⟩ := exists_between h
        have h1 := hhigh T 2 hT1 (by norm_num)
        rw [vortexFreeEnergy_eq J T 2 (by norm_num)] at h1
        have hc : 0 < Real.pi * J - 2 * T := by simp only [bktTemp] at hT2; linarith
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
      · obtain ⟨T, hT1, hT2⟩ := exists_between h
        have h1 := hlow T 2 hT2 (by norm_num)
        rw [vortexFreeEnergy_eq J T 2 (by norm_num)] at h1
        have hc : Real.pi * J - 2 * T < 0 := by simp only [bktTemp] at hT1; linarith
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
  · -- divergence of the correlation length
    intro b hb
    exact (Real.tendsto_exp_atTop.comp
      ((tendsto_inv_sqrt hb).comp (tendsto_sub_nhdsWithin (bktTemp J))))
  · -- essential singularity
    intro b hb n
    exact (tendsto_exp_inv_sqrt_mul_pow hb n).comp (tendsto_sub_nhdsWithin (bktTemp J))

end Phys

