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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The `n`-th (normalized) stationary state of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(n π x / L)`. -/
noncomputable def boxWave (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sqrt (2 / L) * Real.sin ((n : ℝ) * Real.pi / L * x)

/-- The first derivative of `boxWave L n`. -/
noncomputable def boxWaveD1 (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sqrt (2 / L) * ((n : ℝ) * Real.pi / L) * Real.cos ((n : ℝ) * Real.pi / L * x)

/-- The second derivative of `boxWave L n`. -/
noncomputable def boxWaveD2 (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => -(Real.sqrt (2 / L) * ((n : ℝ) * Real.pi / L) ^ 2 *
    Real.sin ((n : ℝ) * Real.pi / L * x))

/-- `psi` is a bound state of energy `E` for a particle of mass `m` in the infinite square well
`[0, L]`: it is twice differentiable on `ℝ` (with derivatives `psi'` and `psi''`), it satisfies
the time-independent Schrödinger equation `-(ℏ²/2m) ψ'' = E ψ`, it vanishes at the walls of the
well, and it is not identically zero inside the well. -/
structure IsBoxEigenstate (hbar m L E : ℝ) (psi psi' psi'' : ℝ → ℝ) : Prop where
  hasDerivAt_psi : ∀ x : ℝ, HasDerivAt psi (psi' x) x
  hasDerivAt_psi' : ∀ x : ℝ, HasDerivAt psi' (psi'' x) x
  schrodinger : ∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * psi'' x = E * psi x
  wall_left : psi 0 = 0
  wall_right : psi L = 0
  nontrivial : ∃ x ∈ Set.Icc (0 : ℝ) L, psi x ≠ 0

/-- `boxWaveD1 L n` is the derivative of `boxWave L n`. -/
lemma hasDerivAt_boxWave (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxWave L n) (boxWaveD1 L n x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi / L * y) ((n : ℝ) * Real.pi / L) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)
  have h2 := (Real.hasDerivAt_sin ((n : ℝ) * Real.pi / L * x)).comp x h1
  have h3 := h2.const_mul (Real.sqrt (2 / L))
  refine h3.congr_deriv ?_
  simp only [boxWaveD1]
  ring

/-- `boxWaveD2 L n` is the derivative of `boxWaveD1 L n`. -/
lemma hasDerivAt_boxWaveD1 (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxWaveD1 L n) (boxWaveD2 L n x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi / L * y) ((n : ℝ) * Real.pi / L) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)
  have h2 := (Real.hasDerivAt_cos ((n : ℝ) * Real.pi / L * x)).comp x h1
  have h3 := h2.const_mul (Real.sqrt (2 / L) * ((n : ℝ) * Real.pi / L))
  refine h3.congr_deriv ?_
  simp only [boxWaveD2]
  ring

/-- The stationary state `ψ_n` is normalized on the well: `∫₀^L |ψ_n|² = 1`. -/
lemma boxWave_normalized {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, (boxWave L n x) ^ 2 = 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hk : ((n : ℝ) * Real.pi / L) ≠ 0 := by positivity
  have hsq : (Real.sqrt (2 / L)) ^ 2 = 2 / L := Real.sq_sqrt (by positivity)
  have hpt : ∀ x : ℝ, (boxWave L n x) ^ 2
      = (2 / L) * Real.sin ((n : ℝ) * Real.pi / L * x) ^ 2 := by
    intro x; rw [boxWave, mul_pow, hsq]
  rw [intervalIntegral.integral_congr
      (g := fun x => (2 / L) * Real.sin ((n : ℝ) * Real.pi / L * x) ^ 2) (fun x _ => hpt x),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun y => Real.sin y ^ 2) hk, integral_sin_sq]
  have h1 : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
  rw [mul_zero, h1, Real.sin_nat_mul_pi]
  simp only [Real.sin_zero, Real.cos_zero, smul_eq_mul]
  field_simp
  ring

/-- **Existence of the levels.** For every `n ≥ 1` the function `ψ_n` is a bound state of the
infinite square well with energy `E_n = n²π²ℏ²/(2mL²)`. -/
theorem isBoxEigenstate_boxWave {hbar m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    {n : ℕ} (hn : 1 ≤ n) :
    IsBoxEigenstate hbar m L (boxEnergy hbar m L n) (boxWave L n) (boxWaveD1 L n)
      (boxWaveD2 L n) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hm' : m ≠ 0 := ne_of_gt hm
  refine ⟨hasDerivAt_boxWave L n, hasDerivAt_boxWaveD1 L n, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [boxWaveD2, boxWave, boxEnergy]
    field_simp
  · simp [boxWave]
  · simp only [boxWave]
    have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
    rw [this, Real.sin_nat_mul_pi]
    ring
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn' : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · simp only [boxWave]
      have harg : (n : ℝ) * Real.pi / L * (L / (2 * n)) = Real.pi / 2 := by
        field_simp
      rw [harg, Real.sin_pi_div_two, mul_one]
      positivity

/-- Uniqueness for the harmonic oscillator equation `f'' = -k² f` with `f 0 = 0`:
any such solution is `f x = (f'(0)/k) sin (k x)`. -/
lemma eq_sin_of_hasDerivAt {k : ℝ} (hk : 0 < k) {f f' f'' : ℝ → ℝ}
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hd' : ∀ x : ℝ, HasDerivAt f' (f'' x) x)
    (heq : ∀ x : ℝ, f'' x = -(k ^ 2) * f x) (h0 : f 0 = 0) :
    ∀ x : ℝ, f x = (f' 0 / k) * Real.sin (k * x) := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  set A : ℝ := f' 0 / k with hA
  set g : ℝ → ℝ := fun x => f x - A * Real.sin (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - A * k * Real.cos (k * x) with hg'
  set g'' : ℝ → ℝ := fun x => f'' x + A * k ^ 2 * Real.sin (k * x) with hg''
  have hkx : ∀ x : ℝ, HasDerivAt (fun y : ℝ => k * y) k x := by
    intro x; simpa using (hasDerivAt_id x).const_mul k
  have hdg : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_sin (k * x)).comp x (hkx x)).const_mul A
    exact ((hd x).sub h1).congr_deriv (by simp [hg']; ring)
  have hdg' : ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_cos (k * x)).comp x (hkx x)).const_mul (A * k)
    exact ((hd' x).sub h1).congr_deriv (by simp [hg'']; ring)
  have hgeq : ∀ x : ℝ, g'' x = -(k ^ 2) * g x := by
    intro x; simp only [hg'', hg, heq x]; ring
  set W : ℝ → ℝ := fun x => g' x ^ 2 + k ^ 2 * g x ^ 2 with hW
  have hdW : ∀ x : ℝ, HasDerivAt W 0 x := by
    intro x
    have h1 : HasDerivAt (fun y => g' y ^ 2) (2 * g' x * g'' x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hdg' x).pow 2
    have h2 : HasDerivAt (fun y => k ^ 2 * g y ^ 2) (k ^ 2 * (2 * g x * g' x)) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using ((hdg x).pow 2).const_mul (k ^ 2)
    refine (h1.add h2).congr_deriv ?_
    rw [hgeq x]; ring
  have hWconst : ∀ x : ℝ, W x = W 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hdW y).differentiableAt)
      (fun y => (hdW y).deriv) x 0
  have hW0 : W 0 = 0 := by
    have hg0 : g 0 = 0 := by simp [hg, h0]
    have hAk : A * k = f' 0 := by rw [hA]; field_simp
    have hg'0 : g' 0 = 0 := by simp [hg', hAk]
    simp [hW, hg0, hg'0]
  intro x
  have hx : g x = 0 := by
    have h := hWconst x
    rw [hW0] at h
    have hz : k ^ 2 * g x ^ 2 = 0 := by
      simp only [hW] at h; nlinarith [sq_nonneg (g x), sq_nonneg (g' x)]
    have hk2 : k ^ 2 ≠ 0 := by positivity
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hz).resolve_left hk2)
  simpa [hg, sub_eq_zero] using hx

/-- There is no bound state of nonpositive energy in the infinite square well. -/
lemma not_isBoxEigenstate_of_nonpos {hbar m L E : ℝ} {psi psi' psi'' : ℝ → ℝ}
    (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : E ≤ 0)
    (h : IsBoxEigenstate hbar m L E psi psi' psi'') : False := by
  obtain ⟨hd, hd', hs, h0, hLL, hnt⟩ := h
  have hb : (hbar : ℝ) ^ 2 ≠ 0 := by positivity
  have hm' : m ≠ 0 := ne_of_gt hm
  have hdiff : Differentiable ℝ psi := fun x => (hd x).differentiableAt
  have hdiff' : Differentiable ℝ psi' := fun x => (hd' x).differentiableAt
  set c : ℝ := -(2 * m * E / hbar ^ 2) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 2 * m * E / hbar ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  have heq : ∀ x : ℝ, psi'' x = c * psi x := by
    intro x
    have h := hs x
    rw [hc]
    field_simp at h ⊢
    linarith
  set g : ℝ → ℝ := fun x => psi x * psi' x with hg
  have hdg : ∀ x : ℝ, HasDerivAt g (psi' x ^ 2 + c * psi x ^ 2) x := by
    intro x
    refine ((hd x).mul (hd' x)).congr_deriv ?_
    rw [heq x]; ring
  have hmono : Monotone g :=
    monotone_of_deriv_nonneg (fun x => (hdg x).differentiableAt)
      (fun x => by rw [(hdg x).deriv]; positivity)
  have hgz : ∀ x ∈ Set.Ioo (0 : ℝ) L, g x = 0 := by
    intro x hx
    have h1 : g 0 ≤ g x := hmono hx.1.le
    have h2 : g x ≤ g L := hmono hx.2.le
    have h3 : g 0 = 0 := by simp [hg, h0]
    have h4 : g L = 0 := by simp [hg, hLL]
    linarith
  have hpsi'z : Set.EqOn psi' 0 (Set.Ioo (0 : ℝ) L) := by
    intro x hx
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] g := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hgz y hy).symm
    have hd0 : HasDerivAt g 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev.symm
    have huniq := (hdg x).unique hd0
    have hnn : 0 ≤ c * psi x ^ 2 := by positivity
    have hz : psi' x ^ 2 = 0 := by nlinarith [sq_nonneg (psi' x)]
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  have hIcc : Set.EqOn psi' 0 (Set.Icc (0 : ℝ) L) := by
    have := hpsi'z.closure hdiff'.continuous continuous_const
    rwa [closure_Ioo (ne_of_lt hL)] at this
  have hconstpsi : ∀ x ∈ Set.Icc (0 : ℝ) L, psi x = psi 0 := by
    refine constant_of_has_deriv_right_zero hdiff.continuous.continuousOn ?_
    intro x hx
    have hzz : psi' x = 0 := hIcc (Set.mem_Icc_of_Ico hx)
    have h2 := (hd x).hasDerivWithinAt (s := Set.Ici x)
    rwa [hzz] at h2
  obtain ⟨x, hx, hne⟩ := hnt
  exact hne (by rw [hconstpsi x hx, h0])

/-- **Quantization.** Every bound state energy of the infinite square well is one of the
`E_n = n²π²ℏ²/(2mL²)` with `n ≥ 1`. -/
theorem exists_eq_boxEnergy {hbar m L E : ℝ} {psi psi' psi'' : ℝ → ℝ}
    (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L)
    (h : IsBoxEigenstate hbar m L E psi psi' psi'') :
    ∃ n : ℕ, 1 ≤ n ∧ E = boxEnergy hbar m L n := by
  rcases le_or_gt E 0 with hEle | hEpos
  · exact absurd h (fun h' => not_isBoxEigenstate_of_nonpos hhbar hm hL hEle h')
  obtain ⟨hd, hd', hs, h0, hLL, hnt⟩ := h
  have hb : (hbar : ℝ) ^ 2 ≠ 0 := by positivity
  have hm' : m ≠ 0 := ne_of_gt hm
  set k : ℝ := Real.sqrt (2 * m * E) / hbar with hkdef
  have hk : 0 < k := by
    rw [hkdef]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) hhbar
  have hk2 : k ^ 2 = 2 * m * E / hbar ^ 2 := by
    rw [hkdef, div_pow, Real.sq_sqrt (by positivity)]
  have heq : ∀ x : ℝ, psi'' x = -(k ^ 2) * psi x := by
    intro x
    have h := hs x
    rw [hk2]
    field_simp at h ⊢
    linarith
  have hsol := eq_sin_of_hasDerivAt hk hd hd' heq h0
  set A : ℝ := psi' 0 / k with hA
  have hA0 : A ≠ 0 := by
    intro hA0
    obtain ⟨x, hx, hne⟩ := hnt
    exact hne (by rw [hsol x, hA0, zero_mul])
  have hsinL : Real.sin (k * L) = 0 := by
    have hL0 := hsol L
    rw [hLL] at hL0
    exact (mul_eq_zero.mp hL0.symm).resolve_left hA0
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsinL
  have hjpos : 0 < j := by
    have hkl : 0 < k * L := mul_pos hk hL
    have h1 : 0 < (j : ℝ) * Real.pi := by rw [hj]; exact hkl
    have h2 : 0 < (j : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast h2
  refine ⟨j.toNat, by omega, ?_⟩
  have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    have h := Int.toNat_of_nonneg hjpos.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  rw [boxEnergy, hcast]
  have hkL : k = (j : ℝ) * Real.pi / L := by
    field_simp
    linarith [hj]
  have hEk : E = hbar ^ 2 * k ^ 2 / (2 * m) := by
    rw [hk2]; field_simp
  rw [hEk, hkL]
  field_simp

/-- **Particle in a box.** The set of bound-state energies of a particle of mass `m` in an
infinite square well of width `L` is exactly `{ n²π²ℏ²/(2mL²) | n ≥ 1 }`. -/
theorem particle_in_box {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    {E : ℝ | ∃ psi psi' psi'' : ℝ → ℝ, IsBoxEigenstate hbar m L E psi psi' psi''} =
      {E : ℝ | ∃ n : ℕ, 1 ≤ n ∧ E = boxEnergy hbar m L n} := by
  ext E
  constructor
  · rintro ⟨psi, psi', psi'', h⟩
    exact exists_eq_boxEnergy hhbar hm hL h
  · rintro ⟨n, hn, rfl⟩
    exact ⟨_, _, _, isBoxEigenstate_boxWave hm hL hn⟩

end QPhys

