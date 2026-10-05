import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Phys

/-- `psi` is a (twice differentiable) solution of the time-independent one-dimensional
Schrödinger equation with potential `V` and energy `E`, in units where `ħ² / 2m = 1`:
`-ψ'' + V ψ = E ψ`, i.e. `ψ'' = (V - E) ψ`. -/
structure IsSchrodingerSolution (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ) : Prop where
  differentiable : Differentiable ℝ psi
  differentiable_deriv : Differentiable ℝ (deriv psi)
  eqn : ∀ x : ℝ, deriv (deriv psi) x = (V x - E) * psi x

/-- If the potential is `a`-periodic, then translating a solution of the Schrödinger equation
by `a` gives again a solution with the same energy. -/
theorem schrodinger_shift {V : ℝ → ℂ} {E : ℂ} {psi : ℝ → ℂ} {a : ℝ}
    (hVper : ∀ x, V (x + a) = V x) (h : IsSchrodingerSolution V E psi) :
    IsSchrodingerSolution V E (fun x => psi (x + a)) := by
  have hd : (deriv fun x : ℝ => psi (x + a)) = fun x : ℝ => deriv psi (x + a) :=
    funext fun y => deriv_comp_add_const psi a y
  refine ⟨fun x => (h.differentiable (x + a)).comp x ((differentiable_id.add_const a) x), ?_, ?_⟩
  · rw [hd]
    exact fun x => (h.differentiable_deriv (x + a)).comp x ((differentiable_id.add_const a) x)
  · intro x
    rw [hd, deriv_comp_add_const (fun y => deriv psi y) a x, h.eqn (x + a), hVper x]

/-- A translation eigenvalue of a bounded function that does not vanish identically has
modulus one. -/
theorem translation_eigenvalue_norm_one {psi : ℝ → ℂ} {a : ℝ} {lam : ℂ} {M : ℝ} {x₀ : ℝ}
    (hlam : ∀ x, psi (x + a) = lam * psi x) (hbdd : ∀ x, ‖psi x‖ ≤ M)
    (hne : psi x₀ ≠ 0) : ‖lam‖ = 1 := by
  -- forward iteration of the translation
  have hfwd : ∀ n : ℕ, psi (x₀ + n * a) = lam ^ n * psi x₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : psi (x₀ + (n : ℝ) * a + a) = lam * psi (x₀ + (n : ℝ) * a) :=
          hlam (x₀ + (n : ℝ) * a)
        have hx : x₀ + ((n : ℕ) + 1 : ℕ) * a = x₀ + (n : ℝ) * a + a := by
          push_cast; ring
        rw [hx, hstep, ih]
        ring
  -- backward iteration of the translation
  have hbwd : ∀ n : ℕ, psi x₀ = lam ^ n * psi (x₀ - n * a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep :
            psi (x₀ - ((n : ℕ) + 1 : ℕ) * a + a) = lam * psi (x₀ - ((n : ℕ) + 1 : ℕ) * a) :=
          hlam _
        have hx : x₀ - ((n : ℕ) + 1 : ℕ) * a + a = x₀ - (n : ℝ) * a := by
          push_cast; ring
        rw [hx] at hstep
        rw [ih, hstep]
        push_cast
        ring
  have hpos : 0 < ‖psi x₀‖ := norm_pos_iff.mpr hne
  -- `‖lam‖ ≤ 1`, else `psi` blows up as `x → +∞`
  have hle : ‖lam‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖psi x₀‖) hgt
    have h1 : ‖lam‖ ^ n * ‖psi x₀‖ ≤ M := by
      have := hbdd (x₀ + n * a)
      rwa [hfwd n, norm_mul, norm_pow] at this
    have h2 : M / ‖psi x₀‖ * ‖psi x₀‖ < ‖lam‖ ^ n * ‖psi x₀‖ := mul_lt_mul_of_pos_right hn hpos
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    linarith
  -- `1 ≤ ‖lam‖`, else `psi` blows up as `x → -∞`
  have hge : 1 ≤ ‖lam‖ := by
    by_contra hlt
    push_neg at hlt
    have hnn : 0 ≤ ‖lam‖ := norm_nonneg _
    have htend : Filter.Tendsto (fun n : ℕ => ‖lam‖ ^ n * M) Filter.atTop (nhds (0 * M)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt).mul_const M
    rw [zero_mul] at htend
    have hbound : ∀ n : ℕ, ‖psi x₀‖ ≤ ‖lam‖ ^ n * M := by
      intro n
      have h1 : ‖psi x₀‖ = ‖lam‖ ^ n * ‖psi (x₀ - n * a)‖ := by
        rw [hbwd n, norm_mul, norm_pow]
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hbdd _) (pow_nonneg hnn n)
    have : ‖psi x₀‖ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds htend hbound
    linarith
  linarith

/-- **Bloch form.** If `psi` is an eigenvector of the translation-by-`a` operator with an
eigenvalue of modulus one, then `psi x = e^{i k x} * u x` with `u` an `a`-periodic function. -/
theorem bloch_form_of_translation_eigenvalue {psi : ℝ → ℂ} {a : ℝ} (ha : a ≠ 0) {lam : ℂ}
    (hnorm : ‖lam‖ = 1) (hlam : ∀ x, psi (x + a) = lam * psi x) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * (k * x)) * u x := by
  obtain ⟨θ, hlamexp⟩ : ∃ θ : ℝ, lam = Complex.exp (θ * Complex.I) := by
    refine ⟨Complex.arg lam, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I lam
    rw [hnorm] at h
    simpa using h.symm
  refine ⟨θ / a, fun x => Complex.exp (-(Complex.I * ((θ / a : ℝ) * x))) * psi x, ?_, ?_⟩
  · intro x
    simp only
    rw [hlam x, hlamexp]
    have hka : ((θ / a : ℝ) : ℂ) * ((a : ℝ) : ℂ) = (θ : ℂ) := by
      have hac : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
      push_cast
      field_simp
    have hexp : -(Complex.I * (((θ / a : ℝ) : ℂ) * ((x + a : ℝ) : ℂ)))
        = -(Complex.I * (((θ / a : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
          - ((θ / a : ℝ) : ℂ) * ((a : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, hka, Complex.exp_sub]
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  · intro x
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**
Let `V` be a potential with period `a > 0`, and let `psi` be a bounded eigenstate of the
corresponding Hamiltonian `H = -d²/dx² + V` with energy `E`, not identically zero, and assume
the bounded eigenspace at energy `E` is nondegenerate (one dimensional).  Then `psi` is a Bloch
wave: there exist a real wave number `k` and an `a`-periodic function `u` such that
`psi x = e^{i k x} * u x` for all `x`. -/
theorem bloch_theorem {V : ℝ → ℂ} {E : ℂ} {psi : ℝ → ℂ} {a : ℝ} {M : ℝ} {x₀ : ℝ}
    (ha : 0 < a) (hVper : ∀ x, V (x + a) = V x)
    (hSchr : IsSchrodingerSolution V E psi)
    (hbdd : ∀ x, ‖psi x‖ ≤ M) (hne : psi x₀ ≠ 0)
    (hnondeg : ∀ phi : ℝ → ℂ, IsSchrodingerSolution V E phi → (∃ N : ℝ, ∀ x, ‖phi x‖ ≤ N) →
      ∃ c : ℂ, ∀ x, phi x = c * psi x) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * (k * x)) * u x := by
  -- The translate of `psi` is a bounded solution with the same energy, hence proportional to
  -- `psi`; that is, `psi` is an eigenvector of the translation operator.
  obtain ⟨lam, hlam⟩ :=
    hnondeg (fun x => psi (x + a)) (schrodinger_shift hVper hSchr) ⟨M, fun x => hbdd (x + a)⟩
  have hnorm : ‖lam‖ = 1 := translation_eigenvalue_norm_one hlam hbdd hne
  exact bloch_form_of_translation_eigenvalue (ne_of_gt ha) hnorm hlam

/-! ### The hypotheses of `bloch_theorem` are satisfiable

We check that the hypotheses of `bloch_theorem` are not contradictory, by exhibiting the free
particle (`V = 0`) at zero energy, whose bounded eigenspace consists exactly of the constants. -/

/-- A bounded function on `ℝ` whose second derivative vanishes identically is constant. -/
theorem const_of_deriv_deriv_eq_zero {phi : ℝ → ℂ} (h1 : Differentiable ℝ phi)
    (h2 : Differentiable ℝ (deriv phi)) (h3 : ∀ x, deriv (deriv phi) x = 0)
    {N : ℝ} (hb : ∀ x, ‖phi x‖ ≤ N) : ∀ x, phi x = phi 0 := by
  set c : ℂ := deriv phi 0 with hc
  have hderiv : ∀ x, deriv phi x = c := fun x => is_const_of_deriv_eq_zero h2 h3 x 0
  -- `phi x - c * x` has vanishing derivative, hence is constant
  have hofReal : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 x := by
    intro x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hg : ∀ x : ℝ, HasDerivAt (fun t : ℝ => phi t - c * (t : ℂ)) 0 x := by
    intro x
    have hp : HasDerivAt phi c x := by
      have := (h1 x).hasDerivAt
      rwa [hderiv x] at this
    have hl : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using (hofReal x).const_mul c
    simpa using hp.sub hl
  have hgc : ∀ x : ℝ, phi x - c * (x : ℂ) = phi 0 - c * ((0 : ℝ) : ℂ) :=
    fun x => is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
      (fun y => (hg y).deriv) x 0
  have haffine : ∀ x : ℝ, phi x = phi 0 + c * (x : ℂ) := by
    intro x
    have := hgc x
    simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
    linear_combination this
  -- boundedness forces the slope `c` to vanish
  have hN : 0 ≤ N := le_trans (norm_nonneg _) (hb 0)
  have hc0 : c = 0 := by
    by_contra hcne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    set t : ℝ := (2 * N + 1) / ‖c‖ with ht
    have htnn : 0 ≤ t := by positivity
    have h1' : ‖c * (t : ℂ)‖ = 2 * N + 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn, ht]
      field_simp
    have h2' : ‖c * (t : ℂ)‖ ≤ 2 * N := by
      have : c * (t : ℂ) = phi t - phi 0 := by
        rw [haffine t]; ring
      rw [this]
      calc ‖phi t - phi 0‖ ≤ ‖phi t‖ + ‖phi 0‖ := norm_sub_le _ _
        _ ≤ N + N := add_le_add (hb t) (hb 0)
        _ = 2 * N := by ring
    linarith
  intro x
  rw [haffine x, hc0]
  ring

/-- The hypotheses of `bloch_theorem` are consistent: they hold for the free particle at zero
energy with the constant eigenstate, on any lattice of period `a = 1`. -/
theorem bloch_theorem_hypotheses_satisfiable :
    ∃ (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ) (a M x₀ : ℝ),
      0 < a ∧ (∀ x, V (x + a) = V x) ∧ IsSchrodingerSolution V E psi ∧
      (∀ x, ‖psi x‖ ≤ M) ∧ psi x₀ ≠ 0 ∧
      (∀ phi : ℝ → ℂ, IsSchrodingerSolution V E phi → (∃ N : ℝ, ∀ x, ‖phi x‖ ≤ N) →
        ∃ c : ℂ, ∀ x, phi x = c * psi x) := by
  refine ⟨fun _ => 0, 0, fun _ => 1, 1, 1, 0, one_pos, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨differentiable_const 1, ?_, ?_⟩
    · simp
    · intro x
      simp
  · intro x; simp
  · simp
  · intro phi hphi hbdd
    obtain ⟨N, hN⟩ := hbdd
    have h3 : ∀ x, deriv (deriv phi) x = 0 := by
      intro x
      simpa using hphi.eqn x
    have := const_of_deriv_deriv_eq_zero hphi.differentiable hphi.differentiable_deriv h3 hN
    exact ⟨phi 0, fun x => by rw [this x]; ring⟩

end Phys

#print axioms Phys.bloch_theorem
#print axioms Phys.bloch_theorem_hypotheses_satisfiable

