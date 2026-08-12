import RequestProject.LSM.Ground

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line, because Lean 4 requires the
`import` commands to be the very first commands of a file.)

## Statement

A half-integer-spin translation-invariant chain is gapless or degenerate.

We formalise this for the spin-`1/2` XY chain with `L` sites and periodic boundary
conditions, whose Hilbert space is `Phys.Chain L = EuclideanSpace ℂ (Fin L → Bool)` and
whose Hamiltonian `Phys.hamOp L` is the translation invariant nearest neighbour exchange
Hamiltonian `-∑ⱼ (S⁺ⱼ S⁻ⱼ₊₁ + S⁻ⱼ S⁺ⱼ₊₁)`.

The theorem `Phys.lieb_schultz_mattis` states the LSM dichotomy in finite volume: either
the ground state is degenerate (there are two orthogonal ground states), or there is a
state orthogonal to the ground state whose energy exceeds the ground state energy by at
most `2π²/L`.  Since this bound tends to `0` as `L → ∞`
(`Phys.lieb_schultz_mattis_bound_tendsto_zero`), the chain is gapless or degenerate.

The proof is the Lieb-Schultz-Mattis twist argument: the twist operator
`U = exp (i (2π/L) ∑ⱼ j Sᶻⱼ)` produces a variational state of energy `cos (2π/L) E₀`,
and it satisfies the *anomalous* commutation relation `T U = -e^{-i(2π/L)Sᶻ} U T` with the
translation `T`.  The crucial sign `-1` is `exp (2π i Sᶻ)` for the half-integer spin `Sᶻ`
carried by the site that wraps around the chain; it forces the twisted state to be
orthogonal to any non-degenerate (hence translation invariant) ground state.
-/

namespace Phys

open scoped ComplexConjugate

instance instNontrivialChain (L : ℕ) : Nontrivial (Chain L) := by
  have : Nonempty (Conf L) := ⟨fun _ => true⟩
  infer_instance

/-- **Lieb-Schultz-Mattis theorem** for the translation invariant spin-`1/2` (half-integer
spin) XY chain with `L ≥ 2` sites and periodic boundary conditions:

either the ground state is degenerate, or there is an excited state whose energy lies
within `2π²/L` of the ground state energy.  As `L → ∞` this bound tends to zero: the chain
is gapless or degenerate. -/
theorem lieb_schultz_mattis (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    Degenerate (hamOp L) ∨ HasLowExcitation (hamOp L) (2 * Real.pi ^ 2 / L) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_isGroundState (hamOp L)
  by_cases hdeg : ∃ φ : Chain L, IsGroundState (hamOp L) φ ∧ ∀ a : ℂ, φ ≠ a • ψ₀
  · obtain ⟨φ, hφ, h⟩ := hdeg
    exact Or.inl (degenerate_of_not_proportional hamOp_isSelfAdjoint hψ₀ hφ h)
  · right
    have hnd0 : ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ₀ := by
      intro φ hφ
      by_contra hcon
      push_neg at hcon
      exact hdeg ⟨φ, hφ, hcon⟩
    obtain ⟨ψ, hψ, hreal, hnd⟩ := exists_real_groundState hψ₀ hnd0
    obtain ⟨m, hm, hmex⟩ := groundState_sector hψ hnd
    exact lsm_core hψ hnd transOp_inner transOp_comm_hamOp twistOp_norm
      (transOp_twistOp_anomaly hL ψ hm)
      (anomaly_factor_ne_one hL (sector_abs_lt hL hψ hnd hm hmex))
      (energy_twist_le hL hψ hreal)

/-- The Lieb-Schultz-Mattis bound `2π²/L` tends to `0` as the length of the chain tends to
infinity: in the thermodynamic limit the chain is gapless or degenerate. -/
theorem lieb_schultz_mattis_bound_tendsto_zero :
    Filter.Tendsto (fun L : ℕ => 2 * Real.pi ^ 2 / L) Filter.atTop (nhds 0) := by
  simpa using
    (tendsto_const_nhds (x := 2 * Real.pi ^ 2) (f := Filter.atTop (α := ℕ))).div_atTop
      tendsto_natCast_atTop_atTop

/-- Monotonicity of the excitation bound. -/
theorem HasLowExcitation.mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : E →L[ℂ] E} {ε ε' : ℝ} (h : HasLowExcitation H ε) (hle : ε ≤ ε') :
    HasLowExcitation H ε' := by
  obtain ⟨ψ, φ, h1, h2, h3, h4⟩ := h
  exact ⟨ψ, φ, h1, h2, h3, h4.trans (by linarith)⟩

/-- The Lieb-Schultz-Mattis dichotomy in the thermodynamic limit: for every `ε > 0`, all
sufficiently long chains are either degenerate or have an excitation of energy at most
`ε`. -/
theorem lieb_schultz_mattis_gapless_or_degenerate {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (L : ℕ) (_ : NeZero L), N ≤ L →
      Degenerate (hamOp L) ∨ HasLowExcitation (hamOp L) ε := by
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1
    ((Metric.tendsto_nhds.1 lieb_schultz_mattis_bound_tendsto_zero) ε hε))
  refine ⟨max N 2, fun L _ hL => ?_⟩
  have h2 : 2 ≤ L := le_trans (le_max_right N 2) hL
  rcases lieb_schultz_mattis L h2 with h | h
  · exact Or.inl h
  · refine Or.inr (h.mono ?_)
    have := hN L (le_trans (le_max_left N 2) hL)
    rw [Real.dist_eq, sub_zero] at this
    exact le_of_lt (lt_of_abs_lt this)

end Phys

import RequestProject.LSM.Twist

/-!
# The energy of the twisted state

For a state with real coordinates the twist multiplies each bond contribution — and hence
the energy — by `cos (2π/L)`: the hopping term picks up the phase `exp (±i 2π/L)` on every
bond, and the two orientations of a bond are exchanged by the involution that swaps the two
spins of the bond.
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
lemma conj_twist_mul (σ : Conf L) : conj (twist L σ) * twist L σ = 1 := by
  rw [mul_comm, Complex.mul_conj]
  have h := norm_twist (L := L) σ
  rw [Complex.normSq_eq_norm_sq, h]
  norm_num

omit [NeZero L] in
lemma conj_exp_I_real (t : ℝ) :
    conj (Complex.exp (Complex.I * (t : ℂ))) = Complex.exp (-(Complex.I * (t : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

omit [NeZero L] in
lemma exp_add_exp_neg (t : ℝ) :
    Complex.exp (-(Complex.I * (t : ℂ))) + Complex.exp (Complex.I * (t : ℂ))
      = 2 * ((Real.cos t : ℝ) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  ring_nf

lemma spin_diff_eq (b c : Bool) (h : b ≠ c) : spin b - spin c = 1 ∨ spin b - spin c = -1 := by
  cases b <;> cases c <;> simp [spin] at h ⊢ <;> norm_num

/-- The matrix element of the hopping term between twisted states carries the phase
`exp (-i α (Sᶻⱼ - Sᶻⱼ₊₁))`. -/
lemma twisted_term (hL : 2 ≤ L) {x : Chain L} (hx : IsRealVec x) (j : Fin L) (σ : Conf L) :
    conj ((twistOp L x) (swapConf L j σ)) * (twistOp L x) σ
      = Complex.exp (-(Complex.I *
          ((twistAngle L * (spin (σ j) - spin (σ (j + 1))) : ℝ) : ℂ)))
        * (x (swapConf L j σ) * x σ) := by
  rw [twistOp_apply, twistOp_apply, twist_swapConf hL, map_mul, map_mul,
    ← conj_exp_I_real (twistAngle L * (spin (σ j) - spin (σ (j + 1))))]
  rw [show (Complex.I * ((twistAngle L * (spin (σ j) - spin (σ (j + 1))) : ℝ) : ℂ))
      = Complex.I * (twistAngle L : ℂ) * ((spin (σ j) - spin (σ (j + 1)) : ℝ) : ℂ) by
        push_cast; ring]
  rw [hx]
  calc conj (Complex.exp (Complex.I * (twistAngle L : ℂ)
          * ((spin (σ j) - spin (σ (j + 1)) : ℝ) : ℂ)))
        * conj (twist L σ) * (x (swapConf L j σ)) * (twist L σ * x σ)
      = conj (Complex.exp (Complex.I * (twistAngle L : ℂ)
          * ((spin (σ j) - spin (σ (j + 1)) : ℝ) : ℂ)))
        * (conj (twist L σ) * twist L σ) * (x (swapConf L j σ) * x σ) := by ring
    _ = _ := by rw [conj_twist_mul]; ring

lemma bondSum_twist (hL : 2 ≤ L) {x : Chain L} (hx : IsRealVec x) (j : Fin L) :
    bondSum (twistOp L x) j = (Real.cos (twistAngle L) : ℂ) * bondSum x j := by
  set a : ℝ := twistAngle L with ha
  set F : Conf L → ℂ := fun σ =>
    if σ j ≠ σ (j + 1) then
      Complex.exp (-(Complex.I * ((a * (spin (σ j) - spin (σ (j + 1))) : ℝ) : ℂ)))
        * (x (swapConf L j σ) * x σ) else 0 with hFdef
  set g : Conf L → ℂ := fun σ => if σ j ≠ σ (j + 1) then x (swapConf L j σ) * x σ else 0 with hgdef
  have hbx : bondSum x j = ∑ σ : Conf L, g σ := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hgdef]
    split
    · rw [hx]
    · rfl
  have hbtx : bondSum (twistOp L x) j = ∑ σ : Conf L, F σ := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hFdef]
    split
    · exact twisted_term hL hx j σ
    · rfl
  have hswapsum : ∑ σ : Conf L, F σ = ∑ σ : Conf L, F (swapConf L j σ) :=
    (Fintype.sum_equiv (swapEquiv j) _ _ (fun _ => rfl)).symm
  have hpair : ∀ σ : Conf L, F σ + F (swapConf L j σ) = 2 * ((Real.cos a : ℝ) : ℂ) * g σ := by
    intro σ
    by_cases hc : σ j ≠ σ (j + 1)
    · have hc' : (swapConf L j σ) j ≠ (swapConf L j σ) (j + 1) := swapConf_ne j hc
      have hd : spin ((swapConf L j σ) j) - spin ((swapConf L j σ) (j + 1))
          = -(spin (σ j) - spin (σ (j + 1))) := by
        rw [swapConf_apply_self, swapConf_apply_succ]; ring
      simp only [hFdef, hgdef, if_pos hc, if_pos hc', swapConf_involutive, hd]
      rcases spin_diff_eq _ _ hc with h1 | h1
      · rw [h1]
        rw [show ((a * -(1 : ℝ) : ℝ) : ℂ) = -((a : ℝ) : ℂ) by push_cast; ring,
            show ((a * (1 : ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) by push_cast; ring]
        rw [show -(Complex.I * -((a : ℝ) : ℂ)) = Complex.I * ((a : ℝ) : ℂ) by ring]
        calc Complex.exp (-(Complex.I * ((a : ℝ) : ℂ))) * (x (swapConf L j σ) * x σ)
              + Complex.exp (Complex.I * ((a : ℝ) : ℂ)) * (x σ * x (swapConf L j σ))
            = (Complex.exp (-(Complex.I * ((a : ℝ) : ℂ)))
                + Complex.exp (Complex.I * ((a : ℝ) : ℂ))) * (x (swapConf L j σ) * x σ) := by ring
          _ = _ := by rw [exp_add_exp_neg]
      · rw [h1]
        rw [show ((a * -(-1 : ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) by push_cast; ring,
            show ((a * (-1 : ℝ) : ℝ) : ℂ) = -((a : ℝ) : ℂ) by push_cast; ring]
        rw [show -(Complex.I * -((a : ℝ) : ℂ)) = Complex.I * ((a : ℝ) : ℂ) by ring]
        calc Complex.exp (Complex.I * ((a : ℝ) : ℂ)) * (x (swapConf L j σ) * x σ)
              + Complex.exp (-(Complex.I * ((a : ℝ) : ℂ))) * (x σ * x (swapConf L j σ))
            = (Complex.exp (-(Complex.I * ((a : ℝ) : ℂ)))
                + Complex.exp (Complex.I * ((a : ℝ) : ℂ))) * (x (swapConf L j σ) * x σ) := by ring
          _ = _ := by rw [exp_add_exp_neg]
    · have hc' : ¬((swapConf L j σ) j ≠ (swapConf L j σ) (j + 1)) := by
        intro hh
        refine hc ?_
        have h4 := swapConf_ne j hh
        rw [swapConf_involutive] at h4
        exact h4
      simp only [hFdef, hgdef, if_neg hc, if_neg hc']
      ring
  have h2 : (2 : ℂ) * ∑ σ : Conf L, F σ = 2 * ((Real.cos a : ℝ) : ℂ) * ∑ σ : Conf L, g σ := by
    calc (2 : ℂ) * ∑ σ : Conf L, F σ = (∑ σ : Conf L, F σ) + ∑ σ : Conf L, F (swapConf L j σ) := by
          rw [← hswapsum]; ring
      _ = ∑ σ : Conf L, (F σ + F (swapConf L j σ)) := by rw [Finset.sum_add_distrib]
      _ = ∑ σ : Conf L, 2 * ((Real.cos a : ℝ) : ℂ) * g σ := Finset.sum_congr rfl fun σ _ => hpair σ
      _ = 2 * ((Real.cos a : ℝ) : ℂ) * ∑ σ : Conf L, g σ := by rw [Finset.mul_sum]
  rw [hbtx, hbx]
  field_simp at h2 ⊢
  linear_combination h2

/-- **Energy of the twisted state.**  For a state with real coordinates the twist
multiplies the energy by `cos (2π/L)`. -/
lemma energy_twistOp (hL : 2 ≤ L) {x : Chain L} (hx : IsRealVec x) :
    energy (hamOp L) (twistOp L x) = Real.cos (twistAngle L) * energy (hamOp L) x := by
  rw [energy_eq_bondSums, energy_eq_bondSums]
  have h : ∀ j : Fin L, (bondSum (twistOp L x) j).re
      = Real.cos (twistAngle L) * (bondSum x j).re := by
    intro j
    rw [bondSum_twist hL hx, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), ← Finset.mul_sum]
  ring

end Phys

import RequestProject.LSM.Ops

/-!
# The Lieb-Schultz-Mattis twist and its anomalous commutation with translations

The twist operator is the diagonal unitary with phase `exp (i (2π/L) ∑ⱼ j Sᶻⱼ)`.  Its
essential property is the anomalous commutation relation with the translation operator:
translating the twist phase produces an extra factor `-exp(-i (2π/L) Sᶻ_tot)`.  The
sign `-1` is `exp (2π i Sᶻ)` for the *half-integer* spin `Sᶻ = ±1/2` of the site that
wraps around the chain; it is the source of the Lieb-Schultz-Mattis theorem.
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
lemma twistAngle_mul (hL : 2 ≤ L) : twistAngle L * L = 2 * Real.pi := by
  have hLne : (L : ℝ) ≠ 0 := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this.ne'
  unfold twistAngle
  field_simp

/-! ### The twist is a phase -/

omit [NeZero L] in
lemma norm_twist (σ : Conf L) : ‖twist L σ‖ = 1 := by
  rw [twist, Complex.norm_exp]
  simp

omit [NeZero L] in
lemma twistOp_norm (x : Chain L) : ‖twistOp L x‖ = ‖x‖ := by
  have h : ∀ σ : Conf L, ‖(twistOp L x) σ‖ = ‖x σ‖ := by
    intro σ
    rw [twistOp_apply, norm_mul, norm_twist, one_mul]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by rw [h σ]

/-! ### Elementary `Fin L` arithmetic -/

lemma val_succ (hL : 2 ≤ L) (j : Fin L) :
    ((j + 1 : Fin L) : ℕ) = if (j : ℕ) + 1 = L then 0 else (j : ℕ) + 1 := by
  rw [Fin.val_add, Fin.val_one']
  have h1 : (1 : ℕ) % L = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have hj := j.isLt
  split
  · next h => rw [h, Nat.mod_self]
  · next h => exact Nat.mod_eq_of_lt (by omega)

lemma succ_ne_self (hL : 2 ≤ L) (j : Fin L) : j + 1 ≠ j := by
  intro h
  have h2 : ((j + 1 : Fin L) : ℕ) = (j : ℕ) := by rw [h]
  rw [val_succ hL] at h2
  have hj := j.isLt
  split at h2 <;> omega

lemma val_pred (hL : 2 ≤ L) (i : Fin L) :
    ((i - 1 : Fin L) : ℕ) = if (i : ℕ) = 0 then L - 1 else (i : ℕ) - 1 := by
  have h1 : ((1 : Fin L) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.sub_def, h1]
  have hi := i.isLt
  show (L - 1 + (i : ℕ)) % L = _
  split
  · next h => rw [h]; simp [Nat.mod_eq_of_lt (show L - 1 < L by omega)]
  · next h =>
      have h2 : L - 1 + (i : ℕ) = L + ((i : ℕ) - 1) := by omega
      rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! ### The effect of a bond exchange on the twist phase -/

lemma spin_diff_int (b c : Bool) : ∃ n : ℤ, spin b - spin c = (n : ℝ) := by
  cases b <;> cases c
  · exact ⟨0, by simp [spin]⟩
  · exact ⟨-1, by simp [spin]; norm_num⟩
  · exact ⟨1, by simp [spin]; norm_num⟩
  · exact ⟨0, by simp [spin]⟩

lemma weight_swap (j : Fin L) (σ : Conf L) :
    (∑ k : Fin L, (k : ℝ) * spin (swapConf L j σ k))
      = ∑ k : Fin L, ((Equiv.swap j (j + 1) k : Fin L) : ℝ) * spin (σ k) := by
  refine Fintype.sum_equiv (Equiv.swap j (j + 1)) _ _ (fun k => ?_)
  simp [swapConf]

lemma weight_diff (hL : 2 ≤ L) (j : Fin L) (σ : Conf L) :
    (∑ k : Fin L, (k : ℝ) * spin (swapConf L j σ k)) - (∑ k : Fin L, (k : ℝ) * spin (σ k))
      = (((j + 1 : Fin L) : ℝ) - (j : ℝ)) * (spin (σ j) - spin (σ (j + 1))) := by
  rw [weight_swap, ← Finset.sum_sub_distrib]
  have hne : j ≠ j + 1 := (succ_ne_self hL j).symm
  have hsub : ∑ k : Fin L, (((Equiv.swap j (j + 1) k : Fin L) : ℝ) - (k : ℝ)) * spin (σ k)
      = ∑ k ∈ ({j, j + 1} : Finset (Fin L)),
          (((Equiv.swap j (j + 1) k : Fin L) : ℝ) - (k : ℝ)) * spin (σ k) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2]
    ring
  calc ∑ k : Fin L, (((Equiv.swap j (j + 1) k : Fin L) : ℝ) * spin (σ k) - (k : ℝ) * spin (σ k))
      = ∑ k : Fin L, (((Equiv.swap j (j + 1) k : Fin L) : ℝ) - (k : ℝ)) * spin (σ k) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hsub, Finset.sum_pair hne, Equiv.swap_apply_left, Equiv.swap_apply_right]
        ring

omit [NeZero L] in
/-- A `2π`-periodicity lemma: multiplying the phase argument by `1 - L` does not change
the twist phase, because the spin difference is an integer. -/
lemma exp_twist_periodic (hL : 2 ≤ L) {t : ℝ} {n : ℤ} (ht : t = (n : ℝ)) {δ : ℝ}
    (hδ : δ = 1 - L) :
    Complex.exp (Complex.I * (twistAngle L : ℂ) * ((δ * t : ℝ) : ℂ))
      = Complex.exp (Complex.I * (twistAngle L : ℂ) * ((t : ℝ) : ℂ)) := by
  have hmul : ((twistAngle L * L : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    rw [twistAngle_mul hL]
  have h1 : ((δ * t : ℝ) : ℂ) = ((t : ℝ) : ℂ) - ((L : ℝ) : ℂ) * ((t : ℝ) : ℂ) := by
    rw [hδ]; push_cast; ring
  rw [h1, mul_sub, Complex.exp_sub]
  have h2 : Complex.I * (twistAngle L : ℂ) * (((L : ℝ) : ℂ) * ((t : ℝ) : ℂ))
      = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast at hmul ⊢
    rw [ht]
    push_cast
    calc Complex.I * (twistAngle L : ℂ) * ((L : ℂ) * (n : ℂ))
        = ((twistAngle L : ℂ) * (L : ℂ)) * ((n : ℂ) * Complex.I) := by ring
      _ = (2 * (Real.pi : ℂ)) * ((n : ℂ) * Complex.I) := by rw [hmul]
      _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- Exchanging the spins on a bond changes the twist phase by `exp (i α d)`, where
`d = Sᶻⱼ - Sᶻⱼ₊₁ ∈ {-1, 0, 1}`.  (The wrap-around bond gives the same answer because the
spins are half-integers, so that `d` is an integer and `exp (i α L d) = exp (2π i d) = 1`.) -/
lemma twist_swapConf (hL : 2 ≤ L) (j : Fin L) (σ : Conf L) :
    twist L (swapConf L j σ) =
      Complex.exp (Complex.I * (twistAngle L : ℂ) * ((spin (σ j) - spin (σ (j + 1)) : ℝ) : ℂ))
        * twist L σ := by
  set d : ℝ := spin (σ j) - spin (σ (j + 1)) with hd
  set δ : ℝ := ((j + 1 : Fin L) : ℝ) - (j : ℝ) with hδ
  have hw : (∑ k : Fin L, (k : ℝ) * spin (swapConf L j σ k))
      = (∑ k : Fin L, (k : ℝ) * spin (σ k)) + δ * d := by
    have h := weight_diff hL j σ
    rw [← hd, ← hδ] at h
    linarith
  have hfac : Complex.exp (Complex.I * (twistAngle L : ℂ) * ((δ * d : ℝ) : ℂ))
      = Complex.exp (Complex.I * (twistAngle L : ℂ) * ((d : ℝ) : ℂ)) := by
    have hj := j.isLt
    by_cases hwrap : (j : ℕ) + 1 = L
    · obtain ⟨n, hn⟩ := spin_diff_int (σ j) (σ (j + 1))
      refine exp_twist_periodic hL (t := d) (n := n) hn ?_
      have hjv : ((j : ℕ) : ℝ) = (L : ℝ) - 1 := by
        have h3 : ((j : ℕ) : ℝ) + 1 = (L : ℝ) := by exact_mod_cast congrArg (Nat.cast (R := ℝ)) hwrap
        linarith
      rw [hδ, val_succ hL, if_pos hwrap]
      push_cast
      rw [hjv]; ring
    · have hone : δ = 1 := by
        rw [hδ, val_succ hL, if_neg hwrap]
        push_cast
        ring
      rw [hone, one_mul]
  rw [twist, twist, hw]
  push_cast
  rw [mul_add, Complex.exp_add]
  rw [show (Complex.I * (twistAngle L : ℂ) * ((δ : ℂ) * (d : ℂ)))
      = Complex.I * (twistAngle L : ℂ) * (((δ * d : ℝ)) : ℂ) by push_cast; ring, hfac]
  ring

/-! ### Translating the twist: the anomaly -/

omit [NeZero L] in
/-- `exp (i α L Sᶻ) = exp (2π i Sᶻ) = -1` for a half-integer spin `Sᶻ = ±1/2`. -/
lemma exp_twist_saturated (hL : 2 ≤ L) (b : Bool) :
    Complex.exp (Complex.I * (twistAngle L : ℂ) * ((L : ℂ) * ((spin b : ℝ) : ℂ))) = -1 := by
  have hmul : ((twistAngle L * L : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by rw [twistAngle_mul hL]
  push_cast at hmul
  have key : Complex.I * (twistAngle L : ℂ) * ((L : ℂ) * ((spin b : ℝ) : ℂ))
      = ((twistAngle L : ℂ) * (L : ℂ)) * ((spin b : ℝ) : ℂ) * Complex.I := by ring
  rw [key, hmul]
  cases b
  · have h0 : ((spin false : ℝ) : ℂ) = -(1 / 2) := by simp [spin]
    rw [h0, show (2 * (Real.pi : ℂ)) * (-(1 / 2)) * Complex.I = -((Real.pi : ℂ) * Complex.I) by
      ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  · have h0 : ((spin true : ℝ) : ℂ) = 1 / 2 := by simp [spin]
    rw [h0, show (2 * (Real.pi : ℂ)) * (1 / 2) * Complex.I = ((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_pi_mul_I]

/-- The weight `∑ⱼ j Sᶻⱼ` after a translation: the wrap-around produces the term `L Sᶻ₀`. -/
lemma weight_shift (hL : 2 ≤ L) (σ : Conf L) :
    (∑ k : Fin L, (k : ℝ) * spin (shiftConf L σ k))
      = (∑ k : Fin L, (k : ℝ) * spin (σ k)) - totSpin σ + L * spin (σ 0) := by
  have h1 : (∑ k : Fin L, (k : ℝ) * spin (shiftConf L σ k))
      = ∑ i : Fin L, ((i - 1 : Fin L) : ℝ) * spin (σ i) := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : Fin L)) _ _ (fun k => ?_)
    simp [shiftConf]
  have h2 : ∀ i : Fin L, ((i - 1 : Fin L) : ℝ)
      = (i : ℝ) - 1 + (if i = 0 then (L : ℝ) else 0) := by
    intro i
    rw [val_pred hL]
    have hi := i.isLt
    by_cases h : (i : ℕ) = 0
    · have hi0 : i = 0 := by
        apply Fin.ext
        simpa [Fin.val_zero] using h
      rw [if_pos h, if_pos hi0, h]
      push_cast [Nat.cast_sub (show 1 ≤ L by omega)]
      ring
    · have hi0 : i ≠ 0 := by
        intro hh; exact h (by rw [hh]; simp)
      rw [if_neg h, if_neg hi0]
      push_cast [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
      ring
  rw [h1]
  simp only [h2, add_mul, sub_mul, one_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin L)]
  simp [totSpin]

/-- **The Lieb-Schultz-Mattis anomaly.**  Translating the twist phase produces the extra
factor `-exp (-i α Sᶻ_tot)`.  The sign `-1` is exactly `exp (2π i Sᶻ)` for a *half-integer*
spin `Sᶻ = ±1/2` on the site that wraps around the chain. -/
lemma twist_shiftConf (hL : 2 ≤ L) (σ : Conf L) :
    twist L (shiftConf L σ) =
      -(Complex.exp (-(Complex.I * (twistAngle L : ℂ) * (totSpin σ : ℂ)))) * twist L σ := by
  rw [twist, twist, weight_shift hL]
  push_cast
  set a : ℂ := (twistAngle L : ℂ)
  set S : ℂ := ∑ x : Fin L, (x : ℂ) * ((spin (σ x) : ℝ) : ℂ) with hS
  set T : ℂ := ((totSpin σ : ℝ) : ℂ)
  set P : ℂ := ((spin (σ 0) : ℝ) : ℂ)
  rw [show Complex.I * a * (S - T + (L : ℂ) * P)
      = (Complex.I * a * S) + (-(Complex.I * a * T)) + (Complex.I * a * ((L : ℂ) * P)) by ring]
  rw [Complex.exp_add, Complex.exp_add, exp_twist_saturated hL]
  ring

/-- The anomalous commutation relation between translation and twist, on a state living in
the magnetization sector `m`. -/
lemma transOp_twistOp_anomaly (hL : 2 ≤ L) {m : ℝ} (x : Chain L)
    (hx : ∀ σ, totSpin σ ≠ m → x σ = 0) :
    transOp L (twistOp L x) =
      (-(Complex.exp (-(Complex.I * (twistAngle L : ℂ) * (m : ℂ))))) • twistOp L (transOp L x) := by
  ext σ
  rw [transOp_apply, twistOp_apply, PiLp.smul_apply, twistOp_apply, transOp_apply,
    twist_shiftConf hL]
  by_cases hz : x (shiftConf L σ) = 0
  · rw [hz]; simp
  · have hts : totSpin σ = m := by
      by_contra hne
      exact hz (hx _ (by rwa [totSpin_shiftConf]))
    rw [hts]
    simp only [smul_eq_mul]
    ring

omit [NeZero L] in
/-- The anomaly factor is different from `1` as soon as the magnetization is not saturated. -/
lemma anomaly_factor_ne_one {m : ℝ} (hL : 2 ≤ L) (hm : |m| < L / 2) :
    (-(Complex.exp (-(Complex.I * (twistAngle L : ℂ) * (m : ℂ))))) ≠ 1 := by
  intro hcon
  have hexp : Complex.exp (-(Complex.I * ((twistAngle L * m : ℝ) : ℂ))) = -1 := by
    rw [show ((twistAngle L * m : ℝ) : ℂ) = (twistAngle L : ℂ) * (m : ℂ) by push_cast; ring]
    rw [show -(Complex.I * ((twistAngle L : ℂ) * (m : ℂ)))
        = -(Complex.I * (twistAngle L : ℂ) * (m : ℂ)) by ring]
    linear_combination -hcon
  set t : ℝ := twistAngle L * m with ht
  have hcos : Real.cos t = -1 := by
    have h1 : (Complex.exp (-(Complex.I * (t : ℂ)))).re = Real.cos t := by
      rw [show -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_re]
      exact Real.cos_neg t
    rw [hexp] at h1
    simpa using h1.symm
  have hLpos : (0 : ℝ) < L := by
    have h0 : (0 : ℕ) < L := by omega
    exact_mod_cast h0
  have hα : 0 < twistAngle L := by
    unfold twistAngle
    positivity
  have habs : |t| < Real.pi := by
    rw [ht, abs_mul, abs_of_pos hα]
    have h2 : twistAngle L * |m| < twistAngle L * ((L : ℝ) / 2) := mul_lt_mul_of_pos_left hm hα
    have h3 : twistAngle L * ((L : ℝ) / 2) = Real.pi := by
      unfold twistAngle
      field_simp
    linarith
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 hcos
  have hpi := Real.pi_pos
  rcases abs_lt.1 habs with ⟨h1, h2⟩
  rcases le_or_gt 0 (k : ℝ) with hkpos | hkneg
  · nlinarith
  · have hk1 : (k : ℝ) ≤ -1 := by
      have hkz : k < 0 := by exact_mod_cast hkneg
      have : k ≤ -1 := by omega
      exact_mod_cast this
    nlinarith

end Phys

import RequestProject.LSM.Abstract

/-!
# The spin-1/2 XY chain: definitions and basic properties

We realise a translation invariant chain of `L` half-integer (spin-1/2) sites with periodic
boundary conditions.  The Hilbert space is `Chain L = EuclideanSpace ℂ (Conf L)` where
`Conf L = Fin L → Bool` is the set of spin configurations.

The Hamiltonian is the nearest-neighbour XY (hopping) Hamiltonian
`H = -∑ⱼ (Sˣⱼ Sˣⱼ₊₁ + Sʸⱼ Sʸⱼ₊₁) * 2 = -∑ⱼ (S⁺ⱼ S⁻ⱼ₊₁ + S⁻ⱼ S⁺ⱼ₊₁)`,
which in the configuration basis exchanges the spins on a bond whose two spins differ.

We also define the translation operator `transOp`, the Lieb-Schultz-Mattis twist operator
`twistOp` (the unitary implementing a `2π` rotation spread over the chain) and the
magnetization sector projections `projOp`.
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

/-- Spin configurations of a chain of `L` sites, each carrying a spin `1/2`
(`true` = up, `false` = down). -/
abbrev Conf (L : ℕ) := Fin L → Bool

/-- The Hilbert space of the spin-1/2 chain with `L` sites. -/
abbrev Chain (L : ℕ) := EuclideanSpace ℂ (Conf L)

/-- The `z`-component of a spin-1/2: `±1/2`, a half-integer. -/
noncomputable def spin (b : Bool) : ℝ := if b then 1 / 2 else -(1 / 2)

/-- The total magnetization of a configuration. -/
noncomputable def totSpin {L : ℕ} (σ : Conf L) : ℝ := ∑ j, spin (σ j)

/-- The twist angle `2π/L`. -/
noncomputable def twistAngle (L : ℕ) : ℝ := 2 * Real.pi / L

variable (L : ℕ) [NeZero L]

/-- Translation of configurations: `(shiftConf σ) j = σ (j+1)`. -/
def shiftConf (σ : Conf L) : Conf L := fun j => σ (j + 1)

/-- Exchange of the spins on the bond `(j, j+1)`. -/
def swapConf (j : Fin L) (σ : Conf L) : Conf L := fun k => σ (Equiv.swap j (j + 1) k)

/-- The hopping (spin exchange) term on the bond `(j, j+1)`. -/
noncomputable def hopMat (j : Fin L) : Matrix (Conf L) (Conf L) ℂ :=
  fun σ τ => if σ j ≠ σ (j + 1) ∧ τ = swapConf L j σ then 1 else 0

/-- The XY Hamiltonian of the chain, as a matrix in the configuration basis. -/
noncomputable def hamMat : Matrix (Conf L) (Conf L) ℂ := -∑ j, hopMat L j

/-- The translation operator, as a matrix in the configuration basis. -/
noncomputable def transMat : Matrix (Conf L) (Conf L) ℂ := fun σ τ => if τ = shiftConf L σ then 1 else 0

/-- The Lieb-Schultz-Mattis twist phase `exp (i (2π/L) ∑ⱼ j Sᶻⱼ)`. -/
noncomputable def twist (σ : Conf L) : ℂ :=
  Complex.exp (Complex.I * (twistAngle L : ℂ) * ((∑ j : Fin L, (j : ℝ) * spin (σ j) : ℝ) : ℂ))

/-- The twist operator, as a matrix in the configuration basis. -/
noncomputable def twistMat : Matrix (Conf L) (Conf L) ℂ := Matrix.diagonal (twist L)

/-- The projection onto the magnetization sector `m`. -/
noncomputable def projMat (m : ℝ) : Matrix (Conf L) (Conf L) ℂ :=
  Matrix.diagonal (fun σ => if totSpin σ = m then 1 else 0)

/-- The XY Hamiltonian as an operator on `Chain L`. -/
noncomputable def hamOp : Chain L →L[ℂ] Chain L := Matrix.toEuclideanCLM (𝕜 := ℂ) (hamMat L)

/-- The translation operator on `Chain L`. -/
noncomputable def transOp : Chain L →L[ℂ] Chain L := Matrix.toEuclideanCLM (𝕜 := ℂ) (transMat L)

/-- The twist operator on `Chain L`. -/
noncomputable def twistOp : Chain L →L[ℂ] Chain L := Matrix.toEuclideanCLM (𝕜 := ℂ) (twistMat L)

/-- The projection onto the magnetization sector `m`, as an operator. -/
noncomputable def projOp (m : ℝ) : Chain L →L[ℂ] Chain L :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (projMat L m)

variable {L}

/-! ### Basic application lemmas -/

omit [NeZero L] in
lemma toEuclideanCLM_apply (M : Matrix (Conf L) (Conf L) ℂ) (x : Chain L) (σ : Conf L) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) M x) σ = ∑ τ, M σ τ * x τ := by
  simp [Matrix.toEuclideanCLM, Matrix.toLin_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply, Finset.sum_ite_eq]

lemma hamOp_apply (x : Chain L) (σ : Conf L) :
    (hamOp L x) σ = -∑ j : Fin L, (if σ j ≠ σ (j + 1) then x (swapConf L j σ) else 0) := by
  rw [hamOp, toEuclideanCLM_apply]
  simp only [hamMat, Matrix.neg_apply, Matrix.sum_apply, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_mul, hopMat]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : σ j = σ (j + 1)
  · simp [h]
  · simp [h, Finset.sum_ite_eq']

lemma transOp_apply (x : Chain L) (σ : Conf L) : (transOp L x) σ = x (shiftConf L σ) := by
  rw [transOp, toEuclideanCLM_apply]
  simp [transMat, Finset.sum_ite_eq']

omit [NeZero L] in
lemma twistOp_apply (x : Chain L) (σ : Conf L) : (twistOp L x) σ = twist L σ * x σ := by
  rw [twistOp, toEuclideanCLM_apply]
  simp [twistMat, Matrix.diagonal]

omit [NeZero L] in
lemma projOp_apply (m : ℝ) (x : Chain L) (σ : Conf L) :
    (projOp L m x) σ = (if totSpin σ = m then 1 else 0) * x σ := by
  rw [projOp, toEuclideanCLM_apply]
  simp [projMat, Matrix.diagonal]

/-! ### Elementary combinatorics of configurations -/

lemma swapConf_involutive (j : Fin L) (σ : Conf L) : swapConf L j (swapConf L j σ) = σ := by
  funext k; simp [swapConf]

/-- The exchange of the spins on a bond, as an involutive equivalence of configurations. -/
def swapEquiv (j : Fin L) : Conf L ≃ Conf L where
  toFun := swapConf L j
  invFun := swapConf L j
  left_inv := swapConf_involutive j
  right_inv := swapConf_involutive j

lemma swapEquiv_apply (j : Fin L) (σ : Conf L) : swapEquiv j σ = swapConf L j σ := rfl

lemma swapConf_apply_self (j : Fin L) (σ : Conf L) : (swapConf L j σ) j = σ (j + 1) := by
  simp [swapConf]

lemma swapConf_apply_succ (j : Fin L) (σ : Conf L) : (swapConf L j σ) (j + 1) = σ j := by
  simp [swapConf]

lemma swapConf_ne (j : Fin L) {σ : Conf L} (h : σ j ≠ σ (j + 1)) :
    (swapConf L j σ) j ≠ (swapConf L j σ) (j + 1) := by
  simp only [swapConf, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact fun hh => h hh.symm

lemma shiftConf_bijective : Function.Bijective (shiftConf L) := by
  constructor
  · intro σ τ h
    funext k
    simpa [shiftConf] using congrFun h (k - 1)
  · intro τ
    exact ⟨fun k => τ (k - 1), by funext k; simp [shiftConf]⟩

lemma spin_le (b : Bool) : spin b ≤ 1 / 2 := by cases b <;> simp [spin]

lemma le_spin (b : Bool) : -(1 / 2 : ℝ) ≤ spin b := by cases b <;> simp [spin]

lemma abs_spin (b : Bool) : |spin b| = 1 / 2 := by cases b <;> simp [spin]

lemma totSpin_shiftConf (σ : Conf L) : totSpin (shiftConf L σ) = totSpin σ := by
  unfold totSpin shiftConf
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin L)) _ _ (fun _ => rfl)

lemma totSpin_swapConf (j : Fin L) (σ : Conf L) : totSpin (swapConf L j σ) = totSpin σ := by
  unfold totSpin swapConf
  exact Fintype.sum_equiv (Equiv.swap j (j + 1)) _ _ (fun _ => rfl)

omit [NeZero L] in
lemma abs_totSpin_le (σ : Conf L) : |totSpin σ| ≤ L / 2 := by
  calc |totSpin σ| ≤ ∑ j : Fin L, |spin (σ j)| := Finset.abs_sum_le_sum_abs _ _
  _ = L / 2 := by simp [abs_spin]; ring

omit [NeZero L] in
lemma eq_allTrue_of_totSpin (σ : Conf L) (h : totSpin σ = L / 2) : σ = fun _ => true := by
  have hsum : ∑ j : Fin L, spin (σ j) = ∑ _j : Fin L, (1 : ℝ) / 2 := by
    rw [Finset.sum_const]
    simpa [totSpin] using h.trans (by field_simp)
  have key := (Finset.sum_eq_sum_iff_of_le (f := fun j : Fin L => spin (σ j))
      (g := fun _ => (1 : ℝ) / 2) (fun i _ => spin_le (σ i))).1 hsum
  funext j
  have hj := (key j (Finset.mem_univ j)).symm
  cases hb : σ j
  · rw [hb] at hj; simp [spin] at hj; norm_num at hj
  · rfl

omit [NeZero L] in
lemma eq_allFalse_of_totSpin (σ : Conf L) (h : totSpin σ = -(L / 2)) : σ = fun _ => false := by
  have hsum : ∑ _j : Fin L, (-(1 / 2 : ℝ)) = ∑ j : Fin L, spin (σ j) := by
    rw [Finset.sum_const]
    simpa [totSpin, eq_comm] using h.trans (by field_simp)
  have key := (Finset.sum_eq_sum_iff_of_le (f := fun _ : Fin L => (-(1 / 2 : ℝ)))
      (g := fun j => spin (σ j)) (fun i _ => le_spin (σ i))).1 hsum
  funext j
  have hj := key j (Finset.mem_univ j)
  cases hb : σ j
  · rfl
  · rw [hb] at hj; simp [spin] at hj; norm_num at hj

/-! ### Further definitions -/

/-- The contribution of the bond `(j, j+1)` to the energy. -/
noncomputable def bondSum (x : Chain L) (j : Fin L) : ℂ :=
  ∑ σ : Conf L, if σ j ≠ σ (j + 1) then conj (x (swapConf L j σ)) * x σ else 0

/-- A vector with real coordinates. -/
def IsRealVec (x : Chain L) : Prop := ∀ σ, conj (x σ) = x σ

/-- Complex conjugation of coordinates. -/
noncomputable def conjVec (x : Chain L) : Chain L := WithLp.toLp 2 (fun σ => conj (x σ))

omit [NeZero L] in
lemma conjVec_apply (x : Chain L) (σ : Conf L) : conjVec x σ = conj (x σ) := rfl

end Phys

import Mathlib

/-!
# Abstract framework for Lieb-Schultz-Mattis type theorems

We work with a finite dimensional complex inner product space `E` (the Hilbert space of a
finite quantum system), a self-adjoint operator `H` (the Hamiltonian), and define ground
states, degeneracy, and low-lying excitations variationally.

The main abstract result is `Phys.lsm_core`: if the ground state `ψ` is non-degenerate,
`T` is a symmetry (an inner-product preserving operator commuting with `H`), `U` is a
norm preserving operator with the *anomalous* commutation relation `T (U ψ) = c • U (T ψ)`
for some `c ≠ 1`, and the twisted state `U ψ` has energy at most `E₀ + ε`, then there is a
unit vector orthogonal to `ψ` with energy at most `E₀ + ε`.
-/

namespace Phys

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The energy expectation value `⟪H ψ, ψ⟫` of a state `ψ`. -/
noncomputable def energy (H : E →L[ℂ] E) (ψ : E) : ℝ := Complex.re (inner ℂ (H ψ) ψ)

lemma energy_eq_reApplyInnerSelf (H : E →L[ℂ] E) (ψ : E) :
    energy H ψ = H.reApplyInnerSelf ψ := rfl

/-- `ψ` is a ground state of `H`: a unit vector minimizing the energy. -/
def IsGroundState (H : E →L[ℂ] E) (ψ : E) : Prop :=
  ‖ψ‖ = 1 ∧ ∀ φ : E, ‖φ‖ = 1 → energy H ψ ≤ energy H φ

/-- The ground state of `H` is degenerate: there are two orthogonal ground states. -/
def Degenerate (H : E →L[ℂ] E) : Prop :=
  ∃ ψ φ : E, IsGroundState H ψ ∧ IsGroundState H φ ∧ inner ℂ ψ φ = (0 : ℂ)

/-- `H` has an excitation of energy at most `ε` above the ground state energy: some unit
vector orthogonal to a ground state has energy at most `E₀ + ε`. -/
def HasLowExcitation (H : E →L[ℂ] E) (ε : ℝ) : Prop :=
  ∃ ψ φ : E, IsGroundState H ψ ∧ ‖φ‖ = 1 ∧ inner ℂ ψ φ = (0 : ℂ) ∧
    energy H φ ≤ energy H ψ + ε

lemma energy_smul (H : E →L[ℂ] E) (a : ℂ) (x : E) :
    energy H (a • x) = Complex.normSq a * energy H x := by
  simp [energy, Complex.normSq_apply]
  ring

lemma IsGroundState.smul {H : E →L[ℂ] E} {ψ : E} (h : IsGroundState H ψ) {a : ℂ}
    (ha : ‖a‖ = 1) : IsGroundState H (a • ψ) := by
  refine ⟨by rw [norm_smul, ha, h.1]; ring, ?_⟩
  intro φ hφ
  have hE : energy H (a • ψ) = energy H ψ := by
    rw [energy_smul, Complex.normSq_eq_norm_sq, ha]; ring
  rw [hE]; exact h.2 φ hφ

section

variable [FiniteDimensional ℂ E]

/-- A ground state exists (the energy is a continuous function on the compact unit sphere). -/
theorem exists_isGroundState [Nontrivial E] (H : E →L[ℂ] E) : ∃ ψ : E, IsGroundState H ψ := by
  have hcomp : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : ContinuousOn (energy H) (Metric.sphere (0 : E) 1) :=
    (by fun_prop : Continuous fun x => Complex.re (inner ℂ (H x) x)).continuousOn
  obtain ⟨ψ, hψmem, hmin⟩ := hcomp.exists_isMinOn hne hcont
  refine ⟨ψ, mem_sphere_zero_iff_norm.mp hψmem, fun φ hφ => ?_⟩
  exact hmin (mem_sphere_zero_iff_norm.mpr hφ)

/-- A ground state is an eigenvector of `H` with eigenvalue the ground state energy. -/
theorem IsGroundState.eigen {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {ψ : E}
    (hψ : IsGroundState H ψ) : H ψ = (energy H ψ : ℂ) • ψ := by
  have hne : ψ ≠ 0 := by
    intro h
    have h1 := hψ.1
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hmin : IsMinOn H.reApplyInnerSelf (Metric.sphere 0 ‖ψ‖) ψ := by
    rw [hψ.1]
    intro x hx
    exact hψ.2 x (mem_sphere_zero_iff_norm.mp hx)
  obtain ⟨hmem, -⟩ := hH.hasEigenvector_of_isMinOn hne hmin
  set r : ℝ := ⨅ x : {x : E // x ≠ 0}, H.rayleighQuotient (x : E) with hr
  have heq : H ψ = (r : ℂ) • ψ := Module.End.mem_eigenspace_iff.1 hmem
  have hE : energy H ψ = r := by
    rw [energy, heq, inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hψ.1]
  rw [heq, hE]

omit [FiniteDimensional ℂ E] in
/-- A unit eigenvector with the ground state energy as eigenvalue is a ground state. -/
theorem isGroundState_of_eigen {H : E →L[ℂ] E} {ψ φ : E} (hψ : IsGroundState H ψ)
    (hφ : ‖φ‖ = 1) (h : H φ = (energy H ψ : ℂ) • φ) : IsGroundState H φ := by
  have hE : energy H φ = energy H ψ := by
    rw [energy, h, inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hφ]
  exact ⟨hφ, by rw [hE]; exact hψ.2⟩

/-- If the ground state `ψ` is non-degenerate (every ground state is a multiple of `ψ`) and
`A` commutes with `H`, then `ψ` is an eigenvector of `A`. -/
theorem eigen_of_commuting {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {ψ : E}
    (hψ : IsGroundState H ψ) (hnd : ∀ φ : E, IsGroundState H φ → ∃ a : ℂ, φ = a • ψ)
    (A : E →L[ℂ] E) (hA : ∀ x, A (H x) = H (A x)) (hAψ : A ψ ≠ 0) :
    ∃ a : ℂ, A ψ = a • ψ := by
  set c : ℝ := ‖A ψ‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hAψ
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  set φ : E := (c⁻¹ : ℂ) • A ψ with hφdef
  have hφnorm : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul]
    simp [hc]
    field_simp
  have hHφ : H φ = (energy H ψ : ℂ) • φ := by
    have h1 : H (A ψ) = A (H ψ) := (hA ψ).symm
    rw [hφdef, ContinuousLinearMap.map_smul, h1, hψ.eigen hH, ContinuousLinearMap.map_smul,
      smul_comm]
  obtain ⟨a, ha⟩ := hnd φ (isGroundState_of_eigen hψ hφnorm hHφ)
  refine ⟨(c : ℂ) * a, ?_⟩
  have h2 : A ψ = (c : ℂ) • φ := by
    rw [hφdef, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  rw [h2, ha, smul_smul]

/-- If some ground state is not a multiple of `ψ`, then the ground state is degenerate. -/
theorem degenerate_of_not_proportional {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {ψ φ : E}
    (hψ : IsGroundState H ψ) (hφ : IsGroundState H φ) (h : ∀ a : ℂ, φ ≠ a • ψ) :
    Degenerate H := by
  set E₀ : ℝ := energy H ψ with hE₀
  have hEφ : energy H φ = E₀ := le_antisymm (by
      have h1 := hψ.2 φ hφ.1
      have h2 := hφ.2 ψ hψ.1
      linarith) (hψ.2 φ hφ.1)
  set v : E := φ - (inner ℂ ψ φ) • ψ with hv
  have hvne : v ≠ 0 := by
    intro h0
    exact h (inner ℂ ψ φ) (by rw [hv, sub_eq_zero] at h0; exact h0)
  have hvnorm : ‖(‖v‖⁻¹ : ℂ) • v‖ = 1 := by
    rw [norm_smul]
    simp [norm_ne_zero_iff.mpr hvne]
  have hHv : H ((‖v‖⁻¹ : ℂ) • v) = (E₀ : ℂ) • ((‖v‖⁻¹ : ℂ) • v) := by
    have h1 : H v = (E₀ : ℂ) • v := by
      rw [hv, map_sub, ContinuousLinearMap.map_smul, hψ.eigen hH,
        show H φ = (E₀ : ℂ) • φ from by rw [← hEφ]; exact hφ.eigen hH]
      rw [smul_sub, smul_comm]
    rw [ContinuousLinearMap.map_smul, h1, smul_comm]
  refine ⟨ψ, (‖v‖⁻¹ : ℂ) • v, hψ, isGroundState_of_eigen hψ hvnorm hHv, ?_⟩
  rw [inner_smul_right, hv, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hψ.1]
  simp

omit [FiniteDimensional ℂ E] in
/-- **The core Lieb-Schultz-Mattis mechanism.**
If the ground state `ψ` is non-degenerate, `T` is a symmetry of `H` preserving the inner
product, and `U` preserves norms and satisfies the anomalous relation `T (U ψ) = c • U (T ψ)`
with `c ≠ 1`, then the twisted state `U ψ` is orthogonal to `ψ`; if moreover its energy
exceeds the ground state energy by at most `ε`, the system has an excitation of energy
at most `ε`. -/
theorem lsm_core {H T U : E →L[ℂ] E} {ψ : E} {c : ℂ} {ε : ℝ}
    (hψ : IsGroundState H ψ)
    (hnd : ∀ φ : E, IsGroundState H φ → ∃ a : ℂ, φ = a • ψ)
    (hT : ∀ x y : E, inner ℂ (T x) (T y) = inner ℂ x y)
    (hTH : ∀ x, H (T x) = T (H x))
    (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (hanom : T (U ψ) = c • U (T ψ)) (hc : c ≠ 1)
    (henergy : energy H (U ψ) ≤ energy H ψ + ε) :
    HasLowExcitation H ε := by
  have hTnorm : ∀ x : E, ‖T x‖ = ‖x‖ := by
    intro x
    have h0 := hT x x
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
    have h1 : (‖T x‖ : ℝ) ^ 2 = (‖x‖ : ℝ) ^ 2 := by exact_mod_cast h0
    nlinarith [norm_nonneg (T x), norm_nonneg x]
  have hTgs : IsGroundState H (T ψ) := by
    refine ⟨by rw [hTnorm, hψ.1], ?_⟩
    have h2 : energy H (T ψ) = energy H ψ := by rw [energy, hTH, hT, ← energy]
    rw [h2]; exact hψ.2
  obtain ⟨a, ha⟩ := hnd (T ψ) hTgs
  have hanorm : ‖a‖ = 1 := by
    have h1 : ‖T ψ‖ = 1 := by rw [hTnorm, hψ.1]
    rw [ha, norm_smul, hψ.1, mul_one] at h1
    exact h1
  have haa : (starRingEnd ℂ) a * a = 1 := by
    rw [mul_comm, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hanorm]
  have hortho : inner ℂ ψ (U ψ) = (0 : ℂ) := by
    have key : inner ℂ ψ (U ψ) = c * inner ℂ ψ (U ψ) := by
      calc inner ℂ ψ (U ψ) = inner ℂ (T ψ) (T (U ψ)) := (hT _ _).symm
      _ = inner ℂ (a • ψ) (c • U (a • ψ)) := by rw [hanom, ha]
      _ = (starRingEnd ℂ) a * (c * (a * inner ℂ ψ (U ψ))) := by
            rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right,
              inner_smul_right]
      _ = ((starRingEnd ℂ) a * a) * (c * inner ℂ ψ (U ψ)) := by ring
      _ = c * inner ℂ ψ (U ψ) := by rw [haa, one_mul]
    have h3 : (1 - c) * inner ℂ ψ (U ψ) = 0 := by rw [sub_mul, one_mul, ← key]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hc
    · exact h
  exact ⟨ψ, U ψ, hψ, by rw [hU, hψ.1], hortho, henergy⟩

end

end Phys

import RequestProject.LSM.Chain

/-!
# Operator properties of the spin-1/2 XY chain

Self-adjointness of the Hamiltonian, unitarity of the translation operator, the
commutation relations of the Hamiltonian with the translation and with the magnetization
sector projections, complex conjugation, and elementary bounds on the energy.
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- The inner product of `Chain L` in coordinates. -/
lemma chain_inner (x y : Chain L) : inner ℂ x y = ∑ σ : Conf L, conj (x σ) * y σ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

omit [NeZero L] in
lemma sum_norm_sq (x : Chain L) : ∑ σ : Conf L, ‖x σ‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-! ### Self-adjointness of the Hamiltonian -/

lemma hopMat_symm (j : Fin L) (σ τ : Conf L) : hopMat L j σ τ = hopMat L j τ σ := by
  unfold hopMat
  by_cases h1 : σ j ≠ σ (j + 1) ∧ τ = swapConf L j σ
  · have h2 : τ j ≠ τ (j + 1) ∧ σ = swapConf L j τ := by
      refine ⟨h1.2 ▸ swapConf_ne j h1.1, ?_⟩
      rw [h1.2, swapConf_involutive]
    rw [if_pos h1, if_pos h2]
  · have h2 : ¬(τ j ≠ τ (j + 1) ∧ σ = swapConf L j τ) := by
      intro h3
      exact h1 ⟨h3.2 ▸ swapConf_ne j h3.1, by rw [h3.2, swapConf_involutive]⟩
    rw [if_neg h1, if_neg h2]

lemma conj_hopMat (j : Fin L) (σ τ : Conf L) : conj (hopMat L j σ τ) = hopMat L j σ τ := by
  unfold hopMat; split <;> simp

lemma hamMat_isHermitian : (hamMat L).IsHermitian := by
  ext σ τ
  show conj (hamMat L τ σ) = hamMat L σ τ
  simp only [hamMat, Matrix.neg_apply, Matrix.sum_apply, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conj_hopMat, hopMat_symm]

lemma hamOp_isSelfAdjoint : IsSelfAdjoint (hamOp L) := by
  have h : star (Matrix.toEuclideanCLM (𝕜 := ℂ) (hamMat L))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (star (hamMat L)) := (map_star _ _).symm
  show star (hamOp L) = hamOp L
  rw [hamOp, h, Matrix.star_eq_conjTranspose, hamMat_isHermitian.eq]

/-! ### Translation invariance -/

/-- Translation of configurations as an equivalence. -/
noncomputable def shiftEquiv (L : ℕ) [NeZero L] : Conf L ≃ Conf L :=
  Equiv.ofBijective (shiftConf L) shiftConf_bijective

lemma transOp_inner (x y : Chain L) : inner ℂ (transOp L x) (transOp L y) = inner ℂ x y := by
  rw [chain_inner, chain_inner]
  simp only [transOp_apply]
  exact Fintype.sum_equiv (shiftEquiv L) _ _ (fun _ => rfl)

/-- Conjugating the exchange of a bond by the translation shifts the bond. -/
lemma swapConf_shiftConf (j : Fin L) (σ : Conf L) :
    swapConf L j (shiftConf L σ) = shiftConf L (swapConf L (j + 1) σ) := by
  funext k
  simp only [swapConf, shiftConf]
  congr 1
  rcases eq_or_ne k j with rfl | h1
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_left, add_assoc]
  rcases eq_or_ne k (j + 1) with rfl | h2
  · rw [Equiv.swap_apply_right]
    exact (Equiv.swap_apply_right _ _).symm
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
      Equiv.swap_apply_of_ne_of_ne (fun hh => h1 (add_right_cancel hh))
        (fun hh => h2 (add_right_cancel hh))]

/-- The Hamiltonian is translation invariant. -/
lemma transOp_comm_hamOp (x : Chain L) : hamOp L (transOp L x) = transOp L (hamOp L x) := by
  ext σ
  rw [hamOp_apply, transOp_apply, hamOp_apply]
  simp only [transOp_apply]
  congr 1
  refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin L)) _ _ (fun j => ?_)).symm
  simp only [Equiv.coe_addRight]
  rw [swapConf_shiftConf]
  rfl

/-- The Hamiltonian conserves the magnetization. -/
lemma projOp_comm_hamOp (m : ℝ) (x : Chain L) :
    projOp L m (hamOp L x) = hamOp L (projOp L m x) := by
  ext σ
  rw [projOp_apply, hamOp_apply, hamOp_apply]
  simp only [projOp_apply, totSpin_swapConf, mul_neg, Finset.mul_sum, mul_ite, mul_zero]

/-! ### Reality of the Hamiltonian -/

omit [NeZero L] in
lemma norm_conjVec (x : Chain L) : ‖conjVec x‖ = ‖x‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

omit [NeZero L] in
lemma inner_conjVec (u v : Chain L) : inner ℂ (conjVec u) (conjVec v) = conj (inner ℂ u v) := by
  rw [chain_inner, chain_inner, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [conjVec_apply, mul_comm]

lemma hamOp_conjVec (x : Chain L) : hamOp L (conjVec x) = conjVec (hamOp L x) := by
  ext σ
  rw [hamOp_apply, conjVec_apply, hamOp_apply, map_neg, map_sum]
  simp only [conjVec_apply, apply_ite conj, map_zero]

lemma energy_conjVec (x : Chain L) : energy (hamOp L) (conjVec x) = energy (hamOp L) x := by
  rw [energy, hamOp_conjVec, inner_conjVec, energy, Complex.conj_re]

/-! ### The energy decomposed into bonds, and a lower bound -/

lemma energy_eq_bondSums (x : Chain L) :
    energy (hamOp L) x = -∑ j : Fin L, (bondSum x j).re := by
  have key : inner ℂ (hamOp L x) x = -∑ j : Fin L, bondSum x j := by
    rw [chain_inner]
    simp only [hamOp_apply, bondSum, map_neg, map_sum, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_mul, apply_ite conj, map_zero, ite_mul, zero_mul]
    rw [Finset.sum_comm]
  rw [energy, key]
  simp [Complex.re_sum]

lemma norm_bondSum_le {x : Chain L} (hx : ‖x‖ = 1) (j : Fin L) : ‖bondSum x j‖ ≤ 1 := by
  have h1 : ‖bondSum x j‖
      ≤ ∑ σ : Conf L, ‖(if σ j ≠ σ (j + 1) then conj (x (swapConf L j σ)) * x σ else 0)‖ :=
    norm_sum_le _ _
  have h2 : ∀ σ : Conf L, ‖(if σ j ≠ σ (j + 1) then conj (x (swapConf L j σ)) * x σ else 0)‖
      ≤ (‖x (swapConf L j σ)‖ ^ 2 + ‖x σ‖ ^ 2) / 2 := by
    intro σ
    split
    · rw [norm_mul, RCLike.norm_conj]
      nlinarith [sq_nonneg (‖x (swapConf L j σ)‖ - ‖x σ‖), norm_nonneg (x (swapConf L j σ)),
        norm_nonneg (x σ)]
    · simp; positivity
  have hswap : ∑ σ : Conf L, ‖x (swapConf L j σ)‖ ^ 2 = ∑ σ : Conf L, ‖x σ‖ ^ 2 :=
    Fintype.sum_equiv (swapEquiv j) _ _ (fun _ => rfl)
  have h3 : ∑ σ : Conf L, (‖x (swapConf L j σ)‖ ^ 2 + ‖x σ‖ ^ 2) / 2 = ‖x‖ ^ 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hswap, sum_norm_sq]
    ring
  calc ‖bondSum x j‖ ≤ _ := h1
    _ ≤ ∑ σ : Conf L, (‖x (swapConf L j σ)‖ ^ 2 + ‖x σ‖ ^ 2) / 2 :=
        Finset.sum_le_sum (fun σ _ => h2 σ)
    _ = ‖x‖ ^ 2 := h3
    _ = 1 := by rw [hx]; norm_num

/-- The energy of any unit vector is at least `-L`. -/
lemma neg_L_le_energy {x : Chain L} (hx : ‖x‖ = 1) : -(L : ℝ) ≤ energy (hamOp L) x := by
  rw [energy_eq_bondSums, neg_le_neg_iff]
  calc ∑ j : Fin L, (bondSum x j).re ≤ ∑ _j : Fin L, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ =>
          le_trans (Complex.re_le_norm _) (norm_bondSum_le hx j)
    _ = (L : ℝ) := by simp

end Phys

import RequestProject.LSM.Energy

/-!
# Ground state properties of the spin-1/2 chain

We collect the facts about a ground state of the XY chain which are needed for the
Lieb-Schultz-Mattis argument:

* if the ground state is non-degenerate it can be chosen with real coordinates
  (`Phys.exists_real_groundState`);
* a non-degenerate ground state lives in a single magnetization sector
  (`Phys.groundState_sector`);
* that magnetization is not saturated (`Phys.sector_abs_lt`): the two saturated
  (fully polarized) states are annihilated by the Hamiltonian, so if the ground state were
  saturated both of them would be ground states, contradicting non-degeneracy;
* the twisted state has energy at most `E₀ + 2π²/L` (`Phys.energy_twist_le`).
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

variable {L : ℕ} [NeZero L]

/-- If the ground state is non-degenerate, it can be chosen to have real coordinates. -/
theorem exists_real_groundState {ψ₀ : Chain L} (hψ₀ : IsGroundState (hamOp L) ψ₀)
    (hnd : ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ₀) :
    ∃ ψ : Chain L, IsGroundState (hamOp L) ψ ∧ IsRealVec ψ ∧
      ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ := by
  have hconj : IsGroundState (hamOp L) (conjVec ψ₀) :=
    ⟨by rw [norm_conjVec, hψ₀.1], by rw [energy_conjVec]; exact hψ₀.2⟩
  obtain ⟨a, ha⟩ := hnd _ hconj
  have hanorm : ‖a‖ = 1 := by
    have h1 : ‖conjVec ψ₀‖ = 1 := hconj.1
    rw [ha, norm_smul, hψ₀.1, mul_one] at h1
    exact h1
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff a).mp hanorm
  set lam : ℂ := Complex.exp ((θ / 2 : ℝ) * Complex.I) with hlam
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlam, Complex.norm_exp]
    simp
  have hlamne : lam ≠ 0 := Complex.exp_ne_zero _
  have hkey : (starRingEnd ℂ) lam * a = lam := by
    have hconjlam : (starRingEnd ℂ) lam = Complex.exp ((-(θ / 2) : ℝ) * Complex.I) := by
      rw [hlam, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
    rw [hconjlam, ← hθ, ← Complex.exp_add, hlam]
    congr 1
    push_cast
    ring
  refine ⟨lam • ψ₀, hψ₀.smul hlamnorm, ?_, ?_⟩
  · intro σ
    have h1 : (lam • ψ₀) σ = lam * ψ₀ σ := rfl
    have h2 : conj (ψ₀ σ) = a * ψ₀ σ := by
      have h3 : (conjVec ψ₀) σ = (a • ψ₀) σ := by rw [ha]
      simpa [conjVec_apply] using h3
    rw [h1, map_mul, h2, ← mul_assoc, hkey]
  · intro φ hφ
    obtain ⟨b, hb⟩ := hnd φ hφ
    refine ⟨b * lam⁻¹, ?_⟩
    rw [hb, smul_smul, mul_assoc, inv_mul_cancel₀ hlamne, mul_one]

/-- A non-degenerate ground state lies in a single magnetization sector. -/
theorem groundState_sector {ψ : Chain L} (hψ : IsGroundState (hamOp L) ψ)
    (hnd : ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ) :
    ∃ m : ℝ, (∀ σ : Conf L, totSpin σ ≠ m → ψ σ = 0) ∧ ∃ σ₀ : Conf L, totSpin σ₀ = m := by
  have hne : ψ ≠ 0 := by
    intro h
    have := hψ.1
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  have hex : ∃ σ₀ : Conf L, ψ σ₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (by ext σ; simpa using hcon σ)
  obtain ⟨σ₀, hσ₀⟩ := hex
  refine ⟨totSpin σ₀, ?_, ⟨σ₀, rfl⟩⟩
  have hPne : projOp L (totSpin σ₀) ψ ≠ 0 := by
    intro h
    have h1 : (projOp L (totSpin σ₀) ψ) σ₀ = (0 : Chain L) σ₀ := by rw [h]
    rw [projOp_apply] at h1
    simp at h1
    exact hσ₀ h1
  obtain ⟨a, ha⟩ := eigen_of_commuting hamOp_isSelfAdjoint hψ hnd (projOp L (totSpin σ₀))
    (fun x => projOp_comm_hamOp _ x) hPne
  have ha1 : a = 1 := by
    have h : (projOp L (totSpin σ₀) ψ) σ₀ = (a • ψ) σ₀ := by rw [ha]
    rw [projOp_apply, if_pos rfl, one_mul] at h
    have h2 : a * ψ σ₀ = 1 * ψ σ₀ := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ hσ₀ h2
  intro σ hσ
  have h : (projOp L (totSpin σ₀) ψ) σ = (a • ψ) σ := by rw [ha]
  rw [projOp_apply, if_neg hσ] at h
  simp only [zero_mul, PiLp.smul_apply, smul_eq_mul, ha1, one_mul] at h
  exact h.symm

/-- A state living in a saturated magnetization sector is annihilated by the Hamiltonian:
a fully polarized chain has no bond with two different spins. -/
theorem hamOp_eq_zero_of_saturated {ψ : Chain L} {m : ℝ}
    (hm : ∀ σ : Conf L, totSpin σ ≠ m → ψ σ = 0) (hsat : m = (L : ℝ) / 2 ∨ m = -((L : ℝ) / 2)) :
    hamOp L ψ = 0 := by
  ext σ
  rw [hamOp_apply]
  simp only [PiLp.zero_apply, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : σ j = σ (j + 1)
  · simp [hj]
  · rw [if_pos hj]
    by_cases hts : totSpin σ = m
    · exfalso
      have hpol : σ j = σ (j + 1) := by
        rcases hsat with h | h
        · rw [eq_allTrue_of_totSpin σ (by rw [hts, h])]
        · rw [eq_allFalse_of_totSpin σ (by rw [hts, h])]
      exact hj hpol
    · exact hm _ (by rwa [totSpin_swapConf])

omit [NeZero L] in
lemma totSpin_allTrue : totSpin (fun _ : Fin L => true) = (L : ℝ) / 2 := by
  simp [totSpin, spin]; ring

omit [NeZero L] in
lemma totSpin_allFalse : totSpin (fun _ : Fin L => false) = -((L : ℝ) / 2) := by
  simp [totSpin, spin]; ring

/-- The fully polarized states are annihilated by the Hamiltonian. -/
lemma hamOp_single_polarized (b : Bool) :
    hamOp L (EuclideanSpace.single (fun _ : Fin L => b) (1 : ℂ)) = 0 := by
  refine hamOp_eq_zero_of_saturated (m := totSpin (fun _ : Fin L => b)) ?_ ?_
  · intro σ hσ
    rw [EuclideanSpace.single_apply, if_neg]
    intro h
    exact hσ (by rw [h])
  · cases b
    · exact Or.inr totSpin_allFalse
    · exact Or.inl totSpin_allTrue

/-- The ground state energy is at most `0`. -/
theorem energy_nonpos {ψ : Chain L} (hψ : IsGroundState (hamOp L) ψ) :
    energy (hamOp L) ψ ≤ 0 := by
  set φ : Chain L := EuclideanSpace.single (fun _ : Fin L => true) (1 : ℂ) with hφ
  have hnorm : ‖φ‖ = 1 := by rw [hφ, EuclideanSpace.norm_single]; simp
  have hE : energy (hamOp L) φ = 0 := by
    rw [energy, hφ, hamOp_single_polarized]
    simp
  have := hψ.2 φ hnorm
  rw [hE] at this
  exact this

/-- The magnetization of a non-degenerate ground state is not saturated. -/
theorem sector_abs_lt (hL : 2 ≤ L) {ψ : Chain L} {m : ℝ} (hψ : IsGroundState (hamOp L) ψ)
    (hnd : ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ)
    (hm : ∀ σ : Conf L, totSpin σ ≠ m → ψ σ = 0) (hmex : ∃ σ₀ : Conf L, totSpin σ₀ = m) :
    |m| < (L : ℝ) / 2 := by
  obtain ⟨σ₀, hσ₀⟩ := hmex
  have hle : |m| ≤ (L : ℝ) / 2 := by rw [← hσ₀]; exact abs_totSpin_le σ₀
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  exfalso
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hL
    exact_mod_cast this
  have hsat : m = (L : ℝ) / 2 ∨ m = -((L : ℝ) / 2) := by
    rcases abs_cases m with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by rw [← h1, h])
    · exact Or.inr (by rw [← h]; linarith)
  have hzero : hamOp L ψ = 0 := hamOp_eq_zero_of_saturated hm hsat
  have hE : energy (hamOp L) ψ = 0 := by rw [energy, hzero]; simp
  -- the opposite polarized state is also a ground state
  set b : Bool := if m = (L : ℝ) / 2 then false else true with hb
  set φ : Chain L := EuclideanSpace.single (fun _ : Fin L => b) (1 : ℂ) with hφ
  have hnorm : ‖φ‖ = 1 := by rw [hφ, EuclideanSpace.norm_single]; simp
  have hgs : IsGroundState (hamOp L) φ := by
    refine isGroundState_of_eigen hψ hnorm ?_
    rw [hφ, hamOp_single_polarized, hE]
    simp
  obtain ⟨c, hc⟩ := hnd φ hgs
  have hval : φ (fun _ : Fin L => b) = (c • ψ) (fun _ : Fin L => b) := by rw [hc]
  rw [hφ] at hval
  simp only [EuclideanSpace.single_apply, if_pos, PiLp.smul_apply, smul_eq_mul] at hval
  have hzeroval : ψ (fun _ : Fin L => b) = 0 := by
    refine hm _ ?_
    rcases hsat with h1 | h1
    · have : b = false := by rw [hb, if_pos h1]
      rw [this, totSpin_allFalse, h1]
      intro hcon
      have : (L : ℝ) = 0 := by linarith
      linarith
    · have hne : m ≠ (L : ℝ) / 2 := by
        rw [h1]
        intro hcon
        have : (L : ℝ) = 0 := by linarith
        linarith
      have : b = true := by rw [hb, if_neg hne]
      rw [this, totSpin_allTrue, h1]
      intro hcon
      have : (L : ℝ) = 0 := by linarith
      linarith
  rw [hzeroval, mul_zero] at hval
  exact one_ne_zero hval

/-- **The variational bound.**  The twisted ground state has energy at most `E₀ + 2π²/L`. -/
theorem energy_twist_le (hL : 2 ≤ L) {ψ : Chain L} (hψ : IsGroundState (hamOp L) ψ)
    (hreal : IsRealVec ψ) :
    energy (hamOp L) (twistOp L ψ) ≤ energy (hamOp L) ψ + 2 * Real.pi ^ 2 / L := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hL
    exact_mod_cast this
  set E := energy (hamOp L) ψ with hE
  have hEle : E ≤ 0 := energy_nonpos hψ
  have hElow : -(L : ℝ) ≤ E := neg_L_le_energy hψ.1
  set α := twistAngle L with hα
  have hαne : α ≠ 0 := by
    rw [hα, twistAngle]
    positivity
  have hcos : 1 - α ^ 2 / 2 < Real.cos α := Real.one_sub_sq_div_two_lt_cos hαne
  have hαsq : α ^ 2 / 2 * (L : ℝ) = 2 * Real.pi ^ 2 / L := by
    rw [hα, twistAngle]
    field_simp
  rw [energy_twistOp hL hreal, ← hE, ← hα]
  nlinarith [Real.cos_le_one α, mul_nonneg (le_of_lt (sub_pos.mpr hcos)) (neg_nonneg.mpr hEle)]

end Phys

