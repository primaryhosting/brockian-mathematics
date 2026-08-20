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
