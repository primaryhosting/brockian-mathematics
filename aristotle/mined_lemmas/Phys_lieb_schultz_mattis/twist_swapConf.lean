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
