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
