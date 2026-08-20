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
