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
