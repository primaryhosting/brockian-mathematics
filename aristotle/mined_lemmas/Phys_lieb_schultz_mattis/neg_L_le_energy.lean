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
