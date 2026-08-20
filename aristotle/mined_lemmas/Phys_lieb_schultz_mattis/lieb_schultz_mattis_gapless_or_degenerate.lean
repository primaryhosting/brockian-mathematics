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
