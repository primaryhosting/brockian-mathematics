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
