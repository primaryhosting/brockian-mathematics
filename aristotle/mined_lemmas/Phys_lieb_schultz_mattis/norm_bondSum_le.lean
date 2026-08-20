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
