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
