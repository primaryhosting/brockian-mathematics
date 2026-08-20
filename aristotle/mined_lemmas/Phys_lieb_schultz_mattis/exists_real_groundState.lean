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

theorem exists_real_groundState {ψ₀ : Chain L} (hψ₀ : IsGroundState (hamOp L) ψ₀)
    (hnd : ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ₀) :
    ∃ ψ : Chain L, IsGroundState (hamOp L) ψ ∧ IsRealVec ψ ∧
      ∀ φ : Chain L, IsGroundState (hamOp L) φ → ∃ a : ℂ, φ = a • ψ := by
  have hconj : IsGroundState (hamOp L) (conjVec ψ₀) :=
    ⟨by rw [norm_conjVec, hψ₀.1], by rw [energy_conjVec]; exact hψ₀.2⟩
  obtain ⟨a, ha⟩ := hnd _ hconj
  have hanorm : ‖a‖ = 1 := by
    have h1 : ‖conjVec ψ₀‖ = 1 := hconj.1
    rw [ha, norm_smul, hψ₀.1, mul_one] at h1
    exact h1
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff a).mp hanorm
  set lam : ℂ := Complex.exp ((θ / 2 : ℝ) * Complex.I) with hlam
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlam, Complex.norm_exp]
    simp
  have hlamne : lam ≠ 0 := Complex.exp_ne_zero _
  have hkey : (starRingEnd ℂ) lam * a = lam := by
    have hconjlam : (starRingEnd ℂ) lam = Complex.exp ((-(θ / 2) : ℝ) * Complex.I) := by
      rw [hlam, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
    rw [hconjlam, ← hθ, ← Complex.exp_add, hlam]
    congr 1
    push_cast
    ring
  refine ⟨lam • ψ₀, hψ₀.smul hlamnorm, ?_, ?_⟩
  · intro σ
    have h1 : (lam • ψ₀) σ = lam * ψ₀ σ := rfl
    have h2 : conj (ψ₀ σ) = a * ψ₀ σ := by
      have h3 : (conjVec ψ₀) σ = (a • ψ₀) σ := by rw [ha]
      simpa [conjVec_apply] using h3
    rw [h1, map_mul, h2, ← mul_assoc, hkey]
  · intro φ hφ
    obtain ⟨b, hb⟩ := hnd φ hφ
    refine ⟨b * lam⁻¹, ?_⟩
    rw [hb, smul_smul, mul_assoc, inv_mul_cancel₀ hlamne, mul_one]

/-- A non-degenerate ground state lies in a single magnetization sector. -/
