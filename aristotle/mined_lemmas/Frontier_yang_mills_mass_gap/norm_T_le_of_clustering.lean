import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Part I. Transfer matrices, mass gap, and exponential clustering -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The kinematical data extracted from a Euclidean quantum field theory by the
Osterwalder–Schrader reconstruction: a (complex) Hilbert space of physical states, a
normalised vacuum vector, and the self-adjoint contraction semigroup `T t = e^{-tH}`
of Euclidean time translations, which fixes the vacuum. -/
structure TransferMatrixTheory (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Euclidean time evolution semigroup `T t = e^{-t H}`. -/
  T : ℝ → (H →L[ℂ] H)
  /-- The vacuum state. -/
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  T_zero : T 0 = ContinuousLinearMap.id ℂ H
  T_add : ∀ ⦃s t : ℝ⦄, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  T_selfAdjoint : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x y : H, ⟪T t x, y⟫_ℂ = ⟪x, T t y⟫_ℂ
  T_contraction : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖
  T_vacuum : ∀ ⦃t : ℝ⦄, 0 ≤ t → T t vacuum = vacuum

namespace TransferMatrixTheory

variable (Th : TransferMatrixTheory H)

/-- The theory has a mass gap at least `Δ > 0`: on the orthogonal complement of the vacuum
the Euclidean evolution decays at least like `e^{-Δ t}`, uniformly in the state.  Equivalently,
the Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`. -/

theorem norm_T_le_of_clustering (ψ : H) {C Δ : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t))
    {s : ℝ} (hs : 0 ≤ s) :
    ‖Th.T s ψ‖ ≤ Real.exp (-Δ * s) * ‖ψ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg ψ) with hψ | hψ
  · have hψ0 : ψ = 0 := norm_eq_zero.mp hψ.symm
    subst hψ0
    simp
  set N : ℝ := ‖ψ‖ with hN
  set E : ℝ := Real.exp (-Δ * s) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hNpos : (0:ℝ) < N := hψ
  set b : ℕ → ℝ := fun n => ‖Th.T (2 ^ n * s) ψ‖ with hb
  have hbnn : ∀ n, 0 ≤ b n := fun n => norm_nonneg _
  have hsn : ∀ n : ℕ, (0:ℝ) ≤ 2 ^ n * s := by
    intro n; positivity
  -- Step 1 : `b n ^ 2 ≤ N * b (n+1)`
  have step : ∀ n : ℕ, b n ^ 2 ≤ N * b (n + 1) := by
    intro n
    have h := norm_T_sq_le (Th := Th) ψ (hsn n)
    have h2 : (2 : ℝ) * (2 ^ n * s) = 2 ^ (n + 1) * s := by ring
    rw [h2] at h
    exact h
  -- Step 2 : `N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * b n`
  have ind : ∀ n : ℕ, N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * b n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hsq : (N * b 0 ^ (2 ^ n)) ^ 2 ≤ (N ^ (2 ^ n) * b n) ^ 2 :=
          pow_le_pow_left₀ (by positivity) ih 2
        have hexp : (N * b 0 ^ (2 ^ n)) ^ 2 = N ^ 2 * b 0 ^ (2 ^ (n + 1)) := by
          rw [mul_pow, ← pow_mul, pow_succ]
          ring_nf
        have hexp2 : (N ^ (2 ^ n) * b n) ^ 2 = N ^ (2 ^ n) * N ^ (2 ^ n) * b n ^ 2 := by
          rw [mul_pow]; ring
        have hstep := step n
        have hkey : N ^ 2 * b 0 ^ (2 ^ (n + 1))
            ≤ N ^ (2 ^ n) * N ^ (2 ^ n) * (N * b (n + 1)) := by
          calc N ^ 2 * b 0 ^ (2 ^ (n + 1)) = (N * b 0 ^ (2 ^ n)) ^ 2 := hexp.symm
            _ ≤ (N ^ (2 ^ n) * b n) ^ 2 := hsq
            _ = N ^ (2 ^ n) * N ^ (2 ^ n) * b n ^ 2 := hexp2
            _ ≤ N ^ (2 ^ n) * N ^ (2 ^ n) * (N * b (n + 1)) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
        have hpow : N ^ (2 ^ n) * N ^ (2 ^ n) = N ^ (2 ^ (n + 1)) := by
          rw [← pow_add, pow_succ]; ring_nf
        rw [hpow] at hkey
        refine le_of_mul_le_mul_left ?_ hNpos
        calc N * (N * b 0 ^ (2 ^ (n + 1))) = N ^ 2 * b 0 ^ (2 ^ (n + 1)) := by ring
          _ ≤ N ^ (2 ^ (n + 1)) * (N * b (n + 1)) := hkey
          _ = N * (N ^ (2 ^ (n + 1)) * b (n + 1)) := by ring
  -- Step 3 : the ratio `r = b 0 / (N * E)` has all `2^n`-th powers bounded
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, ∀ n : ℕ, b n ≤ C' * E ^ (2 ^ n) := by
    refine ⟨Real.sqrt C, fun n => ?_⟩
    have hbd := norm_T_le_sqrt (Th := Th) ψ hC (hsn n)
    have he : Real.exp (-Δ * (2 ^ n * s)) = E ^ (2 ^ n) := by
      rw [hE, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [he] at hbd
  set r : ℝ := b 0 / (N * E) with hr
  have hrnn : 0 ≤ r := div_nonneg (hbnn 0) (by positivity)
  have hb0 : b 0 = r * (N * E) := by
    rw [hr]; field_simp
  have hrbound : ∀ n : ℕ, N * r ^ (2 ^ n) ≤ C' := by
    intro n
    have h1 := ind n
    have h2 : N ^ (2 ^ n) * b n ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) :=
      mul_le_mul_of_nonneg_left (hC' n) (by positivity)
    have h3 : N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) := le_trans h1 h2
    rw [hb0] at h3
    have h4 : (r * (N * E)) ^ (2 ^ n) = r ^ (2 ^ n) * (N ^ (2 ^ n) * E ^ (2 ^ n)) := by
      rw [mul_pow, mul_pow]
    rw [h4] at h3
    have hNE : (0:ℝ) < N ^ (2 ^ n) * E ^ (2 ^ n) := by positivity
    refine le_of_mul_le_mul_left ?_ hNE
    calc N ^ (2 ^ n) * E ^ (2 ^ n) * (N * r ^ (2 ^ n))
        = N * (r ^ (2 ^ n) * (N ^ (2 ^ n) * E ^ (2 ^ n))) := by ring
      _ ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) := h3
      _ = N ^ (2 ^ n) * E ^ (2 ^ n) * C' := by ring
  -- Step 4 : hence `r ≤ 1`
  have hrle : r ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have htend : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hgt
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp htend (C' / N + 1)).exists
    have hmono : r ^ n ≤ r ^ (2 ^ n) :=
      pow_le_pow_right₀ hgt.le (Nat.lt_two_pow_self.le)
    have hbnd := hrbound n
    have h5 : C' / N + 1 ≤ r ^ (2 ^ n) := le_trans hn hmono
    have h6 : N * (C' / N + 1) ≤ N * r ^ (2 ^ n) :=
      mul_le_mul_of_nonneg_left h5 hNpos.le
    have h7 : N * (C' / N + 1) = C' + N := by field_simp
    linarith
  -- Conclude
  have hfinal : b 0 ≤ N * E := by
    rw [hb0]
    have := mul_le_mul_of_nonneg_right hrle (le_of_lt (mul_pos hNpos hEpos))
    linarith [this]
  have hb0' : ‖Th.T s ψ‖ = b 0 := by simp [hb]
  rw [hb0']
  calc b 0 ≤ N * E := hfinal
    _ = E * N := mul_comm N E

end Core

/-- **Reduction theorem.** Exponential clustering of the Euclidean correlations at rate `Δ`
implies a mass gap of size at least `Δ`: the state-dependent constants disappear. -/
