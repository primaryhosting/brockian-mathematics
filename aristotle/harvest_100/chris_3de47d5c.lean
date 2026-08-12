/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-- Translation of a wave function by the lattice constant `a`: `(transl a f) x = f (x + a)`. -/
def transl (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x + a)

/-- A Hamiltonian `H` acting on wave functions is *periodic* with period `a` when it
commutes with translation by `a`. -/
def PeriodicHamiltonian (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ f, H (transl a f) = transl a (H f)

section Helpers

/-- Iterating the quasi-periodicity relation `f (x + a) = c * f x`. -/
lemma shift_pow {A : ℝ} {c : ℂ} {f : ℝ → ℂ} (h : ∀ x, f (x + A) = c * f x) :
    ∀ (n : ℕ) (x : ℝ), f (x + n * A) = c ^ n * f x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      have : (x : ℝ) + (m + 1 : ℕ) * A = (x + m * A) + A := by push_cast; ring
      rw [this, h, ih, pow_succ]
      ring

/-- If a bounded, not identically zero function satisfies `f (x + A) = c * f x`,
then `‖c‖ ≤ 1`. -/
lemma norm_le_one_of_bounded {A : ℝ} {c : ℂ} {f : ℝ → ℂ} {M : ℝ}
    (h : ∀ x, f (x + A) = c * f x) (hM : ∀ x, ‖f x‖ ≤ M) {x₀ : ℝ} (hx₀ : f x₀ ≠ 0) :
    ‖c‖ ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < ‖f x₀‖ := norm_pos_iff.mpr hx₀
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖f x₀‖) hc
  have key : ‖f (x₀ + n * A)‖ = ‖c‖ ^ n * ‖f x₀‖ := by
    rw [shift_pow h n x₀, norm_mul, norm_pow]
  have h1 : M < ‖c‖ ^ n * ‖f x₀‖ := by
    rw [div_lt_iff₀ hpos] at hn
    exact hn
  have h2 : ‖f (x₀ + n * A)‖ ≤ M := hM _
  rw [key] at h2
  linarith

end Helpers

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian on wave functions `ℝ → ℂ` that is periodic
with lattice constant `a > 0` (i.e. commutes with translation by `a`).  Let `ψ` be a bounded,
nonzero eigenstate of `H` with eigenvalue `E`, and assume the eigenvalue `E` is nondegenerate
(every eigenstate with eigenvalue `E` is a scalar multiple of `ψ`).

Then there is a crystal momentum `k : ℝ` and a lattice-periodic function `u` such that
`ψ x = e^{i k x} u x`, i.e. `ψ` is a Bloch wave. -/
theorem bloch_theorem {a : ℝ} (ha : 0 < a) {H : (ℝ → ℂ) → (ℝ → ℂ)}
    (hHper : PeriodicHamiltonian a H) {ψ : ℝ → ℂ} {E : ℂ}
    (hEig : H ψ = E • ψ)
    (hnondeg : ∀ g : ℝ → ℂ, H g = E • g → ∃ c : ℂ, g = c • ψ)
    {x₀ : ℝ} (hx₀ : ψ x₀ ≠ 0)
    {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x, u (x + a) = u x) ∧ ∀ x, ψ x = Complex.exp (k * x * Complex.I) * u x := by
  -- The translate of `ψ` is again an eigenstate with eigenvalue `E`.
  have htransEig : H (transl a ψ) = E • transl a ψ := by
    rw [hHper ψ, hEig]
    funext x
    simp [transl]
  -- By nondegeneracy it is a multiple of `ψ`.
  obtain ⟨c, hc⟩ := hnondeg _ htransEig
  have hshift : ∀ x, ψ (x + a) = c * ψ x := by
    intro x
    have := congrFun hc x
    simpa [transl] using this
  -- `c` is nonzero.
  have hcne : c ≠ 0 := by
    intro h0
    apply hx₀
    have := hshift (x₀ - a)
    rw [h0] at this
    simpa using this
  -- `‖c‖ ≤ 1`.
  have hle : ‖c‖ ≤ 1 := norm_le_one_of_bounded hshift hM hx₀
  -- `‖c‖ ≥ 1`, by applying the same bound to the reflected function.
  have hge : (1 : ℝ) ≤ ‖c‖ := by
    have hrefl : ∀ x : ℝ, (fun y : ℝ => ψ (-y)) (x + a) = c⁻¹ * (fun y : ℝ => ψ (-y)) x := by
      intro x
      have h1 : ψ (-x) = c * ψ (-x - a) := by
        have := hshift (-x - a)
        rwa [show -x - a + a = -x by ring] at this
      show ψ (-(x + a)) = c⁻¹ * ψ (-x)
      rw [h1, show -(x + a) = -x - a by ring]
      field_simp
    have hMr : ∀ x : ℝ, ‖(fun y : ℝ => ψ (-y)) x‖ ≤ M := fun x => hM (-x)
    have hx₀r : (fun y : ℝ => ψ (-y)) (-x₀) ≠ 0 := by simpa using hx₀
    have := norm_le_one_of_bounded (f := fun y : ℝ => ψ (-y)) hrefl hMr hx₀r
    rw [norm_inv] at this
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    rw [inv_le_one₀ hcpos] at this
    exact this
  have hnorm : ‖c‖ = 1 := le_antisymm hle hge
  -- Write `c = exp (θ i)` and set `k = θ / a`.
  set θ : ℝ := Complex.arg c
  have hcexp : c = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hnorm] at this
    simpa using this.symm
  refine ⟨θ / a, fun x => Complex.exp (-(θ / a) * x * Complex.I) * ψ x, ?_, ?_⟩
  · intro x
    dsimp only
    rw [hshift x, hcexp]
    rw [← mul_assoc, ← Complex.exp_add]
    have hane : (a : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ha
    congr 2
    field_simp
    push_cast
    ring
  · intro x
    dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    have : ((θ / a : ℝ) : ℂ) * x * Complex.I + (-((θ / a : ℝ) : ℂ)) * x * Complex.I = 0 := by
      ring
    push_cast
    push_cast at this
    rw [this]
    simp

/-- Translation by `A` is injective on wave functions. -/
lemma transl_injective (A : ℝ) : Function.Injective (transl A) := by
  intro f g h
  funext x
  have := congrFun h (x - A)
  simpa [transl] using this

/-- The hypotheses of `bloch_theorem` are satisfiable: they hold for the plane wave
`ψ x = e^{ix}` with lattice constant `2π`, so the theorem is not vacuous. -/
lemma bloch_theorem_hypotheses_satisfiable :
    ∃ (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) (ψ : ℝ → ℂ) (E : ℂ) (x₀ M : ℝ),
      0 < a ∧ PeriodicHamiltonian a H ∧ H ψ = E • ψ ∧
      (∀ g : ℝ → ℂ, H g = E • g → ∃ c : ℂ, g = c • ψ) ∧ ψ x₀ ≠ 0 ∧ (∀ x, ‖ψ x‖ ≤ M) := by
  classical
  set ψ : ℝ → ℂ := fun x => Complex.exp (x * Complex.I) with hψdef
  refine ⟨2 * Real.pi, fun f => if f = ψ then ψ else 0, ψ, 1, 0, 1, by positivity, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- periodicity of the Hamiltonian
    have hψper : transl (2 * Real.pi) ψ = ψ := by
      funext x
      simp only [transl, hψdef]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I
            = (x : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    intro f
    by_cases hf : f = ψ
    · subst hf
      simp [hψper]
    · have hf' : transl (2 * Real.pi) f ≠ ψ := by
        intro h
        exact hf (transl_injective (2 * Real.pi) (h.trans hψper.symm))
      simp only [hf, hf', if_false]
      funext x
      simp [transl]
  · simp
  · intro g hg
    by_cases hgψ : g = ψ
    · exact ⟨1, by simp [hgψ]⟩
    · refine ⟨0, ?_⟩
      simp only [hgψ, if_false, one_smul] at hg
      simp [← hg]
  · simp [hψdef]
  · intro x
    simp [hψdef, Complex.norm_exp_ofReal_mul_I]

end Phys

