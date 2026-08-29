import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Iterating a translation-eigenvalue relation: `ψ (x₀ + n a) = c ^ n * ψ x₀`. -/
theorem translate_iterate (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ)
    (hc : ∀ x : ℝ, ψ (x + a) = c * ψ x) (x₀ : ℝ) :
    ∀ n : ℕ, ψ (x₀ + n * a) = c ^ n * ψ x₀ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : x₀ + ((n + 1 : ℕ) : ℝ) * a = (x₀ + (n : ℝ) * a) + a := by
        push_cast; ring
      rw [hx, hc, ih]
      ring

/-- If a bounded, not-identically-zero function satisfies `ψ (x + a) = c * ψ x`,
then `‖c‖ ≤ 1`: otherwise the values `c ^ n * ψ x₀` would be unbounded. -/
theorem norm_le_one_of_bounded_translation (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hb : ∀ x : ℝ, ‖ψ x‖ ≤ M) (x₀ : ℝ) (h0 : ψ x₀ ≠ 0)
    (hc : ∀ x : ℝ, ψ (x + a) = c * ψ x) : ‖c‖ ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr h0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) hgt
  have hkey : ‖c‖ ^ n * ‖ψ x₀‖ ≤ M := by
    have := hb (x₀ + (n : ℝ) * a)
    rwa [translate_iterate a ψ c hc x₀ n, norm_mul, norm_pow] at this
  have : M / ‖ψ x₀‖ * ‖ψ x₀‖ < ‖c‖ ^ n * ‖ψ x₀‖ := by
    exact (mul_lt_mul_of_pos_right hn hpos)
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
  linarith

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian on wavefunctions `ℝ → ℂ` which is periodic
with period `a > 0` (it commutes with translation by `a`).  Let `ψ` be a bounded, nonzero
eigenstate of `H` with eigenvalue `E`, whose eigenspace is nondegenerate (one dimensional).
Then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an `a`-periodic function
`u` with `ψ x = exp (i k x) * u x` for all `x`. -/
theorem bloch_theorem
    (a : ℝ) (ha : 0 < a)
    (H : (ℝ → ℂ) → (ℝ → ℂ)) (E : ℂ) (ψ : ℝ → ℂ)
    (hHper : ∀ f : ℝ → ℂ, H (fun x : ℝ => f (x + a)) = fun x : ℝ => H f (x + a))
    (hψE : H ψ = fun x : ℝ => E * ψ x)
    (hnd : ∀ f : ℝ → ℂ, (H f = fun x : ℝ => E * f x) → ∃ c : ℂ, f = fun x : ℝ => c * ψ x)
    (hbdd : ∃ M : ℝ, ∀ x : ℝ, ‖ψ x‖ ≤ M)
    (hne : ψ ≠ 0) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧
      (∀ x : ℝ, ψ x = Complex.exp (Complex.I * (k * x)) * u x) := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨x₀, hx₀⟩ : ∃ x : ℝ, ψ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  -- The translate of `ψ` is again an eigenstate with eigenvalue `E`, hence proportional to `ψ`.
  have hT : H (fun x : ℝ => ψ (x + a)) = fun x : ℝ => E * (ψ (x + a)) := by
    rw [hHper ψ, hψE]
  obtain ⟨c, hc⟩ := hnd _ hT
  have hc' : ∀ x : ℝ, ψ (x + a) = c * ψ x := fun x => congrFun hc x
  -- `c ≠ 0`.
  have hc0 : c ≠ 0 := by
    intro h
    apply hx₀
    have := hc' (x₀ - a)
    rw [h, sub_add_cancel] at this
    simpa using this
  -- `‖c‖ = 1`, using boundedness in both directions.
  have hle : ‖c‖ ≤ 1 :=
    norm_le_one_of_bounded_translation a ψ c M hM x₀ hx₀ hc'
  have hge : 1 ≤ ‖c‖ := by
    have hrefl : ∀ x : ℝ, (fun y : ℝ => ψ (-y)) (x + a) = c⁻¹ * (fun y : ℝ => ψ (-y)) x := by
      intro x
      have hthis := hc' (-(x + a))
      have hx : -(x + a) + a = -x := by ring
      rw [hx] at hthis
      show ψ (-(x + a)) = c⁻¹ * ψ (-x)
      rw [hthis, inv_mul_cancel_left₀ hc0]
    have h1 : ‖c⁻¹‖ ≤ 1 :=
      norm_le_one_of_bounded_translation a (fun y : ℝ => ψ (-y)) c⁻¹ M
        (fun x => hM (-x)) (-x₀) (by simpa using hx₀) hrefl
    rw [norm_inv] at h1
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    rw [inv_le_one_iff₀] at h1
    rcases h1 with h1 | h1
    · linarith
    · exact h1
  have hnorm : ‖c‖ = 1 := le_antisymm hle hge
  -- Write `c = exp (i θ)` and set `k = θ / a`.
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff c).mp hnorm
  refine ⟨θ / a, fun x : ℝ => Complex.exp (-(Complex.I * ((θ / a : ℝ) * x))) * ψ x, ?_, ?_⟩
  · intro x
    have hka : ((θ / a : ℝ) : ℂ) * ((a : ℝ) : ℂ) = ((θ : ℝ) : ℂ) := by
      have : (θ / a) * a = θ := div_mul_cancel₀ _ (ne_of_gt ha)
      exact_mod_cast this
    have hsplit : -(Complex.I * (((θ / a : ℝ) : ℂ) * (((x + a : ℝ)) : ℂ)))
        = -(Complex.I * (((θ / a : ℝ) : ℂ) * ((x : ℝ) : ℂ))) + -((θ : ℝ) * Complex.I) := by
      have hcast : (((x + a : ℝ)) : ℂ) = (x : ℂ) + (a : ℂ) := by push_cast; ring
      rw [hcast, ← hka]
      ring
    show Complex.exp (-(Complex.I * (((θ / a : ℝ) : ℂ) * (((x + a : ℝ)) : ℂ)))) * ψ (x + a)
        = Complex.exp (-(Complex.I * (((θ / a : ℝ) : ℂ) * ((x : ℝ) : ℂ)))) * ψ x
    have hinv : Complex.exp (-(((θ : ℝ) : ℂ) * Complex.I)) = c⁻¹ := by
      rw [Complex.exp_neg, hθ]
    rw [hc' x, hsplit, Complex.exp_add, hinv]
    field_simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- A toy periodic Hamiltonian: it acts as the identity on constant functions and as `0`
on all other functions.  Used only to witness that the hypotheses of `bloch_theorem`
are simultaneously satisfiable. -/
noncomputable def constHamiltonian (f : ℝ → ℂ) : ℝ → ℂ :=
  if (∃ c : ℂ, f = fun _ : ℝ => c) then f else 0

/-- Translation by `a` preserves constancy of a function. -/
theorem exists_const_translate (a : ℝ) (f : ℝ → ℂ) :
    (∃ c : ℂ, (fun x : ℝ => f (x + a)) = fun _ : ℝ => c) ↔ (∃ c : ℂ, f = fun _ : ℝ => c) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun x => ?_⟩
    have := congrFun hc (x - a)
    simpa using this
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun x => by rw [hc]⟩

/-- The hypotheses of `bloch_theorem` are not vacuous: they are satisfied by the
constant wavefunction `ψ = 1` for the Hamiltonian `constHamiltonian` with `E = 1`. -/
theorem bloch_hypotheses_satisfiable :
    ∃ (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) (E : ℂ) (ψ : ℝ → ℂ),
      0 < a ∧
      (∀ f : ℝ → ℂ, H (fun x : ℝ => f (x + a)) = fun x : ℝ => H f (x + a)) ∧
      (H ψ = fun x : ℝ => E * ψ x) ∧
      (∀ f : ℝ → ℂ, (H f = fun x : ℝ => E * f x) → ∃ c : ℂ, f = fun x : ℝ => c * ψ x) ∧
      (∃ M : ℝ, ∀ x : ℝ, ‖ψ x‖ ≤ M) ∧ ψ ≠ 0 := by
  refine ⟨1, constHamiltonian, 1, (fun _ => 1), one_pos, ?_, ?_, ?_, ⟨1, by simp⟩, ?_⟩
  · intro f
    by_cases h : ∃ c : ℂ, f = fun _ : ℝ => c
    · have h2 : ∃ c : ℂ, (fun x : ℝ => f (x + 1)) = fun _ : ℝ => c :=
        (exists_const_translate 1 f).mpr h
      simp only [constHamiltonian, if_pos h, if_pos h2]
    · have h2 : ¬ ∃ c : ℂ, (fun x : ℝ => f (x + 1)) = fun _ : ℝ => c := fun hh =>
        h ((exists_const_translate 1 f).mp hh)
      simp only [constHamiltonian, if_neg h, if_neg h2]
      rfl
  · have h : ∃ c : ℂ, (fun _ : ℝ => (1 : ℂ)) = fun _ : ℝ => c := ⟨1, rfl⟩
    simp [constHamiltonian, if_pos h]
  · intro f hf
    by_cases h : ∃ c : ℂ, f = fun _ : ℝ => c
    · obtain ⟨c, hc⟩ := h
      exact ⟨c, by rw [hc]; simp⟩
    · rw [constHamiltonian, if_neg h] at hf
      exact absurd ⟨0, funext fun x => by simpa using (congrFun hf x).symm⟩ h
  · intro h
    have := congrFun h 0
    simp at this

end Phys

