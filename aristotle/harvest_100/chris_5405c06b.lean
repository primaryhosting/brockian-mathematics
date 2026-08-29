import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The `n`-th (normalized) stationary state of the infinite square well of width `L`:
`ψₙ(x) = √(2/L) · sin(nπx/L)`. -/
noncomputable def boxState (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π / L * x)

section Helpers

lemma hasDerivAt_lin (k x : ℝ) : HasDerivAt (fun y : ℝ => k * y) k x := by
  simpa using (hasDerivAt_id x).const_mul k

/-- A function with everywhere-vanishing derivative is constant. -/
lemma const_of_hasDerivAt_zero {f : ℝ → ℝ} (h : ∀ x, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 :=
  is_const_of_deriv_eq_zero (fun y => (h y).differentiableAt) (fun y => (h y).deriv) x 0

/-- Uniqueness for `g'' = k² g` with vanishing initial data. -/
lemma ode_unique_nonneg {k : ℝ} {g g' g'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (heq : ∀ x, g'' x = k ^ 2 * g x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) :
    ∀ x, g x = 0 := by
  -- `u x = (g' x + k g x)·e^{-kx}` has vanishing derivative, hence vanishes identically.
  have hu : ∀ x, HasDerivAt (fun y => (g' y + k * g y) * Real.exp (-k * y)) 0 x := by
    intro x
    have hA : HasDerivAt (fun y => g' y + k * g y) (g'' x + k * g' x) x :=
      (h2 x).add ((h1 x).const_mul k)
    have hB : HasDerivAt (fun y => Real.exp (-k * y)) (Real.exp (-k * x) * (-k)) x :=
      (hasDerivAt_lin (-k) x).exp
    have h3 := hA.mul hB
    have hE : (g'' x + k * g' x) * Real.exp (-k * x)
        + (g' x + k * g x) * (Real.exp (-k * x) * (-k)) = 0 := by
      rw [heq x]; ring
    rw [hE] at h3
    exact h3
  have hu0 : ∀ x, g' x + k * g x = 0 := by
    intro x
    have h := const_of_hasDerivAt_zero hu x
    have h0 : (g' x + k * g x) * Real.exp (-k * x) = 0 := by rw [h, hg0, hg'0]; simp
    exact (mul_eq_zero.mp h0).resolve_right (Real.exp_ne_zero _)
  -- `v x = g x · e^{kx}` then also has vanishing derivative.
  have hv : ∀ x, HasDerivAt (fun y => g y * Real.exp (k * y)) 0 x := by
    intro x
    have hB : HasDerivAt (fun y => Real.exp (k * y)) (Real.exp (k * x) * k) x :=
      (hasDerivAt_lin k x).exp
    have h3 := (h1 x).mul hB
    have hE : g' x * Real.exp (k * x) + g x * (Real.exp (k * x) * k) = 0 := by
      have h4 := hu0 x
      nlinarith [Real.exp_pos (k * x)]
    rw [hE] at h3
    exact h3
  intro x
  have h := const_of_hasDerivAt_zero hv x
  have h0 : g x * Real.exp (k * x) = 0 := by rw [h, hg0]; simp
  exact (mul_eq_zero.mp h0).resolve_right (Real.exp_ne_zero _)

/-- Uniqueness for `g'' = -k² g` (`k ≠ 0`) with vanishing initial data, via the conserved
energy `g'² + k² g²`. -/
lemma ode_unique_neg {k : ℝ} (hk : k ≠ 0) {g g' g'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (heq : ∀ x, g'' x = -k ^ 2 * g x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) :
    ∀ x, g x = 0 := by
  have hW : ∀ x, HasDerivAt (fun y => g' y ^ 2 + k ^ 2 * g y ^ 2) 0 x := by
    intro x
    have hA : HasDerivAt (fun y => g' y ^ 2) (2 * g' x * g'' x) x := by
      have h := (h2 x).pow 2
      convert h using 1
      push_cast; ring
    have hB : HasDerivAt (fun y => k ^ 2 * g y ^ 2) (k ^ 2 * (2 * g x * g' x)) x := by
      have h := ((h1 x).pow 2).const_mul (k ^ 2)
      convert h using 1
      push_cast; ring
    have h3 := hA.add hB
    have hE : 2 * g' x * g'' x + k ^ 2 * (2 * g x * g' x) = 0 := by
      rw [heq x]; ring
    rw [hE] at h3
    exact h3
  intro x
  have h := const_of_hasDerivAt_zero hW x
  rw [hg0, hg'0] at h
  simp at h
  have hk2 : 0 < k ^ 2 := by positivity
  have hg2 : g x ^ 2 = 0 := by nlinarith [sq_nonneg (g' x), sq_nonneg (g x)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hg2

/-- Solutions of `ψ'' = -k²ψ` (`k ≠ 0`) vanishing at `0` are multiples of `sin (k x)`. -/
lemma sol_form_neg {k : ℝ} (hk : k ≠ 0) {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (heq : ∀ x, f'' x = -k ^ 2 * f x) (hf0 : f 0 = 0) :
    ∀ x, f x = (f' 0 / k) * Real.sin (k * x) := by
  set B := f' 0 / k with hB
  set g : ℝ → ℝ := fun x => f x - B * Real.sin (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - B * (Real.cos (k * x) * k) with hg'
  set g'' : ℝ → ℝ := fun x => f'' x - B * (-(Real.sin (k * x)) * k * k) with hg''
  have hd1 : ∀ x, HasDerivAt g (g' x) x := fun x =>
    (h1 x).sub (((hasDerivAt_lin k x).sin).const_mul B)
  have hd2 : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    have hc : HasDerivAt (fun y => Real.cos (k * y) * k) (-(Real.sin (k * x)) * k * k) x := by
      have h := ((hasDerivAt_lin k x).cos).mul_const k
      convert h using 1
    exact (h2 x).sub (hc.const_mul B)
  have hgeq : ∀ x, g'' x = -k ^ 2 * g x := by
    intro x
    simp only [hg, hg'']
    rw [heq x]; ring
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hg'0 : g' 0 = 0 := by
    have hc : f' 0 / k * k = f' 0 := div_mul_cancel₀ _ hk
    simp only [hg', hB, mul_zero, Real.cos_zero, one_mul, hc, sub_self]
  have hz := ode_unique_neg hk hd1 hd2 hgeq hg0 hg'0
  intro x
  have hx := hz x
  simp only [hg] at hx
  linarith

/-- Solutions of `ψ'' = k²ψ` (`k > 0`) vanishing at `0` are multiples of `sinh (k x)`. -/
lemma sol_form_pos {k : ℝ} (hk : 0 < k) {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (heq : ∀ x, f'' x = k ^ 2 * f x) (hf0 : f 0 = 0) :
    ∀ x, f x = (f' 0 / k) * Real.sinh (k * x) := by
  set B := f' 0 / k with hB
  set g : ℝ → ℝ := fun x => f x - B * Real.sinh (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - B * (Real.cosh (k * x) * k) with hg'
  set g'' : ℝ → ℝ := fun x => f'' x - B * (Real.sinh (k * x) * k * k) with hg''
  have hd1 : ∀ x, HasDerivAt g (g' x) x := fun x =>
    (h1 x).sub (((hasDerivAt_lin k x).sinh).const_mul B)
  have hd2 : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    have hc : HasDerivAt (fun y => Real.cosh (k * y) * k) (Real.sinh (k * x) * k * k) x := by
      have h := ((hasDerivAt_lin k x).cosh).mul_const k
      convert h using 1
    exact (h2 x).sub (hc.const_mul B)
  have hgeq : ∀ x, g'' x = k ^ 2 * g x := by
    intro x
    simp only [hg, hg'']
    rw [heq x]; ring
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hg'0 : g' 0 = 0 := by
    have hc : f' 0 / k * k = f' 0 := div_mul_cancel₀ _ (ne_of_gt hk)
    simp only [hg', hB, mul_zero, Real.cosh_zero, one_mul, hc, sub_self]
  have hz := ode_unique_nonneg (k := k) hd1 hd2 hgeq hg0 hg'0
  intro x
  have hx := hz x
  simp only [hg] at hx
  linarith

/-- Solutions of `ψ'' = 0` vanishing at `0` are linear. -/
lemma sol_form_zero {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (heq : ∀ x, f'' x = 0) (hf0 : f 0 = 0) :
    ∀ x, f x = f' 0 * x := by
  set B := f' 0 with hB
  set g : ℝ → ℝ := fun x => f x - B * x with hg
  set g' : ℝ → ℝ := fun x => f' x - B with hg'
  have hd1 : ∀ x, HasDerivAt g (g' x) x := fun x => (h1 x).sub (hasDerivAt_lin B x)
  have hd2 : ∀ x, HasDerivAt g' (f'' x) x := fun x => (h2 x).sub_const B
  have hgeq : ∀ x, f'' x = (0 : ℝ) ^ 2 * g x := by intro x; rw [heq x]; ring
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hg'0 : g' 0 = 0 := by simp [hg', hB]
  have hz := ode_unique_nonneg hd1 hd2 hgeq hg0 hg'0
  intro x
  have hx := hz x
  simp only [hg] at hx
  linarith

end Helpers

section Eigenstates

variable {hbar m L : ℝ} {n : ℕ}

/-- The stationary states solve the time-independent Schrödinger equation with energy `Eₙ`. -/
lemma boxState_schrodinger (hm : 0 < m) (hL : 0 < L) (x : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxState L n)) x
      = boxEnergy hbar m L n * boxState L n x := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hm0 : m ≠ 0 := ne_of_gt hm
  set a : ℝ := (n : ℝ) * π / L with ha
  have hstate : boxState L n = fun x => Real.sqrt (2 / L) * Real.sin (a * x) := rfl
  have hd1 : ∀ x, HasDerivAt (boxState L n) (Real.sqrt (2 / L) * (Real.cos (a * x) * a)) x := by
    intro x
    rw [hstate]
    exact ((hasDerivAt_lin a x).sin).const_mul _
  have hderiv1 : deriv (boxState L n) = fun x => Real.sqrt (2 / L) * (Real.cos (a * x) * a) := by
    funext x; exact (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (deriv (boxState L n))
      (Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a)) x := by
    intro x
    rw [hderiv1]
    have hc : HasDerivAt (fun y => Real.cos (a * y) * a) (-(Real.sin (a * x)) * a * a) x := by
      have h := ((hasDerivAt_lin a x).cos).mul_const a
      convert h using 1
    exact hc.const_mul _
  have hderiv2 : deriv (deriv (boxState L n))
      = fun x => Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a) := by
    funext x; exact (hd2 x).deriv
  rw [hderiv2, hstate]
  simp only [boxEnergy]
  have haa : a ^ 2 = (n : ℝ) ^ 2 * π ^ 2 / L ^ 2 := by rw [ha]; ring
  have key : -(hbar ^ 2 / (2 * m)) * (Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a))
      = (hbar ^ 2 / (2 * m)) * a ^ 2 * (Real.sqrt (2 / L) * Real.sin (a * x)) := by ring
  rw [key, haa]
  field_simp

/-- The stationary states are normalized on `[0, L]`. -/
lemma boxState_normalized (hL : 0 < L) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, boxState L n x ^ 2 = 1 := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  set a : ℝ := (n : ℝ) * π / L with ha
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by rw [ha]; positivity
  have hsq : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt (by positivity)
  have h1 : ∀ x : ℝ, boxState L n x ^ 2 = (2 / L) * Real.sin (a * x) ^ 2 := by
    intro x
    show (Real.sqrt (2 / L) * Real.sin (a * x)) ^ 2 = _
    rw [mul_pow, hsq]
  rw [intervalIntegral.integral_congr (g := fun x => (2 / L) * Real.sin (a * x) ^ 2)
    (fun x _ => h1 x), intervalIntegral.integral_const_mul]
  have h2 : ∫ x in (0 : ℝ)..L, Real.sin (a * x) ^ 2 = a⁻¹ • ∫ y in (a * 0)..(a * L), Real.sin y ^ 2 :=
    intervalIntegral.integral_comp_mul_left (fun y => Real.sin y ^ 2) (ne_of_gt ha0)
  rw [h2]
  have haL : a * L = (n : ℝ) * π := by rw [ha]; field_simp
  rw [haL, mul_zero, integral_sin_sq]
  simp [Real.sin_nat_mul_pi]
  field_simp
  rw [← haL]; ring

end Eigenstates

/-- **Particle in a box.**  For a particle of mass `m > 0` in an infinite square well of
width `L > 0` (with reduced Planck constant `ℏ > 0`):

1. for every `n ≥ 1`, the function `ψₙ(x) = √(2/L)·sin(nπx/L)` vanishes at both walls,
   is normalized on `[0, L]`, and solves the time-independent Schrödinger equation
   `-(ℏ²/2m)·ψₙ'' = Eₙ·ψₙ` with `Eₙ = n²π²ℏ²/(2mL²)`;
2. conversely, these are the *only* possible energies: any twice-differentiable solution
   of `-(ℏ²/2m)·ψ'' = E·ψ` with `ψ(0) = ψ(L) = 0` which is not identically zero has
   `E = Eₙ` for some `n ≥ 1`. -/
theorem particle_in_box (hbar m L : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    (∀ n : ℕ, 1 ≤ n →
        boxState L n 0 = 0 ∧ boxState L n L = 0 ∧
        (∀ x, -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxState L n)) x
              = boxEnergy hbar m L n * boxState L n x) ∧
        ∫ x in (0 : ℝ)..L, boxState L n x ^ 2 = 1) ∧
    (∀ (E : ℝ) (psi psi' psi'' : ℝ → ℝ),
        (∀ x, HasDerivAt psi (psi' x) x) → (∀ x, HasDerivAt psi' (psi'' x) x) →
        (∀ x, -(hbar ^ 2 / (2 * m)) * psi'' x = E * psi x) →
        psi 0 = 0 → psi L = 0 → (∃ x, psi x ≠ 0) →
        ∃ n : ℕ, 1 ≤ n ∧ E = boxEnergy hbar m L n) := by
  have hhb0 : hbar ≠ 0 := ne_of_gt hhbar
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hL0 : L ≠ 0 := ne_of_gt hL
  constructor
  · -- Part 1: the states `ψₙ` are eigenstates with energy `Eₙ`.
    intro n hn
    refine ⟨by simp [boxState], ?_, fun x => boxState_schrodinger hm hL x,
      boxState_normalized hL hn⟩
    show Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π / L * L) = 0
    have : (n : ℝ) * π / L * L = (n : ℝ) * π := by field_simp
    rw [this, Real.sin_nat_mul_pi, mul_zero]
  · -- Part 2: quantization of the admissible energies.
    intro E psi psi' psi'' h1 h2 hSch hb0 hbL hne
    have heq : ∀ x, psi'' x = (-(2 * m * E / hbar ^ 2)) * psi x := by
      intro x
      have h := hSch x
      field_simp at h ⊢
      nlinarith [h]
    rcases lt_trichotomy E 0 with hE | hE | hE
    · -- `E < 0` is impossible: the solution would be a multiple of `sinh`.
      exfalso
      have hposc : 0 < -(2 * m * E) / hbar ^ 2 := by
        apply div_pos
        · nlinarith
        · positivity
      set k : ℝ := Real.sqrt (-(2 * m * E) / hbar ^ 2) with hk
      have hkpos : 0 < k := Real.sqrt_pos.mpr hposc
      have hk2 : k ^ 2 = -(2 * m * E) / hbar ^ 2 := Real.sq_sqrt hposc.le
      have heq' : ∀ x, psi'' x = k ^ 2 * psi x := by
        intro x; rw [hk2, heq x]; field_simp
      have hsol := sol_form_pos hkpos h1 h2 heq' hb0
      have hzero : psi' 0 / k = 0 := by
        have h := hsol L
        rw [hbL] at h
        have hsinh : Real.sinh (k * L) ≠ 0 := by
          rw [Ne, Real.sinh_eq_zero]
          positivity
        exact (mul_eq_zero.mp h.symm).resolve_right hsinh
      obtain ⟨x, hx⟩ := hne
      exact hx (by rw [hsol x, hzero, zero_mul])
    · -- `E = 0` is impossible: the solution would be linear.
      exfalso
      have heq' : ∀ x, psi'' x = 0 := by intro x; rw [heq x, hE]; ring
      have hsol := sol_form_zero h1 h2 heq' hb0
      have hzero : psi' 0 = 0 := by
        have h := hsol L
        rw [hbL] at h
        exact (mul_eq_zero.mp h.symm).resolve_right hL0
      obtain ⟨x, hx⟩ := hne
      exact hx (by rw [hsol x, hzero, zero_mul])
    · -- `E > 0`: the solution is a multiple of `sin (k x)`, and `sin (k L) = 0` quantizes `k`.
      set k : ℝ := Real.sqrt (2 * m * E / hbar ^ 2) with hk
      have hkpos : 0 < k := Real.sqrt_pos.mpr (by positivity)
      have hk2 : k ^ 2 = 2 * m * E / hbar ^ 2 := Real.sq_sqrt (by positivity)
      have heq' : ∀ x, psi'' x = -k ^ 2 * psi x := by intro x; rw [hk2, heq x]
      have hsol := sol_form_neg (ne_of_gt hkpos) h1 h2 heq' hb0
      have hB : psi' 0 / k ≠ 0 := by
        intro h
        obtain ⟨x, hx⟩ := hne
        exact hx (by rw [hsol x, h, zero_mul])
      have hsin : Real.sin (k * L) = 0 := by
        have h := hsol L
        rw [hbL] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hB
      obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsin
      have hjpos : 0 < j := by
        by_contra hc
        push_neg at hc
        have hle : (j : ℝ) * π ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc) Real.pi_pos.le
        rw [hj] at hle
        nlinarith [hkpos, hL]
      refine ⟨j.toNat, by omega, ?_⟩
      have hjn : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        have h : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hjpos.le
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
      have hkL : k * L = (j : ℝ) * π := hj.symm
      have hE' : E = k ^ 2 * hbar ^ 2 / (2 * m) := by rw [hk2]; field_simp
      have hkval : k = (j : ℝ) * π / L := by field_simp; linarith [hkL]
      rw [boxEnergy, hjn, hE', hkval]
      field_simp

end QPhys

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

