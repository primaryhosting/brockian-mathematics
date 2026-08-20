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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/

theorem quantized_of_boundary (c L : ℝ) (hL : 0 < L) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (hL0 : f L = 0) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) L) (hfx₀ : f x₀ ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ c = (n : ℝ) ^ 2 * Real.pi ^ 2 / L ^ 2 := by
  have hc : 0 < c := by
    by_contra hcon
    push_neg at hcon
    exact hfx₀ (no_nonpositive_eigenvalue c L hL hcon f f' hf hf' h0 hL0 x₀ hx₀)
  set k : ℝ := Real.sqrt c with hkdef
  have hk : 0 < k := Real.sqrt_pos.mpr hc
  have hk2 : k ^ 2 = c := Real.sq_sqrt hc.le
  set a : ℝ := f' 0 / k with hadef
  have hak : a * k = f' 0 := by rw [hadef, div_mul_cancel₀ _ hk.ne']
  set g : ℝ → ℝ := fun x => f x - a * Real.sin (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - f' 0 * Real.cos (k * x) with hg'
  have hgd : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    have hs : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x := by
      simpa using ((hasDerivAt_id x).const_mul k).sin
    have hsum := (hf x).sub (hs.const_mul a)
    convert hsum using 1
    simp only [hg']
    rw [← hak]; ring
  have hg'd : ∀ x : ℝ, HasDerivAt g' (-c * g x) x := by
    intro x
    have hcs : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x := by
      simpa using ((hasDerivAt_id x).const_mul k).cos
    have hsum := (hf' x).sub (hcs.const_mul (f' 0))
    convert hsum using 1
    simp only [hg]
    rw [← hak, ← hk2]; ring
  have hg0 : g 0 = 0 := by simp [hg, h0]
  have hg0' : g' 0 = 0 := by simp [hg']
  have hgz := harmonic_unique_zero c hc g g' hgd hg'd hg0 hg0'
  have hfval : ∀ x : ℝ, f x = a * Real.sin (k * x) := by
    intro x
    have hzx := hgz x
    simp only [hg, sub_eq_zero] at hzx
    exact hzx
  have ha : a ≠ 0 := by
    intro hA
    exact hfx₀ (by rw [hfval x₀, hA, zero_mul])
  have hsinL : Real.sin (k * L) = 0 := by
    have hLval := hfval L
    rw [hL0] at hLval
    rcases mul_eq_zero.mp hLval.symm with h | h
    · exact absurd h ha
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsinL
  have hnpos : 0 < (n : ℝ) := by
    have hkl : 0 < k * L := mul_pos hk hL
    nlinarith [Real.pi_pos]
  have hnz : 0 < n := by exact_mod_cast hnpos
  refine ⟨n.toNat, by omega, ?_⟩
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnz.le
  rw [hcast, ← hk2]
  have hkval : k = (n : ℝ) * Real.pi / L := by field_simp; linarith [hn]
  rw [hkval, div_pow, mul_pow]

/-- `boxState L n` is a stationary state with energy `boxEnergy m hbar L n`, for `n ≥ 1`. -/
