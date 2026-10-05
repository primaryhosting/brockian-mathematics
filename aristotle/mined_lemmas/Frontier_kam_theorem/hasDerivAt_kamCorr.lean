/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Real Finset RealInnerProductSpace

namespace Frontier

/-- One factor of phase space, `ℝⁿ`.  It is used both for the action variables `p`
and for the angle variables `q`; the angles are understood modulo the lattice `2π ℤⁿ`. -/
abbrev Phase (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Fourier mode `k ∈ ℤⁿ`, viewed as a vector of `ℝⁿ`. -/

lemma hasDerivAt_kamCorr (hnr : ∀ k ∈ K, ⟪mode k, ω⟫ ≠ 0) (θ : Phase n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kamCorr ω K a b (θ + s • ω))
      (gradPert K a b (θ + t • ω)) t := by
  classical
  have key : ∀ k ∈ K, HasDerivAt
      (fun s : ℝ => ((a k * cos ⟪mode k, θ + s • ω⟫ + b k * sin ⟪mode k, θ + s • ω⟫)
        / ⟪mode k, ω⟫) • mode k)
      ((-(a k) * sin ⟪mode k, θ + t • ω⟫ + b k * cos ⟪mode k, θ + t • ω⟫) • mode k) t := by
    intro k hk
    set d : ℝ := ⟪mode k, ω⟫ with hd
    set s0 : ℝ := ⟪mode k, θ⟫ with hs0
    have hdne : d ≠ 0 := hnr k hk
    have hlin : HasDerivAt (fun s : ℝ => s0 + s * d) d t := by
      simpa using ((hasDerivAt_id t).mul_const d).const_add s0
    have hc : HasDerivAt (fun s : ℝ => cos (s0 + s * d)) (-sin (s0 + t * d) * d) t :=
      (Real.hasDerivAt_cos _).comp t hlin
    have hs : HasDerivAt (fun s : ℝ => sin (s0 + s * d)) (cos (s0 + t * d) * d) t :=
      (Real.hasDerivAt_sin _).comp t hlin
    have hf : HasDerivAt (fun s : ℝ => (a k * cos (s0 + s * d) + b k * sin (s0 + s * d)) / d)
        ((-(a k) * sin (s0 + t * d) + b k * cos (s0 + t * d))) t := by
      have := ((hc.const_mul (a k)).add (hs.const_mul (b k))).div_const d
      convert this using 1
      field_simp
    have := hf.smul_const (mode k)
    simpa only [inner_mode_add_smul] using this
  have hsum := HasDerivAt.fun_sum key
  simpa only [kamCorr, gradPert] using hsum

/-- The correction `U` is `2π`-periodic in each angle, i.e. it is a function on the torus. -/
