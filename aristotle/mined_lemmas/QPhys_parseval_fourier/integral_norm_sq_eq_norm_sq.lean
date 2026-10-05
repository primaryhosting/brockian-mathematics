import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

noncomputable section

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- For an `L²` function, the integral of the squared norm is the square of the `L²` norm. -/

theorem integral_norm_sq_eq_norm_sq (f : Lp (α := V) H 2) :
    ∫ x : V, ‖(f : V → H) x‖ ^ 2 = ‖f‖ ^ 2 := by
  have h1 : (inner ℂ f f : ℂ) = ∫ a : V, (inner ℂ ((f : V → H) a) ((f : V → H) a) : ℂ) :=
    L2.inner_def f f
  simp_rw [inner_self_eq_norm_sq_to_K] at h1
  exact_mod_cast h1.symm

/-- **Parseval/Plancherel theorem.** The Fourier transform is an isometry of `L²`: for every
square-integrable function `f`, the total squared magnitude of its Fourier transform equals the
total squared magnitude of `f`.  (In quantum mechanics: the position-space and momentum-space
wave functions carry the same total probability.) -/
