import Mathlib

/-!
# A formally audited Hilbert–Pólya conditional

This file separates two issues which the original draft conflated.

* `completedRiemannZeta₀` is Mathlib's *additively regularized* completed zeta
  function.  It is not the classical Riemann ξ-function, and its zeros are not
  the nontrivial zeros of `riemannZeta`.
* Symmetry of an unbounded operator, by itself, does not connect an arbitrary
  function called a determinant to a real spectrum.  That connection has to be
  an explicit hypothesis until a genuine spectral and determinant theory is
  supplied.

Accordingly, the corrected theorem below uses the classical entire factor
`riemannXi s = s (s - 1) completedRiemannZeta s`.  Its harmless conventional
constant factor `1/2` is omitted because it has no effect on zeros.  The
Brockian data explicitly includes the load-bearing conclusion that a zero of
its determinant has real spectral parameter.
-/

noncomputable section
open Complex
open scoped InnerProductSpace

/-- The set used in the submitted draft.  It is retained for auditability, but
it is not the set of nontrivial zeta zeros: Mathlib's `completedRiemannZeta₀`
is an additive pole-removal regularization, not the classical ξ-function. -/

lemma riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    riemannXi s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hGamma : Gammaℝ s ≠ 0 := by
    rw [ne_eq, Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      simpa [Nat.cast_add, add_comm, mul_assoc] using hn
  have hcompleted : completedRiemannZeta s = 0 := by
    have hquotient := riemannZeta_def_of_ne_zero hs0
    rw [hz] at hquotient
    exact (div_eq_zero_iff.mp hquotient.symm).resolve_right hGamma
  simp [riemannXi, hcompleted]

/-- Correct ξ-to-RH bridge. -/
