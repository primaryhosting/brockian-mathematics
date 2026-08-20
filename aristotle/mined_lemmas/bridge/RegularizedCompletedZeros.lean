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

def RegularizedCompletedZeros : Set ℂ :=
  {s : ℂ | completedRiemannZeta₀ s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- A densely defined symmetric operator represented by a linear partial map.

The submitted name `UnboundedSelfAdjoint` overstated its fields: the displayed
inner-product identity says *symmetric*, whereas self-adjointness additionally
requires equality with the adjoint domain.  The more precise name prevents that
important analytic gap from being hidden. -/
structure DenselyDefinedSymmetric (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : H →ₗ.[ℂ] H
  dense_domain : Dense (operator.domain : Set H)
  symmetric : ∀ x y : operator.domain,
    ⟪operator x, (y : H)⟫_ℂ = ⟪(x : H), operator y⟫_ℂ

/-- Abstract determinant data.  No spectral meaning follows merely from this
structure; such meaning is supplied separately in `BrockianSystem`. -/
structure SpectralDeterminant (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : DenselyDefinedSymmetric H) where
  detFn : ℂ → ℂ

/-- The classical ξ-factor, up to the irrelevant nonzero scalar `1/2`.

For a nontrivial zero of `riemannZeta`, the gamma factor is nonzero and hence
`completedRiemannZeta` vanishes; consequently this function vanishes too. -/
