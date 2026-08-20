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

def riemannXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta s

/-- The genuine nontrivial-zero set appearing in the Riemann hypothesis. -/

def NontrivialZetaZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1}

/- The original bridge cannot be used:

```

theorem bridge
    (h : ∀ s ∈ RegularizedCompletedZeros, s.re = 1 / 2) :
    RiemannHypothesis
```

Its premise concerns zeros of `completedRiemannZeta₀`, which satisfies
`completedRiemannZeta = completedRiemannZeta₀ - 1/s - 1/(1-s)`; therefore a
nontrivial zeta zero is not thereby a zero of `completedRiemannZeta₀`.
The corrected bridge is stated using `riemannXi`. -/

/-- Every nontrivial zeta zero is a zero of the classical ξ-factor. -/

theorem bridge
    (h : ∀ s ∈ NontrivialZetaZeros, s.re = 1 / 2) :
    RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s hz htriv hs1
  exact h s (by unfold NontrivialZetaZeros; exact ⟨hz, htriv, hs1⟩)

/-- Data sufficient for the formal Hilbert–Pólya implication.

`det_zero_iff_xi_zero` is the determinant identity at the level actually used
by the proof.  `det_zero_im_zero` is the precise spectral-reality obligation:
every determinant zero has a real parameter.  A future operator-theoretic
development should derive this field from self-adjointness plus a rigorous
identification of determinant zeros with spectrum.

The finite witness field records only nonemptiness, exactly as in the submitted
Gate 0 placeholder; it has no mathematical force and is not used by the RH
proof. -/
structure BrockianSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  B : DenselyDefinedSymmetric H
  det : SpectralDeterminant H B
  det_zero_iff_xi_zero : ∀ t : ℂ,
    det.detFn t = 0 ↔ riemannXi (1 / 2 + I * t) = 0
  det_zero_im_zero : ∀ t : ℂ, det.detFn t = 0 → t.im = 0
  gate0_witness : ∀ _N : ℕ, ∃ (V : Type) (_ : Fintype V), True

/-- The rigorously stated conditional Hilbert–Pólya implication.

Given a nontrivial zero `s`, use the spectral coordinate
`t = -I * (s - 1/2)`, for which `1/2 + I*t = s`.  The ξ bridge makes the
determinant vanish at `t`; spectral reality gives `t.im = 0`, and direct
complex arithmetic then yields `s.re = 1/2`. -/
