/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Uhlenbeck bubbling: quantization of the blow-up set

For a sequence of Yang–Mills connections `A n` on a bundle over a Riemannian manifold `X`
with uniformly bounded Yang–Mills energy `E`, Uhlenbeck's compactness theorem says that,
after gauge transformations and passing to a subsequence, the connections converge smoothly
away from a finite "bubbling" set of points, and at each bubbling point at least a fixed
quantum `ε₀ > 0` of energy is lost.

The genuinely analytic inputs of that theorem are (i) Uhlenbeck's gauge fixing / removable
singularity theorem and (ii) the ε-regularity estimate, which produces the energy quantum
`ε₀`.  What is formalized here is the *bubbling / energy-quantization* mechanism itself,
stated for the sequence of energy densities: the energy densities of the connections are
encoded as a sequence of Borel measures `μ n` on `X` (`μ n = |F_{A n}|² dvol`), the uniform
energy bound is `μ n univ ≤ E`, and the bubbling set is the set of points at which, at every
scale, at least the energy quantum `ε₀` persists in the limit.

The theorem proved below is the resulting reduction: **the bubbling set is finite, and the
number of bubbles times the energy quantum is bounded by the total energy**, i.e. there are
at most `E / ε₀` bubbles.  This is exactly the counting statement used in the Uhlenbeck
compactness theorem to conclude that only finitely many bubbles occur.
-/

namespace Frontier

open MeasureTheory Metric Filter Set

/-- The **bubbling (energy concentration) set** of a sequence of energy measures `μ` at
quantum `ε₀`: the set of points `x` such that at *every* scale `r > 0` the balls `ball x r`
carry, in the limit inferior along the sequence, at least the energy quantum `ε₀`. -/

theorem exists_pos_radius_pairwiseDisjoint_ball {X : Type*} [MetricSpace X] (S : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑S : Set X).PairwiseDisjoint (fun x => ball x r) := by
  classical
  set P : Finset (X × X) := (S ×ˢ S).filter (fun p => p.1 ≠ p.2) with hPdef
  rcases P.eq_empty_or_nonempty with hP | hP
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have hx' : x ∈ S := hx
    have hy' : y ∈ S := hy
    have hmem : (x, y) ∈ P := by simp [hPdef, hx', hy', hxy]
    rw [hP] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · refine ⟨P.inf' hP (fun p => dist p.1 p.2) / 2, ?_, ?_⟩
    · have : 0 < P.inf' hP (fun p => dist p.1 p.2) := by
        rw [Finset.lt_inf'_iff]
        intro p hp
        have hne : p.1 ≠ p.2 := by
          rw [hPdef, Finset.mem_filter] at hp
          exact hp.2
        exact dist_pos.2 hne
      linarith
    · intro x hx y hy hxy
      have hx' : x ∈ S := hx
      have hy' : y ∈ S := hy
      have hmem : (x, y) ∈ P := by simp [hPdef, hx', hy', hxy]
      have hle : P.inf' hP (fun p => dist p.1 p.2) ≤ dist x y := Finset.inf'_le _ hmem
      exact ball_disjoint_ball (by linarith)

/-- **Energy counting for bubbles.** Any finite set of bubbling points has cardinality at
most `E / ε₀`, in the multiplicative form `card * ε₀ ≤ E`. -/
