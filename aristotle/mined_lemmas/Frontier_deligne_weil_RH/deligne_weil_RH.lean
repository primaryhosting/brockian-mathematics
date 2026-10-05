/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Cohomological data attached to a variety over a finite field `𝔽_q`:
the inverse roots (Frobenius eigenvalues) on each cohomology group, together with the
point counts over the extensions `𝔽_{q^m}`, linked by the Grothendieck–Lefschetz trace
formula. -/
structure WeilVariety where
  /-- Cardinality of the base field. -/
  q : ℕ
  /-- The base field has at least two elements. -/
  hq : 2 ≤ q
  /-- Dimension of the variety. -/
  dim : ℕ
  /-- Multiset of inverse roots of Frobenius acting on the `i`-th cohomology group. -/
  frobRoots : ℕ → Multiset ℂ
  /-- `count m` is the number of `𝔽_{q^m}`-rational points. -/
  count : ℕ → ℕ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobRoots i = 0
  /-- Grothendieck–Lefschetz trace formula. -/
  trace : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1),
        (-1) ^ i * (((frobRoots i).map (fun a => a ^ m)).sum)

/-- The Riemann hypothesis for a variety over a finite field: every inverse root of
Frobenius on the `i`-th cohomology group has archimedean absolute value `q ^ (i / 2)`. -/

theorem deligne_weil_RH :
    (∀ (q n : ℕ) (hq : 2 ≤ q), RiemannHypothesis (projectiveSpace q n hq)) ∧
    (∀ (q n m : ℕ) (hq : 2 ≤ q) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ m →
      Nat.card (Projectivization K (Fin (n + 1) → K)) = (projectiveSpace q n hq).count m) ∧
    (∀ (W : WeilVariety), RiemannHypothesis W →
      W.frobRoots (2 * W.dim) = {((W.q : ℂ)) ^ W.dim} →
      ∀ m, 1 ≤ m →
        ‖(W.count m : ℂ) - ((W.q : ℂ)) ^ (W.dim * m)‖ ≤
          (∑ i ∈ Finset.range (2 * W.dim), (Multiset.card (W.frobRoots i) : ℝ)) *
            (W.q : ℝ) ^ (((2 * W.dim - 1 : ℕ) : ℝ) * m / 2)) :=
  ⟨riemannHypothesis_projectiveSpace,
   fun q n m hq K _ _ hK => card_points_projectiveSpace q n m hq K hK,
   fun W hRH htop m hm => count_estimate_of_riemannHypothesis W hRH htop m hm⟩

end Frontier

