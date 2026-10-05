import Mathlib
/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to come first in a file.)
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

namespace Frontier

/-!
## The Weil–Riemann hypothesis, formalized

For a smooth projective variety `X` of dimension `d` over the finite field `F_q`, the Weil
conjectures assert that the zeta function

  `Z_X(T) = exp (∑_{n ≥ 1} N_n T^n / n)`,   `N_n = #X(F_{q^n})`,

is a rational function of the shape `∏_{i=0}^{2d} P_i(T)^{(-1)^{i+1}}` where `P_i ∈ ℤ[T]`,
`P_i(0) = 1`.  Writing `P_i(T) = ∏_j (1 - α_{i,j} T)`, taking the logarithmic derivative of
the displayed identity turns the rationality statement into the point-count formula

  `N_n = ∑_{i=0}^{2d} (-1)^i ∑_j α_{i,j}^n`   for all `n ≥ 1`,

and the *Riemann hypothesis* (proved by Deligne) is the purity statement

  `|α_{i,j}| = q^{i/2}`.

`WeilData` below packages the inverse roots `α_{i,j}` (as a multiset for each cohomological
degree `i`), `WeilData.Computes` is the point-count formula, and `WeilData.RH` is purity.
-/

/-- The inverse roots of the factors `P_i` of the zeta function of a `dim`-dimensional
variety over `F_q`, one multiset for each cohomological degree `i` (empty above degree
`2 * dim`). -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The multiset of inverse roots of `P_i`, the `i`-th factor of the zeta function. -/
  roots : ℕ → Multiset ℂ
  /-- There is no cohomology above degree `2 * dim`. -/
  roots_eq_zero : ∀ i : ℕ, 2 * dim < i → roots i = 0

namespace WeilData

/-- The number `∑_{i} (-1)^i ∑_j α_{i,j}^n` predicted by the datum for `#X(F_{q^n})`. -/

theorem zeroDimensional_RH (q : ℕ) (D : Multiset ℕ) :
    ∃ W : WeilData, W.q = q ∧ W.dim = 0 ∧
      W.Computes (fun n => (D.map (fun m => if m ∣ n then m else 0)).sum) ∧ W.RH := by
  refine Multiset.induction_on D ?_ ?_
  · refine ⟨empty q, rfl, rfl, ?_, empty_RH q⟩
    intro n hn
    simpa using empty_computes q n hn
  · rintro a s ⟨W, hq, hdim, hC, hR⟩
    refine ⟨disjUnion (closedPoint q a) W, rfl, ?_, ?_, ?_⟩
    · simp [disjUnion, closedPoint, hdim]
    · intro n hn
      have h := disjUnion_computes (closedPoint_computes q a) hC n hn
      simpa [Multiset.map_cons, Multiset.sum_cons] using h
    · exact disjUnion_RH hq (closedPoint_RH q a) hR

/-- The Weil datum of projective `d`-space: `P_{2i}(T) = 1 - q^i T` and `P_{odd} = 1`. -/
