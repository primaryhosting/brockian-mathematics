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

lemma count_eq_sum_range (W : WeilData) (K : ℕ) (hK : 2 * W.dim + 1 ≤ K) (n : ℕ) :
    W.count n =
      ∑ i ∈ Finset.range K, (-1 : ℂ) ^ i * ((W.roots i).map (fun α : ℂ => α ^ n)).sum := by
  have hsub : Finset.range (2 * W.dim + 1) ⊆ Finset.range K := Finset.range_subset_range.mpr hK
  refine Finset.sum_subset hsub ?_
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [W.roots_eq_zero i (by omega)]
  simp

end WeilData

/-!
## The general statement (Deligne's theorem)

`DeligneWeilRH` is the statement of the Riemann hypothesis for varieties over finite fields:
for every smooth proper scheme `X` over `F_p` there is a Weil datum, with the correct base
field, computing the numbers of `F_{p^n}`-rational points and satisfying purity.
-/

open AlgebraicGeometry CategoryTheory in
/-- `#X(F_{p^n})`, the number of `F_{p^n}`-rational points of a scheme `X` over `F_p`,
i.e. the number of `F_p`-morphisms `Spec F_{p^n} ⟶ X`. -/
