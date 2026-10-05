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

lemma sum_pow_nthRoots (m n : ℕ) :
    ((Polynomial.nthRoots m (1 : ℂ)).map (fun α : ℂ => α ^ n)).sum =
      if m ∣ n then (m : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
    rw [hζ.nthRoots_eq (a := (1 : ℂ)) (α := 1) (one_pow m), Multiset.map_map]
    have hcomp : ((Multiset.range m).map ((fun α : ℂ => α ^ n) ∘ (fun k : ℕ => ζ ^ k * 1))).sum
        = ∑ k ∈ Finset.range m, (ζ ^ n) ^ k := by
      simp [Function.comp, ← pow_mul, mul_comm]
      rfl
    rw [hcomp]
    by_cases hdvd : m ∣ n
    · have hone : ζ ^ n = 1 := by
        obtain ⟨c, rfl⟩ := hdvd
        rw [pow_mul, hζ.pow_eq_one, one_pow]
      simp [hone, hdvd]
    · have hne : ζ ^ n ≠ 1 := fun h => hdvd (hζ.dvd_of_pow_eq_one n h)
      have hpow : (ζ ^ n) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [geom_sum_eq hne, hpow]
      simp [hdvd]

/-- The Weil datum of a closed point of degree `m` (i.e. of `Spec F_{q^m}`, a zero-dimensional
variety): `P_0(T) = 1 - T^m`, whose inverse roots are the `m`-th roots of unity. -/
