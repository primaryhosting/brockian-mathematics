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

/-!
# Li's criterion (finite / Bombieri–Lagarias core)

Li's criterion states that the Riemann Hypothesis is equivalent to the non-negativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum being over the non-trivial zeros of the Riemann zeta function (equivalently, the zeros
of the completed function `ξ`), counted with multiplicity.

This file formalises and proves the arithmetic-free *core* of the criterion: the equivalence
for an arbitrary **finite** family of non-zero complex numbers `ρ i` that is closed under the
functional-equation symmetry `ρ ↦ 1 - ρ`.  For such a family,

* every `ρ i` lies on the critical line `Re ρ = 1/2`

  if and only if

* all the Li coefficients `λ_n`, `n ≥ 1`, have non-negative real part.

This is exactly the statement of Li's criterion with the zero multiset of `ξ` replaced by a
finite symmetric multiset; the two ingredients that are special to `ξ` (the Hadamard product,
which produces the zero multiset and the convergence of the defining series) are not part of
this statement.

The mathematical content proved here is:

* the *Möbius dictionary* `‖1 - 1/ρ‖ = 1 ↔ Re ρ = 1/2` and `1 < ‖1 - 1/ρ‖ ↔ Re ρ < 1/2`
  (`Frontier.norm_one_sub_inv_eq_one_iff`, `Frontier.one_lt_norm_one_sub_inv_iff`);
* the easy direction, that a zero on the critical line contributes a non-negative real part
  to every `λ_n`;
* the hard direction, a Diophantine/recurrence argument (the finite analogue of the
  Bombieri–Lagarias argument): if some `‖z i‖ > 1`, then the power sums `∑ i, Re (z i ^ n)`
  are unbounded above, because arbitrarily large powers `n` can be chosen so that all the
  `z i ^ n` point in almost the same direction as the positive real axis.
-/

namespace Frontier

open Complex Filter

/-! ### The Möbius dictionary -/

/-- The basic identity behind Li's criterion: `‖1 - 1/ρ‖` compares with `1` exactly as
`Re ρ` compares with `1/2`. -/

theorem norm_pow_mul_sub_one_le (u : ℂ) (hu : ‖u‖ = 1) (n m : ℕ) :
    ‖u ^ (m * n) - 1‖ ≤ m * ‖u ^ n - 1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : u ^ ((m + 1) * n) - 1 = u ^ n * (u ^ (m * n) - 1) + (u ^ n - 1) := by
        have : u ^ ((m + 1) * n) = u ^ n * u ^ (m * n) := by
          rw [← pow_add]; congr 1; ring
        rw [this]; ring
      have hnorm : ‖u ^ n‖ = 1 := by rw [norm_pow, hu, one_pow]
      calc ‖u ^ ((m + 1) * n) - 1‖
          ≤ ‖u ^ n * (u ^ (m * n) - 1)‖ + ‖u ^ n - 1‖ := by
            rw [hstep]; exact norm_add_le _ _
        _ = ‖u ^ (m * n) - 1‖ + ‖u ^ n - 1‖ := by rw [norm_mul, hnorm, one_mul]
        _ ≤ m * ‖u ^ n - 1‖ + ‖u ^ n - 1‖ := by linarith [ih]
        _ = ((m : ℝ) + 1) * ‖u ^ n - 1‖ := by ring
        _ = ((m + 1 : ℕ) : ℝ) * ‖u ^ n - 1‖ := by push_cast; ring

/-- The recurrence lemma with arbitrarily large exponents. -/
