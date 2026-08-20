/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every doc comment, so the header above is
-- written as a plain block comment and repeated verbatim as the module doc comment below.)

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace Math2

open MvPolynomial

/-! ## Setup

We work with the affine plane curves `y ^ a = x ^ b` over a field `k` of characteristic
zero, given by the polynomial `curve k a b = Y ^ a - X ^ b` in `MvPolynomial (Fin 2) k`
(`X = X 0`, `Y = X 1`).  These are exactly the singularities resolved by the classical
Euclidean/continued-fraction sequence of point blowups.

Blowing up the origin of the affine plane is covered by two charts:

* the `x`-chart, `(x, y) ↦ (x, x * y)`;
* the `y`-chart, `(x, y) ↦ (x * y, y)`.

The *total transform* of a curve `p` is its pullback along one of these substitutions; the
*strict transform* is obtained by removing the largest possible power of the exceptional
divisor (`x`, resp. `y`) from the total transform.  This is the content of `BlowupStep`.
-/

/-- The plane curve `y ^ a = x ^ b`, as the polynomial `Y ^ a - X ^ b`. -/
noncomputable def curve (k : Type*) [Field k] (a b : ℕ) : MvPolynomial (Fin 2) k :=
  (X 1) ^ a - (X 0) ^ b

/-- The substitution defining the `x`-chart of the blowup of the origin: `(x, y) ↦ (x, x*y)`. -/
noncomputable def xchart (k : Type*) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0, X 0 * X 1]

/-- The substitution defining the `y`-chart of the blowup of the origin: `(x, y) ↦ (x*y, y)`. -/
noncomputable def ychart (k : Type*) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 * X 1, X 1]

/-- `q` is the strict transform of `p` in one of the two charts of the blowup of the origin:
the pullback of `p` factors as (a power of the exceptional divisor) times `q`, and `q` is
no longer divisible by the exceptional divisor. -/
def BlowupStep {k : Type*} [Field k] (p q : MvPolynomial (Fin 2) k) : Prop :=
  (∃ e : ℕ, xchart k p = (X 0) ^ e * q ∧ ¬ (X 0 ∣ q)) ∨
  (∃ e : ℕ, ychart k p = (X 1) ^ e * q ∧ ¬ (X 1 ∣ q))

/-- The origin is not a singular point of the affine scheme `f = 0`: either the origin does
not lie on it, or the differential of `f` at the origin is nonzero (so that, by the Jacobian
criterion, `f = 0` is smooth of dimension one at the origin). -/
def SmoothAtOrigin {k : Type*} [Field k] (f : MvPolynomial (Fin 2) k) : Prop :=
  eval 0 f ≠ 0 ∨ eval 0 (pderiv 0 f) ≠ 0 ∨ eval 0 (pderiv 1 f) ≠ 0

/-! ## Non-divisibility criteria -/

theorem not_dvd_X_zero {k : Type*} [Field k] (q : MvPolynomial (Fin 2) k) (t : k)
    (h : eval ![0, t] q ≠ 0) : ¬ (X (0 : Fin 2) ∣ q) := by
  rintro ⟨r, rfl⟩
  apply h
  simp

theorem not_dvd_X_one {k : Type*} [Field k] (q : MvPolynomial (Fin 2) k) (t : k)
    (h : eval ![t, 0] q ≠ 0) : ¬ (X (1 : Fin 2) ∣ q) := by
  rintro ⟨r, rfl⟩
  apply h
  simp

/-! ## The two blowup steps: the Euclidean algorithm on exponents -/

/-- In the `x`-chart, the strict transform of `y ^ a = x ^ b` (with `1 ≤ a ≤ b`) is
`y ^ a = x ^ (b - a)`. -/
theorem blowupStep_x {k : Type*} [Field k] {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    BlowupStep (curve k a b) (curve k a (b - a)) := by
  left
  refine ⟨a, ?_, ?_⟩
  · have hb : b = a + (b - a) := by omega
    simp only [xchart, curve, map_sub, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_pow]
    rw [mul_sub]
    congr 1
    rw [← pow_add, ← hb]
  · rcases Nat.eq_or_lt_of_le hab with h | h
    · -- `b = a`, strict transform is `y ^ a - 1`
      apply not_dvd_X_zero _ (0 : k)
      have : b - a = 0 := by omega
      simp [curve, this, zero_pow (by omega : a ≠ 0)]
    · apply not_dvd_X_zero _ (1 : k)
      have hba : b - a ≠ 0 := by omega
      simp [curve, zero_pow hba]

/-- In the `y`-chart, the strict transform of `y ^ a = x ^ b` (with `b < a`) is
`y ^ (a - b) = x ^ b`. -/
theorem blowupStep_y {k : Type*} [Field k] {a b : ℕ} (hba : b < a) :
    BlowupStep (curve k a b) (curve k (a - b) b) := by
  right
  refine ⟨b, ?_, ?_⟩
  · have ha : a = b + (a - b) := by omega
    simp only [ychart, curve, map_sub, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_pow]
    rw [mul_sub, ← pow_add, ← ha]
    ring
  · apply not_dvd_X_one _ (1 : k)
    simp [curve, zero_pow (by omega : a - b ≠ 0)]

/-! ## Smoothness of the terminal curves -/

theorem smoothAtOrigin_curve_zero {k : Type*} [Field k] {a : ℕ} (ha : 1 ≤ a) :
    SmoothAtOrigin (curve k a 0) := by
  left
  simp [curve, zero_pow (by omega : a ≠ 0)]

theorem smoothAtOrigin_curve_zero_left {k : Type*} [Field k] {b : ℕ} (hb : 1 ≤ b) :
    SmoothAtOrigin (curve k 0 b) := by
  left
  simp [curve, zero_pow (by omega : b ≠ 0)]

theorem smoothAtOrigin_curve_one_left {k : Type*} [Field k] (b : ℕ) :
    SmoothAtOrigin (curve k 1 b) := by
  right; right
  simp [curve]

theorem smoothAtOrigin_curve_one_right {k : Type*} [Field k] (a : ℕ) :
    SmoothAtOrigin (curve k a 1) := by
  right; left
  simp [curve]

/-! ## Main theorem -/

/-- **Resolution of singularities for the plane curves `y ^ a = x ^ b`** (a special case of
Hironaka's theorem on resolution of singularities in characteristic zero).

For every pair of positive exponents `a, b`, a finite sequence of point blowups of the affine
plane transforms the curve `y ^ a = x ^ b` into a curve which is smooth at the origin: at each
step one passes to the strict transform in one of the two standard charts of the blowup of the
origin (`BlowupStep`), and the process terminates because it realises the Euclidean algorithm
on the pair of exponents.

The hypothesis `CharZero k` is included because Hironaka's theorem is a characteristic-zero
statement; it is not needed for this special case. -/
theorem hironaka_resolution (k : Type*) [Field k] [CharZero k] (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ q : MvPolynomial (Fin 2) k,
      Relation.ReflTransGen BlowupStep (curve k a b) q ∧ SmoothAtOrigin q := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n IH =>
    subst hn
    rcases eq_or_lt_of_le ha with h1 | h1
    · exact ⟨curve k a b, Relation.ReflTransGen.refl, h1 ▸ smoothAtOrigin_curve_one_left b⟩
    rcases eq_or_lt_of_le hb with h2 | h2
    · exact ⟨curve k a b, Relation.ReflTransGen.refl, h2 ▸ smoothAtOrigin_curve_one_right a⟩
    -- now `2 ≤ a` and `2 ≤ b`
    by_cases hab : a ≤ b
    · rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · refine ⟨curve k a (a - a), Relation.ReflTransGen.single (blowupStep_x ha le_rfl), ?_⟩
        simpa [Nat.sub_self] using smoothAtOrigin_curve_zero (k := k) ha
      · obtain ⟨q, hq, hq'⟩ := IH (a + (b - a)) (by omega) a (b - a) ha (by omega) rfl
        exact ⟨q, Relation.ReflTransGen.head (blowupStep_x ha hab) hq, hq'⟩
    · obtain ⟨q, hq, hq'⟩ := IH ((a - b) + b) (by omega) (a - b) b (by omega) hb rfl
      exact ⟨q, Relation.ReflTransGen.head (blowupStep_y (by omega)) hq, hq'⟩

/-- The resolution statement for every exponent pair except `(0, 0)` (for which `curve k 0 0`
is the zero polynomial, not a curve).  If one of the exponents vanishes the curve misses the
origin already; otherwise this is `hironaka_resolution`. -/
theorem hironaka_resolution_of_ne_zero (k : Type*) [Field k] [CharZero k] (a b : ℕ)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ q : MvPolynomial (Fin 2) k,
      Relation.ReflTransGen BlowupStep (curve k a b) q ∧ SmoothAtOrigin q := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : 1 ≤ b := by omega
    exact ⟨curve k 0 b, Relation.ReflTransGen.refl, smoothAtOrigin_curve_zero_left hb⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact ⟨curve k a 0, Relation.ReflTransGen.refl, smoothAtOrigin_curve_zero ha⟩
  · exact hironaka_resolution k a b ha hb

/-- A worked instance: one blowup resolves the cuspidal curve `y ^ 2 = x ^ 3`, whose strict
transform in the `x`-chart is the smooth curve `y ^ 2 = x`. -/
theorem cusp_resolution :
    BlowupStep (curve ℚ 2 3) (curve ℚ 2 1) ∧ SmoothAtOrigin (curve ℚ 2 1) :=
  ⟨by simpa using blowupStep_x (k := ℚ) (a := 2) (b := 3) (by norm_num) (by norm_num),
    smoothAtOrigin_curve_one_right 2⟩

end Math2

#print axioms Math2.hironaka_resolution
#print axioms Math2.hironaka_resolution_of_ne_zero
#print axioms Math2.cusp_resolution

