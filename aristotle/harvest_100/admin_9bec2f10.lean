/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated verbatim as a module docstring just below the import
line, because Lean 4 does not allow a module docstring to precede import commands.
-/

import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

We work in the three–dimensional real Hilbert space `EuclideanSpace ℝ (Fin 3)`.
A *noncontextual hidden–variable assignment* for quantum mechanics in dimension `3`
is a function `f` which assigns to every (nonzero) vector `u` — i.e. to every rank–one
projection `|u⟩⟨u|` — a definite truth value `f u : Bool`, in such a way that for every
orthogonal triple of nonzero vectors (equivalently, for every orthogonal resolution of the
identity into three rank–one projections) *exactly one* of the three values is `true`.
The value assigned to a projection is required to depend only on the projection itself and
not on the orthogonal triple ("context") in which it is measured — this is exactly what
noncontextuality means, and it is built into the statement by letting `f` be a function of
the vector alone.

The Kochen–Specker theorem states that no such `f` exists.
-/

/-- The three–dimensional real Hilbert space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The vector of `E3` with coordinates `a`, `b`, `c`. -/
noncomputable def mk3 (a b c : ℝ) : E3 := WithLp.toLp 2 ![a, b, c]

@[simp] theorem mk3_apply0 (a b c : ℝ) : mk3 a b c 0 = a := rfl
@[simp] theorem mk3_apply1 (a b c : ℝ) : mk3 a b c 1 = b := rfl
@[simp] theorem mk3_apply2 (a b c : ℝ) : mk3 a b c 2 = c := rfl

theorem inner_expand (u v : E3) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem eq_zero_of_coords (u : E3) (h0 : u 0 = 0) (h1 : u 1 = 0) (h2 : u 2 = 0) : u = 0 := by
  ext i; fin_cases i <;> simpa using ‹_›

/-- The cross product on `E3`. -/
noncomputable def cross3 (u v : E3) : E3 :=
  mk3 (u 1 * v 2 - u 2 * v 1) (u 2 * v 0 - u 0 * v 2) (u 0 * v 1 - u 1 * v 0)

theorem inner_cross3_left (u v : E3) : ⟪u, cross3 u v⟫ = 0 := by
  rw [inner_expand]; simp [cross3]; ring

theorem inner_cross3_right (u v : E3) : ⟪v, cross3 u v⟫ = 0 := by
  rw [inner_expand]; simp [cross3]; ring

/-- The cross product of two orthogonal nonzero vectors is nonzero. -/
theorem cross3_ne_zero (u v : E3) (hu : u ≠ 0) (hv : v ≠ 0) (h : ⟪u, v⟫ = 0) :
    cross3 u v ≠ 0 := by
  intro hc
  have e0 : (cross3 u v) 0 = 0 := by rw [hc]; rfl
  have e1 : (cross3 u v) 1 = 0 := by rw [hc]; rfl
  have e2 : (cross3 u v) 2 = 0 := by rw [hc]; rfl
  simp only [cross3, mk3_apply0, mk3_apply1, mk3_apply2] at e0 e1 e2
  rw [inner_expand] at h
  have key : (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) = 0 := by
    nlinarith [e0, e1, e2, h]
  rcases mul_eq_zero.1 key with hk | hk
  · exact hu (eq_zero_of_coords u
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)])
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)])
      (by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]))
  · exact hv (eq_zero_of_coords v
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]))

/-!
## Vectors with coordinates in `ℤ[√2]`

The Kochen–Specker configuration we use (the 33 rays of Peres) has all coordinates in
`{0, ±1, ±√2}`, so we set up a small amount of exact arithmetic in `ℤ[√2]`.
-/

/-- The real number `a + b √2`. -/
noncomputable def qv (a b : ℤ) : ℝ := (a : ℝ) + (b : ℝ) * Real.sqrt 2

theorem qv_eq_zero_iff (a b : ℤ) : qv a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    by_cases hb : b = 0
    · subst hb
      simp [qv] at h
      exact ⟨by exact_mod_cast h, rfl⟩
    · exfalso
      have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.2 hb
      refine irrational_sqrt_two ⟨(-a : ℚ) / (b : ℚ), ?_⟩
      have h' : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0 := h
      push_cast
      field_simp
      linarith
  · rintro ⟨rfl, rfl⟩; simp [qv]

/-- The vector of `E3` with coordinates `a₁ + b₁√2`, `a₂ + b₂√2`, `a₃ + b₃√2`. -/
noncomputable def kvec (a1 b1 a2 b2 a3 b3 : ℤ) : E3 := mk3 (qv a1 b1) (qv a2 b2) (qv a3 b3)

theorem kvec_ne_zero (a1 b1 a2 b2 a3 b3 : ℤ)
    (h : ¬ (a1 = 0 ∧ b1 = 0) ∨ ¬ (a2 = 0 ∧ b2 = 0) ∨ ¬ (a3 = 0 ∧ b3 = 0)) :
    kvec a1 b1 a2 b2 a3 b3 ≠ 0 := by
  intro hc
  rcases h with h | h | h
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 0 = 0 := by rw [hc]; rfl
    simpa [kvec] using this
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 1 = 0 := by rw [hc]; rfl
    simpa [kvec] using this
  · refine h ((qv_eq_zero_iff _ _).1 ?_)
    have : kvec a1 b1 a2 b2 a3 b3 2 = 0 := by rw [hc]; rfl
    simpa [kvec] using this

theorem inner_kvec_eq_zero (a1 b1 a2 b2 a3 b3 c1 d1 c2 d2 c3 d3 : ℤ)
    (hA : a1 * c1 + 2 * b1 * d1 + (a2 * c2 + 2 * b2 * d2) + (a3 * c3 + 2 * b3 * d3) = 0)
    (hB : a1 * d1 + b1 * c1 + (a2 * d2 + b2 * c2) + (a3 * d3 + b3 * c3) = 0) :
    ⟪kvec a1 b1 a2 b2 a3 b3, kvec c1 d1 c2 d2 c3 d3⟫ = 0 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hA' : ((a1 : ℝ) * c1 + 2 * b1 * d1 + (a2 * c2 + 2 * b2 * d2) + (a3 * c3 + 2 * b3 * d3)) = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hA
  have hB' : ((a1 : ℝ) * d1 + b1 * c1 + (a2 * d2 + b2 * c2) + (a3 * d3 + b3 * c3)) = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hB
  rw [inner_expand]
  simp only [kvec, mk3_apply0, mk3_apply1, mk3_apply2, qv]
  linear_combination hA' + Real.sqrt 2 * hB' + ((b1 : ℝ) * d1 + (b2 : ℝ) * d2 + (b3 : ℝ) * d3) * hs

/-!
## The Kochen–Specker colouring condition
-/

/-- A *noncontextual hidden–variable assignment* (Kochen–Specker colouring) in dimension 3:
a `Bool`-valued function on nonzero vectors of `E3` such that for every orthogonal triple of
nonzero vectors exactly one of the three values is `true`. -/
def IsKSColoring (f : E3 → Bool) : Prop :=
  ∀ u v w : E3, u ≠ 0 → v ≠ 0 → w ≠ 0 → ⟪u, v⟫ = 0 → ⟪u, w⟫ = 0 → ⟪v, w⟫ = 0 →
    (f u = true ∧ f v = false ∧ f w = false) ∨
    (f u = false ∧ f v = true ∧ f w = false) ∨
    (f u = false ∧ f v = false ∧ f w = true)

/-- Two orthogonal nonzero vectors cannot both be assigned `true`. -/
theorem ks_pair {f : E3 → Bool} (hf : IsKSColoring f) {u v : E3}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : ⟪u, v⟫ = 0)
    (h1 : f u = true) (h2 : f v = true) : False := by
  have hw := cross3_ne_zero u v hu hv huv
  rcases hf u v (cross3 u v) hu hv hw huv (inner_cross3_left u v) (inner_cross3_right u v) with
    ⟨-, k, -⟩ | ⟨k, -, -⟩ | ⟨k, -, -⟩ <;> simp [h1, h2] at k

/-- In an orthogonal triple of nonzero vectors at least one vector is assigned `true`. -/
theorem ks_triple {f : E3 → Bool} (hf : IsKSColoring f) {u v w : E3}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0)
    (h1 : f u = false) (h2 : f v = false) (h3 : f w = false) : False := by
  rcases hf u v w hu hv hw huv huw hvw with ⟨k, -, -⟩ | ⟨-, k, -⟩ | ⟨-, -, k⟩ <;>
    simp [h1, h2, h3] at k

/-!
## The Peres configuration of 33 rays

The following 33 vectors have coordinates in `{0, ±1, ±√2}`; among them there are 16
orthogonal triples and 72 orthogonal pairs.  This configuration admits no
Kochen–Specker colouring.
-/

noncomputable def w0 : E3 := kvec 0 1 1 0 1 0
noncomputable def w1 : E3 := kvec 0 1 1 0 (-1) 0
noncomputable def w2 : E3 := kvec 0 1 (-1) 0 1 0
noncomputable def w3 : E3 := kvec 0 1 (-1) 0 (-1) 0
noncomputable def w4 : E3 := kvec 0 1 1 0 0 0
noncomputable def w5 : E3 := kvec 0 1 (-1) 0 0 0
noncomputable def w6 : E3 := kvec 0 1 0 0 1 0
noncomputable def w7 : E3 := kvec 0 1 0 0 (-1) 0
noncomputable def w8 : E3 := kvec 1 0 0 1 1 0
noncomputable def w9 : E3 := kvec 1 0 0 1 (-1) 0
noncomputable def w10 : E3 := kvec 1 0 0 (-1) 1 0
noncomputable def w11 : E3 := kvec 1 0 0 (-1) (-1) 0
noncomputable def w12 : E3 := kvec 1 0 0 1 0 0
noncomputable def w13 : E3 := kvec 1 0 0 (-1) 0 0
noncomputable def w14 : E3 := kvec 1 0 1 0 0 1
noncomputable def w15 : E3 := kvec 1 0 1 0 0 (-1)
noncomputable def w16 : E3 := kvec 1 0 (-1) 0 0 1
noncomputable def w17 : E3 := kvec 1 0 (-1) 0 0 (-1)
noncomputable def w18 : E3 := kvec 1 0 1 0 0 0
noncomputable def w19 : E3 := kvec 1 0 (-1) 0 0 0
noncomputable def w20 : E3 := kvec 1 0 0 0 0 1
noncomputable def w21 : E3 := kvec 1 0 0 0 0 (-1)
noncomputable def w22 : E3 := kvec 1 0 0 0 1 0
noncomputable def w23 : E3 := kvec 1 0 0 0 (-1) 0
noncomputable def w24 : E3 := kvec 1 0 0 0 0 0
noncomputable def w25 : E3 := kvec 0 0 0 1 1 0
noncomputable def w26 : E3 := kvec 0 0 0 1 (-1) 0
noncomputable def w27 : E3 := kvec 0 0 1 0 0 1
noncomputable def w28 : E3 := kvec 0 0 1 0 0 (-1)
noncomputable def w29 : E3 := kvec 0 0 1 0 1 0
noncomputable def w30 : E3 := kvec 0 0 1 0 (-1) 0
noncomputable def w31 : E3 := kvec 0 0 1 0 0 0
noncomputable def w32 : E3 := kvec 0 0 0 0 1 0

theorem w0_ne : w0 ≠ 0 := kvec_ne_zero 0 1 1 0 1 0 (by decide)
theorem w1_ne : w1 ≠ 0 := kvec_ne_zero 0 1 1 0 (-1) 0 (by decide)
theorem w2_ne : w2 ≠ 0 := kvec_ne_zero 0 1 (-1) 0 1 0 (by decide)
theorem w3_ne : w3 ≠ 0 := kvec_ne_zero 0 1 (-1) 0 (-1) 0 (by decide)
theorem w4_ne : w4 ≠ 0 := kvec_ne_zero 0 1 1 0 0 0 (by decide)
theorem w5_ne : w5 ≠ 0 := kvec_ne_zero 0 1 (-1) 0 0 0 (by decide)
theorem w6_ne : w6 ≠ 0 := kvec_ne_zero 0 1 0 0 1 0 (by decide)
theorem w7_ne : w7 ≠ 0 := kvec_ne_zero 0 1 0 0 (-1) 0 (by decide)
theorem w8_ne : w8 ≠ 0 := kvec_ne_zero 1 0 0 1 1 0 (by decide)
theorem w9_ne : w9 ≠ 0 := kvec_ne_zero 1 0 0 1 (-1) 0 (by decide)
theorem w10_ne : w10 ≠ 0 := kvec_ne_zero 1 0 0 (-1) 1 0 (by decide)
theorem w11_ne : w11 ≠ 0 := kvec_ne_zero 1 0 0 (-1) (-1) 0 (by decide)
theorem w12_ne : w12 ≠ 0 := kvec_ne_zero 1 0 0 1 0 0 (by decide)
theorem w13_ne : w13 ≠ 0 := kvec_ne_zero 1 0 0 (-1) 0 0 (by decide)
theorem w14_ne : w14 ≠ 0 := kvec_ne_zero 1 0 1 0 0 1 (by decide)
theorem w15_ne : w15 ≠ 0 := kvec_ne_zero 1 0 1 0 0 (-1) (by decide)
theorem w16_ne : w16 ≠ 0 := kvec_ne_zero 1 0 (-1) 0 0 1 (by decide)
theorem w17_ne : w17 ≠ 0 := kvec_ne_zero 1 0 (-1) 0 0 (-1) (by decide)
theorem w18_ne : w18 ≠ 0 := kvec_ne_zero 1 0 1 0 0 0 (by decide)
theorem w19_ne : w19 ≠ 0 := kvec_ne_zero 1 0 (-1) 0 0 0 (by decide)
theorem w20_ne : w20 ≠ 0 := kvec_ne_zero 1 0 0 0 0 1 (by decide)
theorem w21_ne : w21 ≠ 0 := kvec_ne_zero 1 0 0 0 0 (-1) (by decide)
theorem w22_ne : w22 ≠ 0 := kvec_ne_zero 1 0 0 0 1 0 (by decide)
theorem w23_ne : w23 ≠ 0 := kvec_ne_zero 1 0 0 0 (-1) 0 (by decide)
theorem w24_ne : w24 ≠ 0 := kvec_ne_zero 1 0 0 0 0 0 (by decide)
theorem w25_ne : w25 ≠ 0 := kvec_ne_zero 0 0 0 1 1 0 (by decide)
theorem w26_ne : w26 ≠ 0 := kvec_ne_zero 0 0 0 1 (-1) 0 (by decide)
theorem w27_ne : w27 ≠ 0 := kvec_ne_zero 0 0 1 0 0 1 (by decide)
theorem w28_ne : w28 ≠ 0 := kvec_ne_zero 0 0 1 0 0 (-1) (by decide)
theorem w29_ne : w29 ≠ 0 := kvec_ne_zero 0 0 1 0 1 0 (by decide)
theorem w30_ne : w30 ≠ 0 := kvec_ne_zero 0 0 1 0 (-1) 0 (by decide)
theorem w31_ne : w31 ≠ 0 := kvec_ne_zero 0 0 1 0 0 0 (by decide)
theorem w32_ne : w32 ≠ 0 := kvec_ne_zero 0 0 0 0 1 0 (by decide)

theorem orth_0_3 : ⟪w0, w3⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 1 0 0 1 (-1) 0 (-1) 0 (by decide) (by decide)
theorem orth_0_13 : ⟪w0, w13⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 1 0 1 0 0 (-1) 0 0 (by decide) (by decide)
theorem orth_0_21 : ⟪w0, w21⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 1 0 1 0 0 0 0 (-1) (by decide) (by decide)
theorem orth_0_30 : ⟪w0, w30⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 1 0 0 0 1 0 (-1) 0 (by decide) (by decide)
theorem orth_1_2 : ⟪w1, w2⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 (-1) 0 0 1 (-1) 0 1 0 (by decide) (by decide)
theorem orth_1_13 : ⟪w1, w13⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 (-1) 0 1 0 0 (-1) 0 0 (by decide) (by decide)
theorem orth_1_20 : ⟪w1, w20⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 (-1) 0 1 0 0 0 0 1 (by decide) (by decide)
theorem orth_1_29 : ⟪w1, w29⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 (-1) 0 0 0 1 0 1 0 (by decide) (by decide)
theorem orth_2_12 : ⟪w2, w12⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 1 0 1 0 0 1 0 0 (by decide) (by decide)
theorem orth_2_21 : ⟪w2, w21⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 1 0 1 0 0 0 0 (-1) (by decide) (by decide)
theorem orth_2_29 : ⟪w2, w29⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 1 0 0 0 1 0 1 0 (by decide) (by decide)
theorem orth_3_12 : ⟪w3, w12⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 (-1) 0 1 0 0 1 0 0 (by decide) (by decide)
theorem orth_3_20 : ⟪w3, w20⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 (-1) 0 1 0 0 0 0 1 (by decide) (by decide)
theorem orth_3_30 : ⟪w3, w30⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 (-1) 0 0 0 1 0 (-1) 0 (by decide) (by decide)
theorem orth_4_10 : ⟪w4, w10⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 0 0 1 0 0 (-1) 1 0 (by decide) (by decide)
theorem orth_4_11 : ⟪w4, w11⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 0 0 1 0 0 (-1) (-1) 0 (by decide) (by decide)
theorem orth_4_13 : ⟪w4, w13⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 0 0 1 0 0 (-1) 0 0 (by decide) (by decide)
theorem orth_4_32 : ⟪w4, w32⟫ = 0 :=
  inner_kvec_eq_zero 0 1 1 0 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_5_8 : ⟪w5, w8⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 0 0 1 0 0 1 1 0 (by decide) (by decide)
theorem orth_5_9 : ⟪w5, w9⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 0 0 1 0 0 1 (-1) 0 (by decide) (by decide)
theorem orth_5_12 : ⟪w5, w12⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 0 0 1 0 0 1 0 0 (by decide) (by decide)
theorem orth_5_32 : ⟪w5, w32⟫ = 0 :=
  inner_kvec_eq_zero 0 1 (-1) 0 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_6_15 : ⟪w6, w15⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 1 0 1 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_6_17 : ⟪w6, w17⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 1 0 1 0 (-1) 0 0 (-1) (by decide) (by decide)
theorem orth_6_21 : ⟪w6, w21⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 1 0 1 0 0 0 0 (-1) (by decide) (by decide)
theorem orth_6_31 : ⟪w6, w31⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 1 0 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_7_14 : ⟪w7, w14⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 (-1) 0 1 0 1 0 0 1 (by decide) (by decide)
theorem orth_7_16 : ⟪w7, w16⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 (-1) 0 1 0 (-1) 0 0 1 (by decide) (by decide)
theorem orth_7_20 : ⟪w7, w20⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 (-1) 0 1 0 0 0 0 1 (by decide) (by decide)
theorem orth_7_31 : ⟪w7, w31⟫ = 0 :=
  inner_kvec_eq_zero 0 1 0 0 (-1) 0 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_8_10 : ⟪w8, w10⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 1 0 1 0 0 (-1) 1 0 (by decide) (by decide)
theorem orth_8_23 : ⟪w8, w23⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 1 0 1 0 0 0 (-1) 0 (by decide) (by decide)
theorem orth_8_28 : ⟪w8, w28⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 1 0 0 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_9_11 : ⟪w9, w11⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 (-1) 0 1 0 0 (-1) (-1) 0 (by decide) (by decide)
theorem orth_9_22 : ⟪w9, w22⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 (-1) 0 1 0 0 0 1 0 (by decide) (by decide)
theorem orth_9_27 : ⟪w9, w27⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 (-1) 0 0 0 1 0 0 1 (by decide) (by decide)
theorem orth_10_23 : ⟪w10, w23⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 (-1) 1 0 1 0 0 0 (-1) 0 (by decide) (by decide)
theorem orth_10_27 : ⟪w10, w27⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 (-1) 1 0 0 0 1 0 0 1 (by decide) (by decide)
theorem orth_11_22 : ⟪w11, w22⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 (-1) (-1) 0 1 0 0 0 1 0 (by decide) (by decide)
theorem orth_11_28 : ⟪w11, w28⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 (-1) (-1) 0 0 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_12_32 : ⟪w12, w32⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 1 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_13_32 : ⟪w13, w32⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 (-1) 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_14_15 : ⟪w14, w15⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 1 1 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_14_19 : ⟪w14, w19⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 1 1 0 (-1) 0 0 0 (by decide) (by decide)
theorem orth_14_26 : ⟪w14, w26⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 1 0 0 0 1 (-1) 0 (by decide) (by decide)
theorem orth_15_19 : ⟪w15, w19⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 (-1) 1 0 (-1) 0 0 0 (by decide) (by decide)
theorem orth_15_25 : ⟪w15, w25⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 (-1) 0 0 0 1 1 0 (by decide) (by decide)
theorem orth_16_17 : ⟪w16, w17⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 1 1 0 (-1) 0 0 (-1) (by decide) (by decide)
theorem orth_16_18 : ⟪w16, w18⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 1 1 0 1 0 0 0 (by decide) (by decide)
theorem orth_16_25 : ⟪w16, w25⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 1 0 0 0 1 1 0 (by decide) (by decide)
theorem orth_17_18 : ⟪w17, w18⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 (-1) 1 0 1 0 0 0 (by decide) (by decide)
theorem orth_17_26 : ⟪w17, w26⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 (-1) 0 0 0 1 (-1) 0 (by decide) (by decide)
theorem orth_18_19 : ⟪w18, w19⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 0 1 0 (-1) 0 0 0 (by decide) (by decide)
theorem orth_18_32 : ⟪w18, w32⟫ = 0 :=
  inner_kvec_eq_zero 1 0 1 0 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_19_32 : ⟪w19, w32⟫ = 0 :=
  inner_kvec_eq_zero 1 0 (-1) 0 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_20_31 : ⟪w20, w31⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 1 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_21_31 : ⟪w21, w31⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 (-1) 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_22_23 : ⟪w22, w23⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 1 0 1 0 0 0 (-1) 0 (by decide) (by decide)
theorem orth_22_31 : ⟪w22, w31⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 1 0 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_23_31 : ⟪w23, w31⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 (-1) 0 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_24_25 : ⟪w24, w25⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 0 1 1 0 (by decide) (by decide)
theorem orth_24_26 : ⟪w24, w26⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 0 1 (-1) 0 (by decide) (by decide)
theorem orth_24_27 : ⟪w24, w27⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 1 0 0 1 (by decide) (by decide)
theorem orth_24_28 : ⟪w24, w28⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_24_29 : ⟪w24, w29⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 1 0 1 0 (by decide) (by decide)
theorem orth_24_30 : ⟪w24, w30⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 1 0 (-1) 0 (by decide) (by decide)
theorem orth_24_31 : ⟪w24, w31⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 1 0 0 0 (by decide) (by decide)
theorem orth_24_32 : ⟪w24, w32⟫ = 0 :=
  inner_kvec_eq_zero 1 0 0 0 0 0 0 0 0 0 1 0 (by decide) (by decide)
theorem orth_25_28 : ⟪w25, w28⟫ = 0 :=
  inner_kvec_eq_zero 0 0 0 1 1 0 0 0 1 0 0 (-1) (by decide) (by decide)
theorem orth_26_27 : ⟪w26, w27⟫ = 0 :=
  inner_kvec_eq_zero 0 0 0 1 (-1) 0 0 0 1 0 0 1 (by decide) (by decide)
theorem orth_29_30 : ⟪w29, w30⟫ = 0 :=
  inner_kvec_eq_zero 0 0 1 0 1 0 0 0 1 0 (-1) 0 (by decide) (by decide)
theorem orth_31_32 : ⟪w31, w32⟫ = 0 :=
  inner_kvec_eq_zero 0 0 1 0 0 0 0 0 0 0 1 0 (by decide) (by decide)

/-!
## The Kochen–Specker theorem
-/

/-- **Kochen–Specker theorem** (dimension 3).  There is no noncontextual hidden–variable
assignment for quantum mechanics in dimension `3`: no `Bool`-valued function on the vectors
of `EuclideanSpace ℝ (Fin 3)` can assign, to every orthogonal triple of nonzero vectors,
the value `true` to exactly one of its members. -/
theorem kochen_specker : ¬ ∃ f : E3 → Bool, IsKSColoring f := by
  rintro ⟨f, hf⟩
  have p_0_3 : f w0 = true → f w3 = true → False := fun h₁ h₂ =>
    ks_pair hf w0_ne w3_ne orth_0_3 h₁ h₂
  have p_0_13 : f w0 = true → f w13 = true → False := fun h₁ h₂ =>
    ks_pair hf w0_ne w13_ne orth_0_13 h₁ h₂
  have p_0_21 : f w0 = true → f w21 = true → False := fun h₁ h₂ =>
    ks_pair hf w0_ne w21_ne orth_0_21 h₁ h₂
  have p_0_30 : f w0 = true → f w30 = true → False := fun h₁ h₂ =>
    ks_pair hf w0_ne w30_ne orth_0_30 h₁ h₂
  have p_1_2 : f w1 = true → f w2 = true → False := fun h₁ h₂ =>
    ks_pair hf w1_ne w2_ne orth_1_2 h₁ h₂
  have p_1_13 : f w1 = true → f w13 = true → False := fun h₁ h₂ =>
    ks_pair hf w1_ne w13_ne orth_1_13 h₁ h₂
  have p_1_20 : f w1 = true → f w20 = true → False := fun h₁ h₂ =>
    ks_pair hf w1_ne w20_ne orth_1_20 h₁ h₂
  have p_1_29 : f w1 = true → f w29 = true → False := fun h₁ h₂ =>
    ks_pair hf w1_ne w29_ne orth_1_29 h₁ h₂
  have p_2_12 : f w2 = true → f w12 = true → False := fun h₁ h₂ =>
    ks_pair hf w2_ne w12_ne orth_2_12 h₁ h₂
  have p_2_21 : f w2 = true → f w21 = true → False := fun h₁ h₂ =>
    ks_pair hf w2_ne w21_ne orth_2_21 h₁ h₂
  have p_2_29 : f w2 = true → f w29 = true → False := fun h₁ h₂ =>
    ks_pair hf w2_ne w29_ne orth_2_29 h₁ h₂
  have p_3_12 : f w3 = true → f w12 = true → False := fun h₁ h₂ =>
    ks_pair hf w3_ne w12_ne orth_3_12 h₁ h₂
  have p_3_20 : f w3 = true → f w20 = true → False := fun h₁ h₂ =>
    ks_pair hf w3_ne w20_ne orth_3_20 h₁ h₂
  have p_3_30 : f w3 = true → f w30 = true → False := fun h₁ h₂ =>
    ks_pair hf w3_ne w30_ne orth_3_30 h₁ h₂
  have p_4_10 : f w4 = true → f w10 = true → False := fun h₁ h₂ =>
    ks_pair hf w4_ne w10_ne orth_4_10 h₁ h₂
  have p_4_11 : f w4 = true → f w11 = true → False := fun h₁ h₂ =>
    ks_pair hf w4_ne w11_ne orth_4_11 h₁ h₂
  have p_4_32 : f w4 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w4_ne w32_ne orth_4_32 h₁ h₂
  have p_5_8 : f w5 = true → f w8 = true → False := fun h₁ h₂ =>
    ks_pair hf w5_ne w8_ne orth_5_8 h₁ h₂
  have p_5_9 : f w5 = true → f w9 = true → False := fun h₁ h₂ =>
    ks_pair hf w5_ne w9_ne orth_5_9 h₁ h₂
  have p_5_32 : f w5 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w5_ne w32_ne orth_5_32 h₁ h₂
  have p_6_15 : f w6 = true → f w15 = true → False := fun h₁ h₂ =>
    ks_pair hf w6_ne w15_ne orth_6_15 h₁ h₂
  have p_6_17 : f w6 = true → f w17 = true → False := fun h₁ h₂ =>
    ks_pair hf w6_ne w17_ne orth_6_17 h₁ h₂
  have p_6_31 : f w6 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w6_ne w31_ne orth_6_31 h₁ h₂
  have p_7_14 : f w7 = true → f w14 = true → False := fun h₁ h₂ =>
    ks_pair hf w7_ne w14_ne orth_7_14 h₁ h₂
  have p_7_16 : f w7 = true → f w16 = true → False := fun h₁ h₂ =>
    ks_pair hf w7_ne w16_ne orth_7_16 h₁ h₂
  have p_7_31 : f w7 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w7_ne w31_ne orth_7_31 h₁ h₂
  have p_8_23 : f w8 = true → f w23 = true → False := fun h₁ h₂ =>
    ks_pair hf w8_ne w23_ne orth_8_23 h₁ h₂
  have p_8_28 : f w8 = true → f w28 = true → False := fun h₁ h₂ =>
    ks_pair hf w8_ne w28_ne orth_8_28 h₁ h₂
  have p_9_22 : f w9 = true → f w22 = true → False := fun h₁ h₂ =>
    ks_pair hf w9_ne w22_ne orth_9_22 h₁ h₂
  have p_9_27 : f w9 = true → f w27 = true → False := fun h₁ h₂ =>
    ks_pair hf w9_ne w27_ne orth_9_27 h₁ h₂
  have p_10_23 : f w10 = true → f w23 = true → False := fun h₁ h₂ =>
    ks_pair hf w10_ne w23_ne orth_10_23 h₁ h₂
  have p_10_27 : f w10 = true → f w27 = true → False := fun h₁ h₂ =>
    ks_pair hf w10_ne w27_ne orth_10_27 h₁ h₂
  have p_11_22 : f w11 = true → f w22 = true → False := fun h₁ h₂ =>
    ks_pair hf w11_ne w22_ne orth_11_22 h₁ h₂
  have p_11_28 : f w11 = true → f w28 = true → False := fun h₁ h₂ =>
    ks_pair hf w11_ne w28_ne orth_11_28 h₁ h₂
  have p_12_32 : f w12 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w12_ne w32_ne orth_12_32 h₁ h₂
  have p_13_32 : f w13 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w13_ne w32_ne orth_13_32 h₁ h₂
  have p_14_19 : f w14 = true → f w19 = true → False := fun h₁ h₂ =>
    ks_pair hf w14_ne w19_ne orth_14_19 h₁ h₂
  have p_14_26 : f w14 = true → f w26 = true → False := fun h₁ h₂ =>
    ks_pair hf w14_ne w26_ne orth_14_26 h₁ h₂
  have p_15_19 : f w15 = true → f w19 = true → False := fun h₁ h₂ =>
    ks_pair hf w15_ne w19_ne orth_15_19 h₁ h₂
  have p_15_25 : f w15 = true → f w25 = true → False := fun h₁ h₂ =>
    ks_pair hf w15_ne w25_ne orth_15_25 h₁ h₂
  have p_16_18 : f w16 = true → f w18 = true → False := fun h₁ h₂ =>
    ks_pair hf w16_ne w18_ne orth_16_18 h₁ h₂
  have p_16_25 : f w16 = true → f w25 = true → False := fun h₁ h₂ =>
    ks_pair hf w16_ne w25_ne orth_16_25 h₁ h₂
  have p_17_18 : f w17 = true → f w18 = true → False := fun h₁ h₂ =>
    ks_pair hf w17_ne w18_ne orth_17_18 h₁ h₂
  have p_17_26 : f w17 = true → f w26 = true → False := fun h₁ h₂ =>
    ks_pair hf w17_ne w26_ne orth_17_26 h₁ h₂
  have p_18_19 : f w18 = true → f w19 = true → False := fun h₁ h₂ =>
    ks_pair hf w18_ne w19_ne orth_18_19 h₁ h₂
  have p_18_32 : f w18 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w18_ne w32_ne orth_18_32 h₁ h₂
  have p_19_32 : f w19 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w19_ne w32_ne orth_19_32 h₁ h₂
  have p_20_31 : f w20 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w20_ne w31_ne orth_20_31 h₁ h₂
  have p_21_31 : f w21 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w21_ne w31_ne orth_21_31 h₁ h₂
  have p_22_23 : f w22 = true → f w23 = true → False := fun h₁ h₂ =>
    ks_pair hf w22_ne w23_ne orth_22_23 h₁ h₂
  have p_22_31 : f w22 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w22_ne w31_ne orth_22_31 h₁ h₂
  have p_23_31 : f w23 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w23_ne w31_ne orth_23_31 h₁ h₂
  have p_24_25 : f w24 = true → f w25 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w25_ne orth_24_25 h₁ h₂
  have p_24_26 : f w24 = true → f w26 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w26_ne orth_24_26 h₁ h₂
  have p_24_27 : f w24 = true → f w27 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w27_ne orth_24_27 h₁ h₂
  have p_24_28 : f w24 = true → f w28 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w28_ne orth_24_28 h₁ h₂
  have p_24_29 : f w24 = true → f w29 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w29_ne orth_24_29 h₁ h₂
  have p_24_30 : f w24 = true → f w30 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w30_ne orth_24_30 h₁ h₂
  have p_24_31 : f w24 = true → f w31 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w31_ne orth_24_31 h₁ h₂
  have p_24_32 : f w24 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w24_ne w32_ne orth_24_32 h₁ h₂
  have p_29_30 : f w29 = true → f w30 = true → False := fun h₁ h₂ =>
    ks_pair hf w29_ne w30_ne orth_29_30 h₁ h₂
  have p_31_32 : f w31 = true → f w32 = true → False := fun h₁ h₂ =>
    ks_pair hf w31_ne w32_ne orth_31_32 h₁ h₂
  have t_0 : f w0 = false → f w3 = false → f w30 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w0_ne w3_ne w30_ne orth_0_3 orth_0_30 orth_3_30 h₁ h₂ h₃
  have t_1 : f w1 = false → f w2 = false → f w29 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w1_ne w2_ne w29_ne orth_1_2 orth_1_29 orth_2_29 h₁ h₂ h₃
  have t_2 : f w4 = false → f w13 = false → f w32 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w4_ne w13_ne w32_ne orth_4_13 orth_4_32 orth_13_32 h₁ h₂ h₃
  have t_3 : f w5 = false → f w12 = false → f w32 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w5_ne w12_ne w32_ne orth_5_12 orth_5_32 orth_12_32 h₁ h₂ h₃
  have t_4 : f w6 = false → f w21 = false → f w31 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w6_ne w21_ne w31_ne orth_6_21 orth_6_31 orth_21_31 h₁ h₂ h₃
  have t_5 : f w7 = false → f w20 = false → f w31 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w7_ne w20_ne w31_ne orth_7_20 orth_7_31 orth_20_31 h₁ h₂ h₃
  have t_6 : f w8 = false → f w10 = false → f w23 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w8_ne w10_ne w23_ne orth_8_10 orth_8_23 orth_10_23 h₁ h₂ h₃
  have t_7 : f w9 = false → f w11 = false → f w22 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w9_ne w11_ne w22_ne orth_9_11 orth_9_22 orth_11_22 h₁ h₂ h₃
  have t_8 : f w14 = false → f w15 = false → f w19 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w14_ne w15_ne w19_ne orth_14_15 orth_14_19 orth_15_19 h₁ h₂ h₃
  have t_9 : f w16 = false → f w17 = false → f w18 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w16_ne w17_ne w18_ne orth_16_17 orth_16_18 orth_17_18 h₁ h₂ h₃
  have t_10 : f w18 = false → f w19 = false → f w32 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w18_ne w19_ne w32_ne orth_18_19 orth_18_32 orth_19_32 h₁ h₂ h₃
  have t_11 : f w22 = false → f w23 = false → f w31 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w22_ne w23_ne w31_ne orth_22_23 orth_22_31 orth_23_31 h₁ h₂ h₃
  have t_12 : f w24 = false → f w25 = false → f w28 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w24_ne w25_ne w28_ne orth_24_25 orth_24_28 orth_25_28 h₁ h₂ h₃
  have t_13 : f w24 = false → f w26 = false → f w27 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w24_ne w26_ne w27_ne orth_24_26 orth_24_27 orth_26_27 h₁ h₂ h₃
  have t_14 : f w24 = false → f w29 = false → f w30 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w24_ne w29_ne w30_ne orth_24_29 orth_24_30 orth_29_30 h₁ h₂ h₃
  have t_15 : f w24 = false → f w31 = false → f w32 = false → False := fun h₁ h₂ h₃ =>
    ks_triple hf w24_ne w31_ne w32_ne orth_24_31 orth_24_32 orth_31_32 h₁ h₂ h₃
  exact
    (Bool.dichotomy (f w24)).elim (fun h24 =>
    (Bool.dichotomy (f w31)).elim (fun h31 =>
    (Bool.dichotomy (f w32)).elim (fun h32 => t_15 h24 h31 h32) (fun h32 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w18)).elim (fun h18 =>
    (Bool.dichotomy (f w19)).elim (fun h19 =>
    (Bool.dichotomy (f w22)).elim (fun h22 =>
    (Bool.dichotomy (f w23)).elim (fun h23 => t_11 h22 h23 h31) (fun h23 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w29)).elim (fun h29 =>
    (Bool.dichotomy (f w30)).elim (fun h30 => t_14 h24 h29 h30) (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 => t_1 h1 h2 h29) (fun h2 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    t_7 h9 h11 h22
    ) (fun h11 => p_11_28 h11 h28)
    ) (fun h9 => p_9_27 h9 h27)
    )
    )
    )
    ) (fun h25 => p_16_25 h16 h25)
    ) (fun h26 => p_14_26 h14 h26)
    ) (fun h7 => p_7_14 h7 h14)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h15 => p_6_15 h6 h15)
    )
    ) (fun h21 => p_2_21 h2 h21)
    )
    ) (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    t_7 h9 h11 h22
    ) (fun h11 => p_11_28 h11 h28)
    ) (fun h9 => p_9_27 h9 h27)
    )
    )
    )
    ) (fun h26 => p_17_26 h17 h26)
    ) (fun h25 => p_15_25 h15 h25)
    ) (fun h6 => p_6_15 h6 h15)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h14 => p_7_14 h7 h14)
    )
    ) (fun h20 => p_1_20 h1 h20)
    ) (fun h2 => p_1_2 h1 h2)
    )
    ) (fun h3 => p_3_30 h3 h30)
    ) (fun h0 => p_0_30 h0 h30)
    )
    ) (fun h29 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w30)).elim (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    t_7 h9 h11 h22
    ) (fun h11 => p_11_28 h11 h28)
    ) (fun h9 => p_9_27 h9 h27)
    )
    )
    )
    ) (fun h26 => p_17_26 h17 h26)
    ) (fun h25 => p_15_25 h15 h25)
    ) (fun h6 => p_6_15 h6 h15)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h14 => p_7_14 h7 h14)
    )
    ) (fun h20 => p_3_20 h3 h20)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    t_7 h9 h11 h22
    ) (fun h11 => p_11_28 h11 h28)
    ) (fun h9 => p_9_27 h9 h27)
    )
    )
    )
    ) (fun h25 => p_16_25 h16 h25)
    ) (fun h26 => p_14_26 h14 h26)
    ) (fun h7 => p_7_14 h7 h14)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h15 => p_6_15 h6 h15)
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h30 => p_29_30 h29 h30)
    ) (fun h2 => p_2_29 h2 h29)
    ) (fun h1 => p_1_29 h1 h29)
    )
    ) (fun h10 => p_10_23 h10 h23)
    ) (fun h8 => p_8_23 h8 h23)
    )
    ) (fun h22 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w23)).elim (fun h23 =>
    (Bool.dichotomy (f w29)).elim (fun h29 =>
    (Bool.dichotomy (f w30)).elim (fun h30 => t_14 h24 h29 h30) (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 => t_1 h1 h2 h29) (fun h2 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    t_6 h8 h10 h23
    ) (fun h10 => p_10_27 h10 h27)
    ) (fun h8 => p_8_28 h8 h28)
    )
    )
    )
    ) (fun h25 => p_16_25 h16 h25)
    ) (fun h26 => p_14_26 h14 h26)
    ) (fun h7 => p_7_14 h7 h14)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h15 => p_6_15 h6 h15)
    )
    ) (fun h21 => p_2_21 h2 h21)
    )
    ) (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    t_6 h8 h10 h23
    ) (fun h10 => p_10_27 h10 h27)
    ) (fun h8 => p_8_28 h8 h28)
    )
    )
    )
    ) (fun h26 => p_17_26 h17 h26)
    ) (fun h25 => p_15_25 h15 h25)
    ) (fun h6 => p_6_15 h6 h15)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h14 => p_7_14 h7 h14)
    )
    ) (fun h20 => p_1_20 h1 h20)
    ) (fun h2 => p_1_2 h1 h2)
    )
    ) (fun h3 => p_3_30 h3 h30)
    ) (fun h0 => p_0_30 h0 h30)
    )
    ) (fun h29 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w30)).elim (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    t_6 h8 h10 h23
    ) (fun h10 => p_10_27 h10 h27)
    ) (fun h8 => p_8_28 h8 h28)
    )
    )
    )
    ) (fun h26 => p_17_26 h17 h26)
    ) (fun h25 => p_15_25 h15 h25)
    ) (fun h6 => p_6_15 h6 h15)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h14 => p_7_14 h7 h14)
    )
    ) (fun h20 => p_3_20 h3 h20)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w28)).elim (fun h28 => t_12 h24 h25 h28) (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 => t_13 h24 h26 h27) (fun h27 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    t_6 h8 h10 h23
    ) (fun h10 => p_10_27 h10 h27)
    ) (fun h8 => p_8_28 h8 h28)
    )
    )
    )
    ) (fun h25 => p_16_25 h16 h25)
    ) (fun h26 => p_14_26 h14 h26)
    ) (fun h7 => p_7_14 h7 h14)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h15 => p_6_15 h6 h15)
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h30 => p_29_30 h29 h30)
    ) (fun h2 => p_2_29 h2 h29)
    ) (fun h1 => p_1_29 h1 h29)
    )
    ) (fun h23 => p_22_23 h22 h23)
    ) (fun h11 => p_11_22 h11 h22)
    ) (fun h9 => p_9_22 h9 h22)
    )
    ) (fun h19 => p_19_32 h19 h32)
    ) (fun h18 => p_18_32 h18 h32)
    ) (fun h13 => p_13_32 h13 h32)
    ) (fun h12 => p_12_32 h12 h32)
    ) (fun h5 => p_5_32 h5 h32)
    ) (fun h4 => p_4_32 h4 h32)
    )
    ) (fun h31 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w22)).elim (fun h22 =>
    (Bool.dichotomy (f w23)).elim (fun h23 =>
    (Bool.dichotomy (f w32)).elim (fun h32 =>
    (Bool.dichotomy (f w18)).elim (fun h18 =>
    (Bool.dichotomy (f w19)).elim (fun h19 => t_10 h18 h19 h32) (fun h19 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w29)).elim (fun h29 =>
    (Bool.dichotomy (f w30)).elim (fun h30 => t_14 h24 h29 h30) (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 => t_1 h1 h2 h29) (fun h2 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    t_9 h16 h17 h18
    ) (fun h17 => p_17_26 h17 h26)
    ) (fun h16 => p_16_25 h16 h25)
    )
    )
    )
    ) (fun h28 => p_11_28 h11 h28)
    ) (fun h27 => p_10_27 h10 h27)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h9 => p_5_9 h5 h9)
    ) (fun h8 => p_5_8 h5 h8)
    )
    ) (fun h12 => p_2_12 h2 h12)
    )
    ) (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    t_9 h16 h17 h18
    ) (fun h17 => p_17_26 h17 h26)
    ) (fun h16 => p_16_25 h16 h25)
    )
    )
    )
    ) (fun h27 => p_9_27 h9 h27)
    ) (fun h28 => p_8_28 h8 h28)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h11 => p_4_11 h4 h11)
    ) (fun h10 => p_4_10 h4 h10)
    )
    ) (fun h13 => p_1_13 h1 h13)
    ) (fun h2 => p_1_2 h1 h2)
    )
    ) (fun h3 => p_3_30 h3 h30)
    ) (fun h0 => p_0_30 h0 h30)
    )
    ) (fun h29 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w30)).elim (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    t_9 h16 h17 h18
    ) (fun h17 => p_17_26 h17 h26)
    ) (fun h16 => p_16_25 h16 h25)
    )
    )
    )
    ) (fun h28 => p_11_28 h11 h28)
    ) (fun h27 => p_10_27 h10 h27)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h9 => p_5_9 h5 h9)
    ) (fun h8 => p_5_8 h5 h8)
    )
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    t_9 h16 h17 h18
    ) (fun h17 => p_17_26 h17 h26)
    ) (fun h16 => p_16_25 h16 h25)
    )
    )
    )
    ) (fun h27 => p_9_27 h9 h27)
    ) (fun h28 => p_8_28 h8 h28)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h11 => p_4_11 h4 h11)
    ) (fun h10 => p_4_10 h4 h10)
    )
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h30 => p_29_30 h29 h30)
    ) (fun h2 => p_2_29 h2 h29)
    ) (fun h1 => p_1_29 h1 h29)
    )
    ) (fun h15 => p_15_19 h15 h19)
    ) (fun h14 => p_14_19 h14 h19)
    )
    ) (fun h18 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w19)).elim (fun h19 =>
    (Bool.dichotomy (f w29)).elim (fun h29 =>
    (Bool.dichotomy (f w30)).elim (fun h30 => t_14 h24 h29 h30) (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 => t_1 h1 h2 h29) (fun h2 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    t_8 h14 h15 h19
    ) (fun h15 => p_15_25 h15 h25)
    ) (fun h14 => p_14_26 h14 h26)
    )
    )
    )
    ) (fun h28 => p_11_28 h11 h28)
    ) (fun h27 => p_10_27 h10 h27)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h9 => p_5_9 h5 h9)
    ) (fun h8 => p_5_8 h5 h8)
    )
    ) (fun h12 => p_2_12 h2 h12)
    )
    ) (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    t_8 h14 h15 h19
    ) (fun h15 => p_15_25 h15 h25)
    ) (fun h14 => p_14_26 h14 h26)
    )
    )
    )
    ) (fun h27 => p_9_27 h9 h27)
    ) (fun h28 => p_8_28 h8 h28)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h11 => p_4_11 h4 h11)
    ) (fun h10 => p_4_10 h4 h10)
    )
    ) (fun h13 => p_1_13 h1 h13)
    ) (fun h2 => p_1_2 h1 h2)
    )
    ) (fun h3 => p_3_30 h3 h30)
    ) (fun h0 => p_0_30 h0 h30)
    )
    ) (fun h29 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    (Bool.dichotomy (f w30)).elim (fun h30 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    t_8 h14 h15 h19
    ) (fun h15 => p_15_25 h15 h25)
    ) (fun h14 => p_14_26 h14 h26)
    )
    )
    )
    ) (fun h28 => p_11_28 h11 h28)
    ) (fun h27 => p_10_27 h10 h27)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h9 => p_5_9 h5 h9)
    ) (fun h8 => p_5_8 h5 h8)
    )
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w25)).elim (fun h25 => t_12 h24 h25 h28) (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 => t_13 h24 h26 h27) (fun h26 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    t_8 h14 h15 h19
    ) (fun h15 => p_15_25 h15 h25)
    ) (fun h14 => p_14_26 h14 h26)
    )
    )
    )
    ) (fun h27 => p_9_27 h9 h27)
    ) (fun h28 => p_8_28 h8 h28)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h11 => p_4_11 h4 h11)
    ) (fun h10 => p_4_10 h4 h10)
    )
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h30 => p_29_30 h29 h30)
    ) (fun h2 => p_2_29 h2 h29)
    ) (fun h1 => p_1_29 h1 h29)
    )
    ) (fun h19 => p_18_19 h18 h19)
    ) (fun h17 => p_17_18 h17 h18)
    ) (fun h16 => p_16_18 h16 h18)
    )
    ) (fun h32 => p_31_32 h31 h32)
    ) (fun h23 => p_23_31 h23 h31)
    ) (fun h22 => p_22_31 h22 h31)
    ) (fun h21 => p_21_31 h21 h31)
    ) (fun h20 => p_20_31 h20 h31)
    ) (fun h7 => p_7_31 h7 h31)
    ) (fun h6 => p_6_31 h6 h31)
    )
    ) (fun h24 =>
    (Bool.dichotomy (f w25)).elim (fun h25 =>
    (Bool.dichotomy (f w26)).elim (fun h26 =>
    (Bool.dichotomy (f w27)).elim (fun h27 =>
    (Bool.dichotomy (f w28)).elim (fun h28 =>
    (Bool.dichotomy (f w29)).elim (fun h29 =>
    (Bool.dichotomy (f w30)).elim (fun h30 =>
    (Bool.dichotomy (f w31)).elim (fun h31 =>
    (Bool.dichotomy (f w32)).elim (fun h32 =>
    (Bool.dichotomy (f w18)).elim (fun h18 =>
    (Bool.dichotomy (f w19)).elim (fun h19 => t_10 h18 h19 h32) (fun h19 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w22)).elim (fun h22 =>
    (Bool.dichotomy (f w23)).elim (fun h23 => t_11 h22 h23 h31) (fun h23 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_21 h2 h21)
    ) (fun h1 => p_1_13 h1 h13)
    )
    )
    ) (fun h6 => p_6_17 h6 h17)
    ) (fun h4 => p_4_11 h4 h11)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h9 => p_5_9 h5 h9)
    )
    )
    ) (fun h20 => p_3_20 h3 h20)
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_12 h2 h12)
    ) (fun h1 => p_1_20 h1 h20)
    )
    )
    ) (fun h7 => p_7_16 h7 h16)
    ) (fun h5 => p_5_9 h5 h9)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h11 => p_4_11 h4 h11)
    )
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h10 => p_10_23 h10 h23)
    ) (fun h8 => p_8_23 h8 h23)
    )
    ) (fun h22 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w23)).elim (fun h23 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w17)).elim (fun h17 => t_9 h16 h17 h18) (fun h17 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_21 h2 h21)
    ) (fun h1 => p_1_13 h1 h13)
    )
    )
    ) (fun h6 => p_6_17 h6 h17)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h16 => p_7_16 h7 h16)
    ) (fun h8 => p_5_8 h5 h8)
    )
    )
    ) (fun h20 => p_3_20 h3 h20)
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w16)).elim (fun h16 => t_9 h16 h17 h18) (fun h16 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_12 h2 h12)
    ) (fun h1 => p_1_20 h1 h20)
    )
    )
    ) (fun h7 => p_7_16 h7 h16)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h17 => p_6_17 h6 h17)
    ) (fun h10 => p_4_10 h4 h10)
    )
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h23 => p_22_23 h22 h23)
    ) (fun h11 => p_11_22 h11 h22)
    ) (fun h9 => p_9_22 h9 h22)
    )
    ) (fun h15 => p_15_19 h15 h19)
    ) (fun h14 => p_14_19 h14 h19)
    )
    ) (fun h18 =>
    (Bool.dichotomy (f w16)).elim (fun h16 =>
    (Bool.dichotomy (f w17)).elim (fun h17 =>
    (Bool.dichotomy (f w19)).elim (fun h19 =>
    (Bool.dichotomy (f w22)).elim (fun h22 =>
    (Bool.dichotomy (f w23)).elim (fun h23 => t_11 h22 h23 h31) (fun h23 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w11)).elim (fun h11 => t_7 h9 h11 h22) (fun h11 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_21 h2 h21)
    ) (fun h1 => p_1_13 h1 h13)
    )
    )
    ) (fun h6 => p_6_15 h6 h15)
    ) (fun h4 => p_4_11 h4 h11)
    )
    )
    ) (fun h14 => p_7_14 h7 h14)
    ) (fun h9 => p_5_9 h5 h9)
    )
    )
    ) (fun h20 => p_3_20 h3 h20)
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w9)).elim (fun h9 => t_7 h9 h11 h22) (fun h9 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_12 h2 h12)
    ) (fun h1 => p_1_20 h1 h20)
    )
    )
    ) (fun h7 => p_7_14 h7 h14)
    ) (fun h5 => p_5_9 h5 h9)
    )
    )
    ) (fun h15 => p_6_15 h6 h15)
    ) (fun h11 => p_4_11 h4 h11)
    )
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h10 => p_10_23 h10 h23)
    ) (fun h8 => p_8_23 h8 h23)
    )
    ) (fun h22 =>
    (Bool.dichotomy (f w9)).elim (fun h9 =>
    (Bool.dichotomy (f w11)).elim (fun h11 =>
    (Bool.dichotomy (f w23)).elim (fun h23 =>
    (Bool.dichotomy (f w0)).elim (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 => t_0 h0 h3 h30) (fun h3 =>
    (Bool.dichotomy (f w12)).elim (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 =>
    (Bool.dichotomy (f w5)).elim (fun h5 => t_3 h5 h12 h32) (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 => t_5 h7 h20 h31) (fun h7 =>
    (Bool.dichotomy (f w8)).elim (fun h8 =>
    (Bool.dichotomy (f w14)).elim (fun h14 =>
    (Bool.dichotomy (f w10)).elim (fun h10 => t_6 h8 h10 h23) (fun h10 =>
    (Bool.dichotomy (f w15)).elim (fun h15 => t_8 h14 h15 h19) (fun h15 =>
    (Bool.dichotomy (f w4)).elim (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 =>
    (Bool.dichotomy (f w13)).elim (fun h13 => t_2 h4 h13 h32) (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 => t_4 h6 h21 h31) (fun h21 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_21 h2 h21)
    ) (fun h1 => p_1_13 h1 h13)
    )
    )
    ) (fun h6 => p_6_15 h6 h15)
    ) (fun h4 => p_4_10 h4 h10)
    )
    )
    ) (fun h14 => p_7_14 h7 h14)
    ) (fun h8 => p_5_8 h5 h8)
    )
    )
    ) (fun h20 => p_3_20 h3 h20)
    ) (fun h12 => p_3_12 h3 h12)
    )
    ) (fun h0 =>
    (Bool.dichotomy (f w3)).elim (fun h3 =>
    (Bool.dichotomy (f w13)).elim (fun h13 =>
    (Bool.dichotomy (f w21)).elim (fun h21 =>
    (Bool.dichotomy (f w4)).elim (fun h4 => t_2 h4 h13 h32) (fun h4 =>
    (Bool.dichotomy (f w6)).elim (fun h6 => t_4 h6 h21 h31) (fun h6 =>
    (Bool.dichotomy (f w10)).elim (fun h10 =>
    (Bool.dichotomy (f w15)).elim (fun h15 =>
    (Bool.dichotomy (f w8)).elim (fun h8 => t_6 h8 h10 h23) (fun h8 =>
    (Bool.dichotomy (f w14)).elim (fun h14 => t_8 h14 h15 h19) (fun h14 =>
    (Bool.dichotomy (f w5)).elim (fun h5 =>
    (Bool.dichotomy (f w7)).elim (fun h7 =>
    (Bool.dichotomy (f w12)).elim (fun h12 => t_3 h5 h12 h32) (fun h12 =>
    (Bool.dichotomy (f w20)).elim (fun h20 => t_5 h7 h20 h31) (fun h20 =>
    (Bool.dichotomy (f w1)).elim (fun h1 =>
    (Bool.dichotomy (f w2)).elim (fun h2 =>
    t_1 h1 h2 h29
    ) (fun h2 => p_2_12 h2 h12)
    ) (fun h1 => p_1_20 h1 h20)
    )
    )
    ) (fun h7 => p_7_14 h7 h14)
    ) (fun h5 => p_5_8 h5 h8)
    )
    )
    ) (fun h15 => p_6_15 h6 h15)
    ) (fun h10 => p_4_10 h4 h10)
    )
    )
    ) (fun h21 => p_0_21 h0 h21)
    ) (fun h13 => p_0_13 h0 h13)
    ) (fun h3 => p_0_3 h0 h3)
    )
    ) (fun h23 => p_22_23 h22 h23)
    ) (fun h11 => p_11_22 h11 h22)
    ) (fun h9 => p_9_22 h9 h22)
    )
    ) (fun h19 => p_18_19 h18 h19)
    ) (fun h17 => p_17_18 h17 h18)
    ) (fun h16 => p_16_18 h16 h18)
    )
    ) (fun h32 => p_24_32 h24 h32)
    ) (fun h31 => p_24_31 h24 h31)
    ) (fun h30 => p_24_30 h24 h30)
    ) (fun h29 => p_24_29 h24 h29)
    ) (fun h28 => p_24_28 h24 h28)
    ) (fun h27 => p_24_27 h24 h27)
    ) (fun h26 => p_24_26 h24 h26)
    ) (fun h25 => p_24_25 h24 h25)
    )

end Frontier

