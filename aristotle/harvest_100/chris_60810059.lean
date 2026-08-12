import Mathlib

set_option maxHeartbeats 1000000

/-!
# Common machinery for the Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system with Hilbert space `E`
assigns to every unit vector (equivalently, to every rank-one projection, i.e. to every
"yes/no question" about the system) a definite truth value, in a way that does not depend on
the context in which the corresponding measurement is performed, and which respects the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections — that is, in every orthonormal basis — exactly one projection is assigned the
value `true`.

We model such an assignment by a function `f : E → Bool`, the sum rule being the hypothesis
`∀ b : Fin n → E, Orthonormal ℝ b → ∃! i, f (b i) = true` (in an `n`-dimensional space an
orthonormal family indexed by `Fin n` is exactly an orthonormal basis).

This file collects the pieces used in dimensions three and four.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- "Exactly one `true`" in a triple, expressed as a count. -/
lemma ks_count3 {E : Type*} (f : E → Bool) (u : Fin 3 → E) (h : ∃! i, f (u i) = true) :
    (f (u 0)).toNat + (f (u 1)).toNat + (f (u 2)).toNat = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j, j ≠ i → f (u j) = false := by
    intro j hj
    by_contra hc
    exact hj (hu j (by simpa using hc))
  fin_cases i <;> simp_all

/-- "Exactly one `true`" in a quadruple, expressed as a count. -/
lemma ks_count4 {E : Type*} (f : E → Bool) (u : Fin 4 → E) (h : ∃! i, f (u i) = true) :
    (f (u 0)).toNat + (f (u 1)).toNat + (f (u 2)).toNat + (f (u 3)).toNat = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j, j ≠ i → f (u j) = false := by
    intro j hj
    by_contra hc
    exact hj (hu j (by simpa using hc))
  fin_cases i <;> simp_all

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalisation of a vector (the zero vector is mapped to itself). -/
noncomputable def nrm (w : E) : E := ‖w‖⁻¹ • w

/-- Normalising a family of pairwise orthogonal nonzero vectors gives an orthonormal family. -/
lemma orthonormal_nrm {ι : Type*} (v : ι → E) (hne : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : Orthonormal ℝ (fun i => nrm (v i)) := by
  constructor
  · intro i
    simpa [nrm] using norm_smul_inv_norm (𝕜 := ℝ) (hne i)
  · intro i j hij
    simp [nrm, real_inner_smul_left, real_inner_smul_right, ho i j hij]

end Frontier

import RequestProject.KSCore

/-!
# Kochen–Specker in dimension three (Peres' 33 rays)

This file rules out a noncontextual `{0,1}`-valued assignment on the unit vectors of `ℝ³`.
The configuration used is Peres' set of 33 rays, whose coordinates are `0, ±1, ±√2`.
Thirteen of the orthogonal triples of the configuration must each carry exactly one `true`,
and 33 further orthogonal pairs of rays cannot both carry `true` (any orthogonal pair extends,
via the cross product, to an orthogonal triple).  These 46 constraints are contradictory.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- Three-dimensional real Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The real inner product on `E3`, in coordinates. -/
lemma inner_e3 (x y : E3) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

lemma inner_vec3 (a b c a' b' c' : ℝ) :
    ⟪(!₂[a, b, c] : E3), !₂[a', b', c']⟫ = a * a' + b * b' + c * c' := by
  rw [inner_e3]; simp

/-- The cross product on `E3`. -/
noncomputable def cr (u v : E3) : E3 :=
  !₂[u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

lemma cr_apply (u v : E3) : (cr u v) 0 = u 1 * v 2 - u 2 * v 1 ∧
    (cr u v) 1 = u 2 * v 0 - u 0 * v 2 ∧ (cr u v) 2 = u 0 * v 1 - u 1 * v 0 := ⟨rfl, rfl, rfl⟩

lemma inner_cr_left (u v : E3) : ⟪u, cr u v⟫ = 0 := by
  rw [inner_e3, (cr_apply u v).1, (cr_apply u v).2.1, (cr_apply u v).2.2]; ring

lemma inner_cr_right (u v : E3) : ⟪v, cr u v⟫ = 0 := by
  rw [inner_e3, (cr_apply u v).1, (cr_apply u v).2.1, (cr_apply u v).2.2]; ring

/-- Lagrange's identity for the cross product. -/
lemma inner_cr_self (u v : E3) : ⟪cr u v, cr u v⟫ = ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  rw [inner_e3 (cr u v), inner_e3 u u, inner_e3 v v, inner_e3 u v,
    (cr_apply u v).1, (cr_apply u v).2.1, (cr_apply u v).2.2]; ring

/-- The counting relation attached to an orthogonal triple of nonzero vectors. -/
lemma ks_ctx3 (f : E3 → Bool)
    (h : ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, f (b i) = true)
    (w0 w1 w2 : E3)
    (n0 : ⟪w0, w0⟫ ≠ 0) (n1 : ⟪w1, w1⟫ ≠ 0) (n2 : ⟪w2, w2⟫ ≠ 0)
    (h01 : ⟪w0, w1⟫ = 0) (h02 : ⟪w0, w2⟫ = 0) (h12 : ⟪w1, w2⟫ = 0) :
    (f (nrm w0)).toNat + (f (nrm w1)).toNat + (f (nrm w2)).toNat = 1 := by
  have hon : Orthonormal ℝ (fun i => nrm (![w0, w1, w2] i)) := by
    apply orthonormal_nrm
    · intro i; fin_cases i <;> intro hz <;> simp_all
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  simpa using ks_count3 f _ (h _ hon)

/-- Two orthogonal nonzero vectors of `ℝ³` cannot both be assigned `true`: complete them
to an orthogonal triple using the cross product. -/
lemma ks_pair3 (f : E3 → Bool)
    (h : ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, f (b i) = true)
    (w0 w1 : E3) (n0 : ⟪w0, w0⟫ ≠ 0) (n1 : ⟪w1, w1⟫ ≠ 0) (h01 : ⟪w0, w1⟫ = 0) :
    (f (nrm w0)).toNat + (f (nrm w1)).toNat ≤ 1 := by
  have h2 : ⟪cr w0 w1, cr w0 w1⟫ ≠ 0 := by
    rw [inner_cr_self, h01]
    simpa using mul_ne_zero n0 n1
  have := ks_ctx3 f h w0 w1 (cr w0 w1) n0 n1 h2 h01 (inner_cr_left w0 w1) (inner_cr_right w0 w1)
  omega

/-- `√2`. -/
noncomputable def s2 : ℝ := Real.sqrt 2

lemma s2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-! ### Peres' 33 rays -/

/-- Ray 0 of the Peres configuration. -/
noncomputable def r0 : E3 := !₂[0, 0, 1]
/-- Ray 1 of the Peres configuration. -/
noncomputable def r1 : E3 := !₂[0, 1, -1]
/-- Ray 2 of the Peres configuration. -/
noncomputable def r2 : E3 := !₂[0, 1, -s2]
/-- Ray 3 of the Peres configuration. -/
noncomputable def r3 : E3 := !₂[0, s2, -1]
/-- Ray 4 of the Peres configuration. -/
noncomputable def r4 : E3 := !₂[0, 1, 0]
/-- Ray 5 of the Peres configuration. -/
noncomputable def r5 : E3 := !₂[0, s2, 1]
/-- Ray 6 of the Peres configuration. -/
noncomputable def r6 : E3 := !₂[0, 1, s2]
/-- Ray 7 of the Peres configuration. -/
noncomputable def r7 : E3 := !₂[0, 1, 1]
/-- Ray 8 of the Peres configuration. -/
noncomputable def r8 : E3 := !₂[1, -1, -s2]
/-- Ray 9 of the Peres configuration. -/
noncomputable def r9 : E3 := !₂[1, -1, 0]
/-- Ray 10 of the Peres configuration. -/
noncomputable def r10 : E3 := !₂[1, -1, s2]
/-- Ray 11 of the Peres configuration. -/
noncomputable def r11 : E3 := !₂[1, -s2, -1]
/-- Ray 12 of the Peres configuration. -/
noncomputable def r12 : E3 := !₂[1, -s2, 0]
/-- Ray 13 of the Peres configuration. -/
noncomputable def r13 : E3 := !₂[1, -s2, 1]
/-- Ray 14 of the Peres configuration. -/
noncomputable def r14 : E3 := !₂[s2, -1, -1]
/-- Ray 15 of the Peres configuration. -/
noncomputable def r15 : E3 := !₂[s2, -1, 0]
/-- Ray 16 of the Peres configuration. -/
noncomputable def r16 : E3 := !₂[s2, -1, 1]
/-- Ray 17 of the Peres configuration. -/
noncomputable def r17 : E3 := !₂[1, 0, -1]
/-- Ray 18 of the Peres configuration. -/
noncomputable def r18 : E3 := !₂[1, 0, -s2]
/-- Ray 19 of the Peres configuration. -/
noncomputable def r19 : E3 := !₂[s2, 0, -1]
/-- Ray 20 of the Peres configuration. -/
noncomputable def r20 : E3 := !₂[1, 0, 0]
/-- Ray 21 of the Peres configuration. -/
noncomputable def r21 : E3 := !₂[s2, 0, 1]
/-- Ray 22 of the Peres configuration. -/
noncomputable def r22 : E3 := !₂[1, 0, s2]
/-- Ray 23 of the Peres configuration. -/
noncomputable def r23 : E3 := !₂[1, 0, 1]
/-- Ray 24 of the Peres configuration. -/
noncomputable def r24 : E3 := !₂[s2, 1, -1]
/-- Ray 25 of the Peres configuration. -/
noncomputable def r25 : E3 := !₂[s2, 1, 0]
/-- Ray 26 of the Peres configuration. -/
noncomputable def r26 : E3 := !₂[s2, 1, 1]
/-- Ray 27 of the Peres configuration. -/
noncomputable def r27 : E3 := !₂[1, s2, -1]
/-- Ray 28 of the Peres configuration. -/
noncomputable def r28 : E3 := !₂[1, s2, 0]
/-- Ray 29 of the Peres configuration. -/
noncomputable def r29 : E3 := !₂[1, s2, 1]
/-- Ray 30 of the Peres configuration. -/
noncomputable def r30 : E3 := !₂[1, 1, -s2]
/-- Ray 31 of the Peres configuration. -/
noncomputable def r31 : E3 := !₂[1, 1, 0]
/-- Ray 32 of the Peres configuration. -/
noncomputable def r32 : E3 := !₂[1, 1, s2]

/-! ### The rays are nonzero and the required pairs are orthogonal -/

lemma nz0 : ⟪r0, r0⟫ ≠ 0 := by
  have hv : ⟪r0, r0⟫ = (1 : ℝ) := by
    simp only [r0, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz1 : ⟪r1, r1⟫ ≠ 0 := by
  have hv : ⟪r1, r1⟫ = (2 : ℝ) := by
    simp only [r1, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz2 : ⟪r2, r2⟫ ≠ 0 := by
  have hv : ⟪r2, r2⟫ = (3 : ℝ) := by
    simp only [r2, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz3 : ⟪r3, r3⟫ ≠ 0 := by
  have hv : ⟪r3, r3⟫ = (3 : ℝ) := by
    simp only [r3, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz4 : ⟪r4, r4⟫ ≠ 0 := by
  have hv : ⟪r4, r4⟫ = (1 : ℝ) := by
    simp only [r4, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz5 : ⟪r5, r5⟫ ≠ 0 := by
  have hv : ⟪r5, r5⟫ = (3 : ℝ) := by
    simp only [r5, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz6 : ⟪r6, r6⟫ ≠ 0 := by
  have hv : ⟪r6, r6⟫ = (3 : ℝ) := by
    simp only [r6, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz7 : ⟪r7, r7⟫ ≠ 0 := by
  have hv : ⟪r7, r7⟫ = (2 : ℝ) := by
    simp only [r7, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz8 : ⟪r8, r8⟫ ≠ 0 := by
  have hv : ⟪r8, r8⟫ = (4 : ℝ) := by
    simp only [r8, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz9 : ⟪r9, r9⟫ ≠ 0 := by
  have hv : ⟪r9, r9⟫ = (2 : ℝ) := by
    simp only [r9, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz10 : ⟪r10, r10⟫ ≠ 0 := by
  have hv : ⟪r10, r10⟫ = (4 : ℝ) := by
    simp only [r10, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz11 : ⟪r11, r11⟫ ≠ 0 := by
  have hv : ⟪r11, r11⟫ = (4 : ℝ) := by
    simp only [r11, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz12 : ⟪r12, r12⟫ ≠ 0 := by
  have hv : ⟪r12, r12⟫ = (3 : ℝ) := by
    simp only [r12, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz13 : ⟪r13, r13⟫ ≠ 0 := by
  have hv : ⟪r13, r13⟫ = (4 : ℝ) := by
    simp only [r13, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz14 : ⟪r14, r14⟫ ≠ 0 := by
  have hv : ⟪r14, r14⟫ = (4 : ℝ) := by
    simp only [r14, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz15 : ⟪r15, r15⟫ ≠ 0 := by
  have hv : ⟪r15, r15⟫ = (3 : ℝ) := by
    simp only [r15, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz16 : ⟪r16, r16⟫ ≠ 0 := by
  have hv : ⟪r16, r16⟫ = (4 : ℝ) := by
    simp only [r16, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz17 : ⟪r17, r17⟫ ≠ 0 := by
  have hv : ⟪r17, r17⟫ = (2 : ℝ) := by
    simp only [r17, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz18 : ⟪r18, r18⟫ ≠ 0 := by
  have hv : ⟪r18, r18⟫ = (3 : ℝ) := by
    simp only [r18, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz19 : ⟪r19, r19⟫ ≠ 0 := by
  have hv : ⟪r19, r19⟫ = (3 : ℝ) := by
    simp only [r19, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz20 : ⟪r20, r20⟫ ≠ 0 := by
  have hv : ⟪r20, r20⟫ = (1 : ℝ) := by
    simp only [r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz21 : ⟪r21, r21⟫ ≠ 0 := by
  have hv : ⟪r21, r21⟫ = (3 : ℝ) := by
    simp only [r21, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz22 : ⟪r22, r22⟫ ≠ 0 := by
  have hv : ⟪r22, r22⟫ = (3 : ℝ) := by
    simp only [r22, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz23 : ⟪r23, r23⟫ ≠ 0 := by
  have hv : ⟪r23, r23⟫ = (2 : ℝ) := by
    simp only [r23, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz24 : ⟪r24, r24⟫ ≠ 0 := by
  have hv : ⟪r24, r24⟫ = (4 : ℝ) := by
    simp only [r24, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz25 : ⟪r25, r25⟫ ≠ 0 := by
  have hv : ⟪r25, r25⟫ = (3 : ℝ) := by
    simp only [r25, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz26 : ⟪r26, r26⟫ ≠ 0 := by
  have hv : ⟪r26, r26⟫ = (4 : ℝ) := by
    simp only [r26, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz27 : ⟪r27, r27⟫ ≠ 0 := by
  have hv : ⟪r27, r27⟫ = (4 : ℝ) := by
    simp only [r27, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz28 : ⟪r28, r28⟫ ≠ 0 := by
  have hv : ⟪r28, r28⟫ = (3 : ℝ) := by
    simp only [r28, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz29 : ⟪r29, r29⟫ ≠ 0 := by
  have hv : ⟪r29, r29⟫ = (4 : ℝ) := by
    simp only [r29, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz30 : ⟪r30, r30⟫ ≠ 0 := by
  have hv : ⟪r30, r30⟫ = (4 : ℝ) := by
    simp only [r30, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz31 : ⟪r31, r31⟫ ≠ 0 := by
  have hv : ⟪r31, r31⟫ = (2 : ℝ) := by
    simp only [r31, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
  rw [hv]; norm_num
lemma nz32 : ⟪r32, r32⟫ ≠ 0 := by
  have hv : ⟪r32, r32⟫ = (4 : ℝ) := by
    simp only [r32, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
  rw [hv]; norm_num

lemma o0_4 : ⟪r0, r4⟫ = 0 := by
  simp only [r0, r4, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_9 : ⟪r0, r9⟫ = 0 := by
  simp only [r0, r9, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_12 : ⟪r0, r12⟫ = 0 := by
  simp only [r0, r12, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_15 : ⟪r0, r15⟫ = 0 := by
  simp only [r0, r15, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_20 : ⟪r0, r20⟫ = 0 := by
  simp only [r0, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_25 : ⟪r0, r25⟫ = 0 := by
  simp only [r0, r25, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_28 : ⟪r0, r28⟫ = 0 := by
  simp only [r0, r28, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o0_31 : ⟪r0, r31⟫ = 0 := by
  simp only [r0, r31, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o1_7 : ⟪r1, r7⟫ = 0 := by
  simp only [r1, r7, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o1_14 : ⟪r1, r14⟫ = 0 := by
  simp only [r1, r14, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o1_20 : ⟪r1, r20⟫ = 0 := by
  simp only [r1, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o1_26 : ⟪r1, r26⟫ = 0 := by
  simp only [r1, r26, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o2_5 : ⟪r2, r5⟫ = 0 := by
  simp only [r2, r5, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o2_11 : ⟪r2, r11⟫ = 0 := by
  simp only [r2, r11, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o2_20 : ⟪r2, r20⟫ = 0 := by
  simp only [r2, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o2_29 : ⟪r2, r29⟫ = 0 := by
  simp only [r2, r29, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o3_6 : ⟪r3, r6⟫ = 0 := by
  simp only [r3, r6, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o3_8 : ⟪r3, r8⟫ = 0 := by
  simp only [r3, r8, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o3_20 : ⟪r3, r20⟫ = 0 := by
  simp only [r3, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o3_32 : ⟪r3, r32⟫ = 0 := by
  simp only [r3, r32, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_17 : ⟪r4, r17⟫ = 0 := by
  simp only [r4, r17, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_18 : ⟪r4, r18⟫ = 0 := by
  simp only [r4, r18, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_19 : ⟪r4, r19⟫ = 0 := by
  simp only [r4, r19, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_20 : ⟪r4, r20⟫ = 0 := by
  simp only [r4, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_21 : ⟪r4, r21⟫ = 0 := by
  simp only [r4, r21, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_22 : ⟪r4, r22⟫ = 0 := by
  simp only [r4, r22, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o4_23 : ⟪r4, r23⟫ = 0 := by
  simp only [r4, r23, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o5_10 : ⟪r5, r10⟫ = 0 := by
  simp only [r5, r10, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o5_20 : ⟪r5, r20⟫ = 0 := by
  simp only [r5, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o5_30 : ⟪r5, r30⟫ = 0 := by
  simp only [r5, r30, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o6_13 : ⟪r6, r13⟫ = 0 := by
  simp only [r6, r13, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o6_20 : ⟪r6, r20⟫ = 0 := by
  simp only [r6, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o6_27 : ⟪r6, r27⟫ = 0 := by
  simp only [r6, r27, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o7_16 : ⟪r7, r16⟫ = 0 := by
  simp only [r7, r16, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o7_20 : ⟪r7, r20⟫ = 0 := by
  simp only [r7, r20, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o7_24 : ⟪r7, r24⟫ = 0 := by
  simp only [r7, r24, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o8_10 : ⟪r8, r10⟫ = 0 := by
  simp only [r8, r10, inner_vec3]; linear_combination (-1 : ℝ) * s2_sq
lemma o8_21 : ⟪r8, r21⟫ = 0 := by
  simp only [r8, r21, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o8_31 : ⟪r8, r31⟫ = 0 := by
  simp only [r8, r31, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o9_30 : ⟪r9, r30⟫ = 0 := by
  simp only [r9, r30, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o9_31 : ⟪r9, r31⟫ = 0 := by
  simp only [r9, r31, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o9_32 : ⟪r9, r32⟫ = 0 := by
  simp only [r9, r32, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o10_19 : ⟪r10, r19⟫ = 0 := by
  simp only [r10, r19, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o10_31 : ⟪r10, r31⟫ = 0 := by
  simp only [r10, r31, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o11_23 : ⟪r11, r23⟫ = 0 := by
  simp only [r11, r23, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o11_25 : ⟪r11, r25⟫ = 0 := by
  simp only [r11, r25, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o11_27 : ⟪r11, r27⟫ = 0 := by
  simp only [r11, r27, inner_vec3]; linear_combination (-1 : ℝ) * s2_sq
lemma o12_24 : ⟪r12, r24⟫ = 0 := by
  simp only [r12, r24, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o12_25 : ⟪r12, r25⟫ = 0 := by
  simp only [r12, r25, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o12_26 : ⟪r12, r26⟫ = 0 := by
  simp only [r12, r26, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o13_17 : ⟪r13, r17⟫ = 0 := by
  simp only [r13, r17, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o13_25 : ⟪r13, r25⟫ = 0 := by
  simp only [r13, r25, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o13_29 : ⟪r13, r29⟫ = 0 := by
  simp only [r13, r29, inner_vec3]; linear_combination (-1 : ℝ) * s2_sq
lemma o14_22 : ⟪r14, r22⟫ = 0 := by
  simp only [r14, r22, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o14_26 : ⟪r14, r26⟫ = 0 := by
  simp only [r14, r26, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
lemma o14_28 : ⟪r14, r28⟫ = 0 := by
  simp only [r14, r28, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o15_27 : ⟪r15, r27⟫ = 0 := by
  simp only [r15, r27, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o15_28 : ⟪r15, r28⟫ = 0 := by
  simp only [r15, r28, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o15_29 : ⟪r15, r29⟫ = 0 := by
  simp only [r15, r29, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o16_18 : ⟪r16, r18⟫ = 0 := by
  simp only [r16, r18, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o16_24 : ⟪r16, r24⟫ = 0 := by
  simp only [r16, r24, inner_vec3]; linear_combination (1 : ℝ) * s2_sq
lemma o16_28 : ⟪r16, r28⟫ = 0 := by
  simp only [r16, r28, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o17_23 : ⟪r17, r23⟫ = 0 := by
  simp only [r17, r23, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o17_29 : ⟪r17, r29⟫ = 0 := by
  simp only [r17, r29, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o18_21 : ⟪r18, r21⟫ = 0 := by
  simp only [r18, r21, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o18_26 : ⟪r18, r26⟫ = 0 := by
  simp only [r18, r26, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o19_22 : ⟪r19, r22⟫ = 0 := by
  simp only [r19, r22, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o19_32 : ⟪r19, r32⟫ = 0 := by
  simp only [r19, r32, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o21_30 : ⟪r21, r30⟫ = 0 := by
  simp only [r21, r30, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o22_24 : ⟪r22, r24⟫ = 0 := by
  simp only [r22, r24, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o23_27 : ⟪r23, r27⟫ = 0 := by
  simp only [r23, r27, inner_vec3]; linear_combination (0 : ℝ) * s2_sq
lemma o30_32 : ⟪r30, r32⟫ = 0 := by
  simp only [r30, r32, inner_vec3]; linear_combination (-1 : ℝ) * s2_sq

/-! ### The combinatorial contradiction -/

private lemma t3_cases_a {a b c : ℕ} (h : a + b + c = 1) : a = 0 ∨ a = 1 := by omega
private lemma t3_cases_b {a b c : ℕ} (h : a + b + c = 1) : b = 0 ∨ b = 1 := by omega
private lemma t3_cases_c {a b c : ℕ} (h : a + b + c = 1) : c = 0 ∨ c = 1 := by omega
private lemma p2_cases_a {a b : ℕ} (h : a + b ≤ 1) : a = 0 ∨ a = 1 := by omega
private lemma p2_cases_b {a b : ℕ} (h : a + b ≤ 1) : b = 0 ∨ b = 1 := by omega
private lemma t3_one_a {a b c : ℕ} (h : a + b + c = 1) (ha : a = 1) : b = 0 ∧ c = 0 := by omega
private lemma t3_one_b {a b c : ℕ} (h : a + b + c = 1) (hb : b = 1) : a = 0 ∧ c = 0 := by omega
private lemma t3_one_c {a b c : ℕ} (h : a + b + c = 1) (hc : c = 1) : a = 0 ∧ b = 0 := by omega
private lemma t3_last_a {a b c : ℕ} (h : a + b + c = 1) (hb : b = 0) (hc : c = 0) : a = 1 := by omega
private lemma t3_last_b {a b c : ℕ} (h : a + b + c = 1) (ha : a = 0) (hc : c = 0) : b = 1 := by omega
private lemma t3_last_c {a b c : ℕ} (h : a + b + c = 1) (ha : a = 0) (hb : b = 0) : c = 1 := by omega
private lemma t3_false {a b c : ℕ} (h : a + b + c = 1) (ha : a = 0) (hb : b = 0) (hc : c = 0) :
    False := by omega
private lemma t3_false_ab {a b c : ℕ} (h : a + b + c = 1) (ha : a = 1) (hb : b = 1) : False := by
  omega
private lemma t3_false_ac {a b c : ℕ} (h : a + b + c = 1) (ha : a = 1) (hc : c = 1) : False := by
  omega
private lemma t3_false_bc {a b c : ℕ} (h : a + b + c = 1) (hb : b = 1) (hc : c = 1) : False := by
  omega
private lemma p2_a {a b : ℕ} (h : a + b ≤ 1) (ha : a = 1) : b = 0 := by omega
private lemma p2_b {a b : ℕ} (h : a + b ≤ 1) (hb : b = 1) : a = 0 := by omega
private lemma p2_false {a b : ℕ} (h : a + b ≤ 1) (ha : a = 1) (hb : b = 1) : False := by omega

/-- The 46 counting constraints coming from Peres' configuration are contradictory. -/
private lemma ks3_arith {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 : ℕ}
    (h0 : x0 + x4 + x20 = 1) (h1 : x0 + x12 + x25 = 1) (h2 : x0 + x15 + x28 = 1)
    (h3 : x1 + x14 + x26 = 1) (h4 : x2 + x5 + x20 = 1) (h5 : x3 + x6 + x20 = 1)
    (h6 : x4 + x18 + x21 = 1) (h7 : x4 + x19 + x22 = 1) (h8 : x7 + x16 + x24 = 1)
    (h9 : x8 + x10 + x31 = 1) (h10 : x9 + x30 + x32 = 1) (h11 : x11 + x23 + x27 = 1)
    (h12 : x13 + x17 + x29 = 1) (h13 : x0 + x9 ≤ 1) (h14 : x0 + x31 ≤ 1)
    (h15 : x1 + x7 ≤ 1) (h16 : x1 + x20 ≤ 1) (h17 : x2 + x11 ≤ 1)
    (h18 : x2 + x29 ≤ 1) (h19 : x3 + x8 ≤ 1) (h20 : x3 + x32 ≤ 1)
    (h21 : x4 + x17 ≤ 1) (h22 : x4 + x23 ≤ 1) (h23 : x5 + x10 ≤ 1)
    (h24 : x5 + x30 ≤ 1) (h25 : x6 + x13 ≤ 1) (h26 : x6 + x27 ≤ 1)
    (h27 : x7 + x20 ≤ 1) (h28 : x8 + x21 ≤ 1) (h29 : x9 + x31 ≤ 1)
    (h30 : x10 + x19 ≤ 1) (h31 : x11 + x25 ≤ 1) (h32 : x12 + x24 ≤ 1)
    (h33 : x12 + x26 ≤ 1) (h34 : x13 + x25 ≤ 1) (h35 : x14 + x22 ≤ 1)
    (h36 : x14 + x28 ≤ 1) (h37 : x15 + x27 ≤ 1) (h38 : x15 + x29 ≤ 1)
    (h39 : x16 + x18 ≤ 1) (h40 : x16 + x28 ≤ 1) (h41 : x17 + x23 ≤ 1)
    (h42 : x18 + x26 ≤ 1) (h43 : x19 + x32 ≤ 1) (h44 : x21 + x30 ≤ 1)
    (h45 : x22 + x24 ≤ 1)
    : False := by
  rcases t3_cases_a h0 with e0 | e0
  ·
    rcases t3_cases_b h0 with e4 | e4
    ·
      have e20 : x20 = 1 := t3_last_c h0 e0 e4
      have ph4_c := t3_one_c h4 e20
      have e2 : x2 = 0 := ph4_c.1
      have e5 : x5 = 0 := ph4_c.2
      have ph5_c := t3_one_c h5 e20
      have e3 : x3 = 0 := ph5_c.1
      have e6 : x6 = 0 := ph5_c.2
      have e1 : x1 = 0 := p2_b h16 e20
      have e7 : x7 = 0 := p2_b h27 e20
      rcases t3_cases_a h9 with e8 | e8
      ·
        rcases t3_cases_a h10 with e9 | e9
        ·
          rcases t3_cases_b h9 with e10 | e10
          ·
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            rcases t3_cases_a h11 with e11 | e11
            ·
              rcases t3_cases_b h1 with e12 | e12
              ·
                have e25 : x25 = 1 := t3_last_c h1 e0 e12
                have e13 : x13 = 0 := p2_b h34 e25
                rcases t3_cases_b h3 with e14 | e14
                ·
                  have e26 : x26 = 1 := t3_last_c h3 e1 e14
                  have e18 : x18 = 0 := p2_b h42 e26
                  have e21 : x21 = 1 := t3_last_c h6 e4 e18
                  have e30 : x30 = 0 := p2_a h44 e21
                  have e32 : x32 = 1 := t3_last_c h10 e9 e30
                  have e19 : x19 = 0 := p2_b h43 e32
                  have e22 : x22 = 1 := t3_last_c h7 e4 e19
                  have e24 : x24 = 0 := p2_a h45 e22
                  have e16 : x16 = 1 := t3_last_b h8 e7 e24
                  have e28 : x28 = 0 := p2_a h40 e16
                  have e15 : x15 = 1 := t3_last_b h2 e0 e28
                  have e27 : x27 = 0 := p2_a h37 e15
                  have e29 : x29 = 0 := p2_a h38 e15
                  have e23 : x23 = 1 := t3_last_b h11 e11 e27
                  have e17 : x17 = 1 := t3_last_b h12 e13 e29
                  exact p2_false h41 e17 e23
                ·
                  have ph3_b := t3_one_b h3 e14
                  have e26 : x26 = 0 := ph3_b.2
                  have e22 : x22 = 0 := p2_a h35 e14
                  have e28 : x28 = 0 := p2_a h36 e14
                  have e15 : x15 = 1 := t3_last_b h2 e0 e28
                  have e19 : x19 = 1 := t3_last_b h7 e4 e22
                  have e27 : x27 = 0 := p2_a h37 e15
                  have e29 : x29 = 0 := p2_a h38 e15
                  have e32 : x32 = 0 := p2_a h43 e19
                  have e30 : x30 = 1 := t3_last_b h10 e9 e32
                  have e23 : x23 = 1 := t3_last_b h11 e11 e27
                  have e17 : x17 = 1 := t3_last_b h12 e13 e29
                  exact p2_false h41 e17 e23
              ·
                have ph1_b := t3_one_b h1 e12
                have e25 : x25 = 0 := ph1_b.2
                have e24 : x24 = 0 := p2_a h32 e12
                have e26 : x26 = 0 := p2_a h33 e12
                have e14 : x14 = 1 := t3_last_b h3 e1 e26
                have e16 : x16 = 1 := t3_last_b h8 e7 e24
                have e22 : x22 = 0 := p2_a h35 e14
                have e28 : x28 = 0 := p2_a h36 e14
                have e18 : x18 = 0 := p2_a h39 e16
                have e15 : x15 = 1 := t3_last_b h2 e0 e28
                have e21 : x21 = 1 := t3_last_c h6 e4 e18
                have e19 : x19 = 1 := t3_last_b h7 e4 e22
                have e27 : x27 = 0 := p2_a h37 e15
                have e29 : x29 = 0 := p2_a h38 e15
                have e32 : x32 = 0 := p2_a h43 e19
                have e30 : x30 = 0 := p2_a h44 e21
                exact t3_false h10 e9 e30 e32
            ·
              have ph11_a := t3_one_a h11 e11
              have e23 : x23 = 0 := ph11_a.1
              have e27 : x27 = 0 := ph11_a.2
              have e25 : x25 = 0 := p2_a h31 e11
              have e12 : x12 = 1 := t3_last_b h1 e0 e25
              have e24 : x24 = 0 := p2_a h32 e12
              have e26 : x26 = 0 := p2_a h33 e12
              have e14 : x14 = 1 := t3_last_b h3 e1 e26
              have e16 : x16 = 1 := t3_last_b h8 e7 e24
              have e22 : x22 = 0 := p2_a h35 e14
              have e28 : x28 = 0 := p2_a h36 e14
              have e18 : x18 = 0 := p2_a h39 e16
              have e15 : x15 = 1 := t3_last_b h2 e0 e28
              have e21 : x21 = 1 := t3_last_c h6 e4 e18
              have e19 : x19 = 1 := t3_last_b h7 e4 e22
              have e29 : x29 = 0 := p2_a h38 e15
              have e32 : x32 = 0 := p2_a h43 e19
              have e30 : x30 = 0 := p2_a h44 e21
              exact t3_false h10 e9 e30 e32
          ·
            have ph9_b := t3_one_b h9 e10
            have e31 : x31 = 0 := ph9_b.2
            have e19 : x19 = 0 := p2_a h30 e10
            have e22 : x22 = 1 := t3_last_c h7 e4 e19
            have e14 : x14 = 0 := p2_b h35 e22
            have e24 : x24 = 0 := p2_a h45 e22
            have e26 : x26 = 1 := t3_last_c h3 e1 e14
            have e16 : x16 = 1 := t3_last_b h8 e7 e24
            have e12 : x12 = 0 := p2_b h33 e26
            have e18 : x18 = 0 := p2_a h39 e16
            have e28 : x28 = 0 := p2_a h40 e16
            have e25 : x25 = 1 := t3_last_c h1 e0 e12
            have e15 : x15 = 1 := t3_last_b h2 e0 e28
            have e21 : x21 = 1 := t3_last_c h6 e4 e18
            have e11 : x11 = 0 := p2_b h31 e25
            have e13 : x13 = 0 := p2_b h34 e25
            have e27 : x27 = 0 := p2_a h37 e15
            have e29 : x29 = 0 := p2_a h38 e15
            have e30 : x30 = 0 := p2_a h44 e21
            have e32 : x32 = 1 := t3_last_c h10 e9 e30
            have e23 : x23 = 1 := t3_last_b h11 e11 e27
            have e17 : x17 = 1 := t3_last_b h12 e13 e29
            exact p2_false h41 e17 e23
        ·
          have ph10_a := t3_one_a h10 e9
          have e30 : x30 = 0 := ph10_a.1
          have e32 : x32 = 0 := ph10_a.2
          have e31 : x31 = 0 := p2_a h29 e9
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e19 : x19 = 0 := p2_a h30 e10
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e14 : x14 = 0 := p2_b h35 e22
          have e24 : x24 = 0 := p2_a h45 e22
          have e26 : x26 = 1 := t3_last_c h3 e1 e14
          have e16 : x16 = 1 := t3_last_b h8 e7 e24
          have e12 : x12 = 0 := p2_b h33 e26
          have e18 : x18 = 0 := p2_a h39 e16
          have e28 : x28 = 0 := p2_a h40 e16
          have e25 : x25 = 1 := t3_last_c h1 e0 e12
          have e15 : x15 = 1 := t3_last_b h2 e0 e28
          have e21 : x21 = 1 := t3_last_c h6 e4 e18
          have e11 : x11 = 0 := p2_b h31 e25
          have e13 : x13 = 0 := p2_b h34 e25
          have e27 : x27 = 0 := p2_a h37 e15
          have e29 : x29 = 0 := p2_a h38 e15
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
      ·
        have ph9_a := t3_one_a h9 e8
        have e10 : x10 = 0 := ph9_a.1
        have e31 : x31 = 0 := ph9_a.2
        have e21 : x21 = 0 := p2_a h28 e8
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e16 : x16 = 0 := p2_b h39 e18
        have e26 : x26 = 0 := p2_a h42 e18
        have e14 : x14 = 1 := t3_last_b h3 e1 e26
        have e24 : x24 = 1 := t3_last_c h8 e7 e16
        have e12 : x12 = 0 := p2_b h32 e24
        have e22 : x22 = 0 := p2_a h35 e14
        have e28 : x28 = 0 := p2_a h36 e14
        have e25 : x25 = 1 := t3_last_c h1 e0 e12
        have e15 : x15 = 1 := t3_last_b h2 e0 e28
        have e19 : x19 = 1 := t3_last_b h7 e4 e22
        have e11 : x11 = 0 := p2_b h31 e25
        have e13 : x13 = 0 := p2_b h34 e25
        have e27 : x27 = 0 := p2_a h37 e15
        have e29 : x29 = 0 := p2_a h38 e15
        have e32 : x32 = 0 := p2_a h43 e19
        have e23 : x23 = 1 := t3_last_b h11 e11 e27
        have e17 : x17 = 1 := t3_last_b h12 e13 e29
        exact p2_false h41 e17 e23
    ·
      have ph0_b := t3_one_b h0 e4
      have e20 : x20 = 0 := ph0_b.2
      have ph6_a := t3_one_a h6 e4
      have e18 : x18 = 0 := ph6_a.1
      have e21 : x21 = 0 := ph6_a.2
      have ph7_a := t3_one_a h7 e4
      have e19 : x19 = 0 := ph7_a.1
      have e22 : x22 = 0 := ph7_a.2
      have e17 : x17 = 0 := p2_a h21 e4
      have e23 : x23 = 0 := p2_a h22 e4
      rcases t3_cases_a h3 with e1 | e1
      ·
        rcases t3_cases_a h4 with e2 | e2
        ·
          have e5 : x5 = 1 := t3_last_b h4 e2 e20
          have e10 : x10 = 0 := p2_a h23 e5
          have e30 : x30 = 0 := p2_a h24 e5
          rcases t3_cases_a h5 with e3 | e3
          ·
            have e6 : x6 = 1 := t3_last_b h5 e3 e20
            have e13 : x13 = 0 := p2_a h25 e6
            have e27 : x27 = 0 := p2_a h26 e6
            have e11 : x11 = 1 := t3_last_a h11 e23 e27
            have e29 : x29 = 1 := t3_last_c h12 e13 e17
            have e25 : x25 = 0 := p2_a h31 e11
            have e15 : x15 = 0 := p2_b h38 e29
            have e12 : x12 = 1 := t3_last_b h1 e0 e25
            have e28 : x28 = 1 := t3_last_c h2 e0 e15
            have e24 : x24 = 0 := p2_a h32 e12
            have e26 : x26 = 0 := p2_a h33 e12
            have e14 : x14 = 0 := p2_b h36 e28
            have e16 : x16 = 0 := p2_b h40 e28
            exact t3_false h3 e1 e14 e26
          ·
            have ph5_a := t3_one_a h5 e3
            have e6 : x6 = 0 := ph5_a.1
            have e8 : x8 = 0 := p2_a h19 e3
            have e32 : x32 = 0 := p2_a h20 e3
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            have e9 : x9 = 1 := t3_last_a h10 e30 e32
            exact p2_false h29 e9 e31
        ·
          have ph4_a := t3_one_a h4 e2
          have e5 : x5 = 0 := ph4_a.1
          have e11 : x11 = 0 := p2_a h17 e2
          have e29 : x29 = 0 := p2_a h18 e2
          have e27 : x27 = 1 := t3_last_c h11 e11 e23
          have e13 : x13 = 1 := t3_last_a h12 e17 e29
          have e6 : x6 = 0 := p2_b h25 e13
          have e25 : x25 = 0 := p2_a h34 e13
          have e15 : x15 = 0 := p2_b h37 e27
          have e12 : x12 = 1 := t3_last_b h1 e0 e25
          have e28 : x28 = 1 := t3_last_c h2 e0 e15
          have e3 : x3 = 1 := t3_last_a h5 e6 e20
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e24 : x24 = 0 := p2_a h32 e12
          have e26 : x26 = 0 := p2_a h33 e12
          have e14 : x14 = 0 := p2_b h36 e28
          have e16 : x16 = 0 := p2_b h40 e28
          exact t3_false h3 e1 e14 e26
      ·
        have ph3_a := t3_one_a h3 e1
        have e14 : x14 = 0 := ph3_a.1
        have e26 : x26 = 0 := ph3_a.2
        have e7 : x7 = 0 := p2_a h15 e1
        rcases t3_cases_a h4 with e2 | e2
        ·
          have e5 : x5 = 1 := t3_last_b h4 e2 e20
          have e10 : x10 = 0 := p2_a h23 e5
          have e30 : x30 = 0 := p2_a h24 e5
          rcases t3_cases_a h5 with e3 | e3
          ·
            have e6 : x6 = 1 := t3_last_b h5 e3 e20
            have e13 : x13 = 0 := p2_a h25 e6
            have e27 : x27 = 0 := p2_a h26 e6
            have e11 : x11 = 1 := t3_last_a h11 e23 e27
            have e29 : x29 = 1 := t3_last_c h12 e13 e17
            have e25 : x25 = 0 := p2_a h31 e11
            have e15 : x15 = 0 := p2_b h38 e29
            have e12 : x12 = 1 := t3_last_b h1 e0 e25
            have e28 : x28 = 1 := t3_last_c h2 e0 e15
            have e24 : x24 = 0 := p2_a h32 e12
            have e16 : x16 = 0 := p2_b h40 e28
            exact t3_false h8 e7 e16 e24
          ·
            have ph5_a := t3_one_a h5 e3
            have e6 : x6 = 0 := ph5_a.1
            have e8 : x8 = 0 := p2_a h19 e3
            have e32 : x32 = 0 := p2_a h20 e3
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            have e9 : x9 = 1 := t3_last_a h10 e30 e32
            exact p2_false h29 e9 e31
        ·
          have ph4_a := t3_one_a h4 e2
          have e5 : x5 = 0 := ph4_a.1
          have e11 : x11 = 0 := p2_a h17 e2
          have e29 : x29 = 0 := p2_a h18 e2
          have e27 : x27 = 1 := t3_last_c h11 e11 e23
          have e13 : x13 = 1 := t3_last_a h12 e17 e29
          have e6 : x6 = 0 := p2_b h25 e13
          have e25 : x25 = 0 := p2_a h34 e13
          have e15 : x15 = 0 := p2_b h37 e27
          have e12 : x12 = 1 := t3_last_b h1 e0 e25
          have e28 : x28 = 1 := t3_last_c h2 e0 e15
          have e3 : x3 = 1 := t3_last_a h5 e6 e20
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e24 : x24 = 0 := p2_a h32 e12
          have e16 : x16 = 0 := p2_b h40 e28
          exact t3_false h8 e7 e16 e24
  ·
    have ph0_a := t3_one_a h0 e0
    have e4 : x4 = 0 := ph0_a.1
    have e20 : x20 = 0 := ph0_a.2
    have ph1_a := t3_one_a h1 e0
    have e12 : x12 = 0 := ph1_a.1
    have e25 : x25 = 0 := ph1_a.2
    have ph2_a := t3_one_a h2 e0
    have e15 : x15 = 0 := ph2_a.1
    have e28 : x28 = 0 := ph2_a.2
    have e9 : x9 = 0 := p2_a h13 e0
    have e31 : x31 = 0 := p2_a h14 e0
    rcases t3_cases_a h3 with e1 | e1
    ·
      rcases t3_cases_a h4 with e2 | e2
      ·
        have e5 : x5 = 1 := t3_last_b h4 e2 e20
        have e10 : x10 = 0 := p2_a h23 e5
        have e30 : x30 = 0 := p2_a h24 e5
        have e8 : x8 = 1 := t3_last_a h9 e10 e31
        have e32 : x32 = 1 := t3_last_c h10 e9 e30
        have e3 : x3 = 0 := p2_b h19 e8
        have e21 : x21 = 0 := p2_a h28 e8
        have e19 : x19 = 0 := p2_b h43 e32
        have e6 : x6 = 1 := t3_last_b h5 e3 e20
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e22 : x22 = 1 := t3_last_c h7 e4 e19
        have e13 : x13 = 0 := p2_a h25 e6
        have e27 : x27 = 0 := p2_a h26 e6
        have e14 : x14 = 0 := p2_b h35 e22
        have e16 : x16 = 0 := p2_b h39 e18
        have e26 : x26 = 0 := p2_a h42 e18
        have e24 : x24 = 0 := p2_a h45 e22
        exact t3_false h3 e1 e14 e26
      ·
        have ph4_a := t3_one_a h4 e2
        have e5 : x5 = 0 := ph4_a.1
        have e11 : x11 = 0 := p2_a h17 e2
        have e29 : x29 = 0 := p2_a h18 e2
        rcases t3_cases_a h5 with e3 | e3
        ·
          have e6 : x6 = 1 := t3_last_b h5 e3 e20
          have e13 : x13 = 0 := p2_a h25 e6
          have e27 : x27 = 0 := p2_a h26 e6
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
        ·
          have ph5_a := t3_one_a h5 e3
          have e6 : x6 = 0 := ph5_a.1
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e30 : x30 = 1 := t3_last_b h10 e9 e32
          have e19 : x19 = 0 := p2_a h30 e10
          have e21 : x21 = 0 := p2_b h44 e30
          have e18 : x18 = 1 := t3_last_b h6 e4 e21
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e14 : x14 = 0 := p2_b h35 e22
          have e16 : x16 = 0 := p2_b h39 e18
          have e26 : x26 = 0 := p2_a h42 e18
          have e24 : x24 = 0 := p2_a h45 e22
          exact t3_false h3 e1 e14 e26
    ·
      have ph3_a := t3_one_a h3 e1
      have e14 : x14 = 0 := ph3_a.1
      have e26 : x26 = 0 := ph3_a.2
      have e7 : x7 = 0 := p2_a h15 e1
      rcases t3_cases_a h4 with e2 | e2
      ·
        have e5 : x5 = 1 := t3_last_b h4 e2 e20
        have e10 : x10 = 0 := p2_a h23 e5
        have e30 : x30 = 0 := p2_a h24 e5
        have e8 : x8 = 1 := t3_last_a h9 e10 e31
        have e32 : x32 = 1 := t3_last_c h10 e9 e30
        have e3 : x3 = 0 := p2_b h19 e8
        have e21 : x21 = 0 := p2_a h28 e8
        have e19 : x19 = 0 := p2_b h43 e32
        have e6 : x6 = 1 := t3_last_b h5 e3 e20
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e22 : x22 = 1 := t3_last_c h7 e4 e19
        have e13 : x13 = 0 := p2_a h25 e6
        have e27 : x27 = 0 := p2_a h26 e6
        have e16 : x16 = 0 := p2_b h39 e18
        have e24 : x24 = 0 := p2_a h45 e22
        exact t3_false h8 e7 e16 e24
      ·
        have ph4_a := t3_one_a h4 e2
        have e5 : x5 = 0 := ph4_a.1
        have e11 : x11 = 0 := p2_a h17 e2
        have e29 : x29 = 0 := p2_a h18 e2
        rcases t3_cases_a h5 with e3 | e3
        ·
          have e6 : x6 = 1 := t3_last_b h5 e3 e20
          have e13 : x13 = 0 := p2_a h25 e6
          have e27 : x27 = 0 := p2_a h26 e6
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
        ·
          have ph5_a := t3_one_a h5 e3
          have e6 : x6 = 0 := ph5_a.1
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e30 : x30 = 1 := t3_last_b h10 e9 e32
          have e19 : x19 = 0 := p2_a h30 e10
          have e21 : x21 = 0 := p2_b h44 e30
          have e18 : x18 = 1 := t3_last_b h6 e4 e21
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e16 : x16 = 0 := p2_b h39 e18
          have e24 : x24 = 0 := p2_a h45 e22
          exact t3_false h8 e7 e16 e24

/-- **Kochen–Specker theorem**, dimension three: there is no assignment of truth values to
the unit vectors of `ℝ³` giving exactly one `true` in every orthonormal basis. -/
theorem kochen_specker_three (f : E3 → Bool)
    (h : ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, f (b i) = true) : False := by
  have c0 := ks_ctx3 f h r0 r4 r20 nz0 nz4 nz20 o0_4 o0_20 o4_20
  have c1 := ks_ctx3 f h r0 r12 r25 nz0 nz12 nz25 o0_12 o0_25 o12_25
  have c2 := ks_ctx3 f h r0 r15 r28 nz0 nz15 nz28 o0_15 o0_28 o15_28
  have c3 := ks_ctx3 f h r1 r14 r26 nz1 nz14 nz26 o1_14 o1_26 o14_26
  have c4 := ks_ctx3 f h r2 r5 r20 nz2 nz5 nz20 o2_5 o2_20 o5_20
  have c5 := ks_ctx3 f h r3 r6 r20 nz3 nz6 nz20 o3_6 o3_20 o6_20
  have c6 := ks_ctx3 f h r4 r18 r21 nz4 nz18 nz21 o4_18 o4_21 o18_21
  have c7 := ks_ctx3 f h r4 r19 r22 nz4 nz19 nz22 o4_19 o4_22 o19_22
  have c8 := ks_ctx3 f h r7 r16 r24 nz7 nz16 nz24 o7_16 o7_24 o16_24
  have c9 := ks_ctx3 f h r8 r10 r31 nz8 nz10 nz31 o8_10 o8_31 o10_31
  have c10 := ks_ctx3 f h r9 r30 r32 nz9 nz30 nz32 o9_30 o9_32 o30_32
  have c11 := ks_ctx3 f h r11 r23 r27 nz11 nz23 nz27 o11_23 o11_27 o23_27
  have c12 := ks_ctx3 f h r13 r17 r29 nz13 nz17 nz29 o13_17 o13_29 o17_29
  have d0 := ks_pair3 f h r0 r9 nz0 nz9 o0_9
  have d1 := ks_pair3 f h r0 r31 nz0 nz31 o0_31
  have d2 := ks_pair3 f h r1 r7 nz1 nz7 o1_7
  have d3 := ks_pair3 f h r1 r20 nz1 nz20 o1_20
  have d4 := ks_pair3 f h r2 r11 nz2 nz11 o2_11
  have d5 := ks_pair3 f h r2 r29 nz2 nz29 o2_29
  have d6 := ks_pair3 f h r3 r8 nz3 nz8 o3_8
  have d7 := ks_pair3 f h r3 r32 nz3 nz32 o3_32
  have d8 := ks_pair3 f h r4 r17 nz4 nz17 o4_17
  have d9 := ks_pair3 f h r4 r23 nz4 nz23 o4_23
  have d10 := ks_pair3 f h r5 r10 nz5 nz10 o5_10
  have d11 := ks_pair3 f h r5 r30 nz5 nz30 o5_30
  have d12 := ks_pair3 f h r6 r13 nz6 nz13 o6_13
  have d13 := ks_pair3 f h r6 r27 nz6 nz27 o6_27
  have d14 := ks_pair3 f h r7 r20 nz7 nz20 o7_20
  have d15 := ks_pair3 f h r8 r21 nz8 nz21 o8_21
  have d16 := ks_pair3 f h r9 r31 nz9 nz31 o9_31
  have d17 := ks_pair3 f h r10 r19 nz10 nz19 o10_19
  have d18 := ks_pair3 f h r11 r25 nz11 nz25 o11_25
  have d19 := ks_pair3 f h r12 r24 nz12 nz24 o12_24
  have d20 := ks_pair3 f h r12 r26 nz12 nz26 o12_26
  have d21 := ks_pair3 f h r13 r25 nz13 nz25 o13_25
  have d22 := ks_pair3 f h r14 r22 nz14 nz22 o14_22
  have d23 := ks_pair3 f h r14 r28 nz14 nz28 o14_28
  have d24 := ks_pair3 f h r15 r27 nz15 nz27 o15_27
  have d25 := ks_pair3 f h r15 r29 nz15 nz29 o15_29
  have d26 := ks_pair3 f h r16 r18 nz16 nz18 o16_18
  have d27 := ks_pair3 f h r16 r28 nz16 nz28 o16_28
  have d28 := ks_pair3 f h r17 r23 nz17 nz23 o17_23
  have d29 := ks_pair3 f h r18 r26 nz18 nz26 o18_26
  have d30 := ks_pair3 f h r19 r32 nz19 nz32 o19_32
  have d31 := ks_pair3 f h r21 r30 nz21 nz30 o21_30
  have d32 := ks_pair3 f h r22 r24 nz22 nz24 o22_24
  exact ks3_arith c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 d32

end Frontier

import RequestProject.KS3

/-!
# From dimension `n ≥ 3` down to dimension three

Given a noncontextual assignment `f` on `ℝⁿ` with `3 ≤ n`, we produce one on `ℝ³`.

The point to check is that the sum rule survives the restriction.  Apply the sum rule to the
standard basis: exactly one standard basis vector, say `e k`, gets the value `true`.  Choose an
injection `φ : Fin 3 ↪ Fin n` whose image contains `k`, and embed `ℝ³` isometrically into `ℝⁿ`
along `φ`.  Any orthonormal basis of the image, completed by the standard basis vectors `e j`
with `j ∉ range φ` (all of which are `false`, since `k ∈ range φ`), is an orthonormal basis of
`ℝⁿ`; hence exactly one vector of the original basis of `ℝ³` gets the value `true`.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- The real inner product on `EuclideanSpace ℝ (Fin n)`, in coordinates. -/
lemma inner_en {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ⟪x, y⟫ = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

/-- A noncontextual assignment in dimension `n ≥ 3` restricts to one in dimension three. -/
theorem ks_reduce {n : ℕ} (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool)
    (h : ∀ b : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ b → ∃! i, f (b i) = true) :
    ∃ g : E3 → Bool, ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, g (b i) = true := by
  classical
  set e : Fin n → EuclideanSpace ℝ (Fin n) := fun j => EuclideanSpace.single j (1:ℝ) with he_def
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single
  obtain ⟨k, hk, hk'⟩ := h e he
  have hn0 : 0 < n := by omega
  set φ : Fin 3 → Fin n := fun i => Equiv.swap (⟨0, hn0⟩ : Fin n) k (Fin.castLE hn i) with hφ_def
  have hφ : Function.Injective φ := fun a b hab =>
    Fin.castLE_injective hn ((Equiv.swap (⟨0, hn0⟩ : Fin n) k).injective hab)
  have hφ0 : φ 0 = k := by
    have h0 : Fin.castLE hn (0 : Fin 3) = (⟨0, hn0⟩ : Fin n) := rfl
    rw [hφ_def]
    simp only [h0, Equiv.swap_apply_left]
  set emb : E3 → EuclideanSpace ℝ (Fin n) :=
    fun u => (WithLp.toLp 2 (Function.extend φ (fun i => u i) (fun _ => (0:ℝ)))) with hemb_def
  have hemb1 : ∀ (u : E3) (i : Fin 3), (emb u) (φ i) = u i := by
    intro u i
    simp only [hemb_def, WithLp.ofLp_toLp]
    exact hφ.extend_apply _ _ i
  have hemb0 : ∀ (u : E3) (j : Fin n), (¬ ∃ i, φ i = j) → (emb u) j = 0 := by
    intro u j hj
    simp only [hemb_def, WithLp.ofLp_toLp]
    exact Function.extend_apply' _ _ _ hj
  have hinner : ∀ u v : E3, ⟪emb u, emb v⟫ = ⟪u, v⟫ := by
    intro u v
    rw [inner_en, inner_en]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image φ Finset.univ))
      (by
        intro j _ hj
        rw [hemb0 u j (by simpa using hj), zero_mul])]
    rw [Finset.sum_image (fun a _ b _ hab => hφ hab)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hemb1, hemb1])
  have hinner_e : ∀ (u : E3) (j : Fin n), (¬ ∃ i, φ i = j) → ⟪emb u, e j⟫ = 0 := by
    intro u j hj
    rw [he_def]
    simp only [EuclideanSpace.inner_single_right]
    simp [hemb0 u j hj]
  refine ⟨fun u => f (emb u), ?_⟩
  intro b hb
  set c : Fin n → EuclideanSpace ℝ (Fin n) := Function.extend φ (fun i => emb (b i)) e with hc_def
  have hc1 : ∀ i, c (φ i) = emb (b i) := fun i => hφ.extend_apply _ _ i
  have hc0 : ∀ j, (¬ ∃ i, φ i = j) → c j = e j := fun j hj => Function.extend_apply' _ _ _ hj
  have hcon : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro j1 j2
    by_cases h1 : ∃ i, φ i = j1
    · obtain ⟨i1, rfl⟩ := h1
      by_cases h2 : ∃ i, φ i = j2
      · obtain ⟨i2, rfl⟩ := h2
        rw [hc1, hc1, hinner, (orthonormal_iff_ite.mp hb) i1 i2]
        by_cases hii : i1 = i2
        · simp [hii]
        · have hne : φ i1 ≠ φ i2 := fun hc => hii (hφ hc)
          simp [hii, hne]
      · rw [hc1, hc0 j2 h2, hinner_e _ _ h2]
        have hne : φ i1 ≠ j2 := fun hcc => h2 ⟨i1, hcc⟩
        simp [hne]
    · by_cases h2 : ∃ i, φ i = j2
      · obtain ⟨i2, rfl⟩ := h2
        rw [hc0 j1 h1, hc1, real_inner_comm, hinner_e _ _ h1]
        have hne : j1 ≠ φ i2 := fun hcc => h1 ⟨i2, hcc.symm⟩
        simp [hne]
      · rw [hc0 j1 h1, hc0 j2 h2, (orthonormal_iff_ite.mp he) j1 j2]
  obtain ⟨j, hj, hju⟩ := h c hcon
  have hjrange : ∃ i, φ i = j := by
    by_contra hcon2
    rw [hc0 j hcon2] at hj
    have hjk : j = k := hk' j hj
    exact hcon2 ⟨0, by rw [hφ0, hjk]⟩
  obtain ⟨i, rfl⟩ := hjrange
  refine ⟨i, ?_, ?_⟩
  · show f (emb (b i)) = true
    rw [← hc1 i]
    exact hj
  · intro i' hi'
    have hii : φ i' = φ i := hju (φ i') (by show f (c (φ i')) = true; rw [hc1 i']; exact hi')
    exact hφ hii

end Frontier

import RequestProject.KSGeneral
import RequestProject.KS4

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

set_option grind.warning false

/-!
# The Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system assigns to every rank-one
projection — equivalently, to every unit vector, i.e. to every "yes/no question" about the
system — a definite truth value, independently of the context (the orthogonal resolution of
the identity) in which the corresponding measurement is performed, and compatibly with the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections, exactly one projection is assigned the value `true`.

The Kochen–Specker theorem says that no such assignment exists in dimension at least three.

Here the assignment is a Boolean-valued function `f` on the vectors of `ℝⁿ`, and the sum rule
is the requirement that for every orthonormal family `b : Fin n → EuclideanSpace ℝ (Fin n)`
— in dimension `n` such a family is precisely an orthonormal basis — there is exactly one
index `i` with `f (b i) = true`.

The dimension-three case is proved in `RequestProject.KS3` from Peres' configuration of
33 rays; `RequestProject.KSGeneral` reduces dimension `n ≥ 3` to dimension three.  The
independent four-dimensional parity proof, using the 18-vector configuration of Cabello,
Estebaranz and García-Alcaine, is in `RequestProject.KS4`.
-/

namespace Frontier

/-- **The Kochen–Specker theorem.**  In dimension `n ≥ 3` there is no noncontextual
hidden-variable assignment: no Boolean-valued function on the vectors of `ℝⁿ` selects exactly
one vector of every orthonormal basis. -/
theorem kochen_specker {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ b : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ b → ∃! i, f (b i) = true := by
  rintro ⟨f, hf⟩
  obtain ⟨g, hg⟩ := ks_reduce hn f hf
  exact kochen_specker_three g hg

end Frontier

import RequestProject.KSCore

/-!
# Kochen–Specker in dimension four (the 18-vector proof)

The proof uses the 18-vector, 9-context configuration of Cabello, Estebaranz and
García-Alcaine: each of the nine contexts is a quadruple of mutually orthogonal vectors, and
each of the eighteen vectors lies in exactly two of the contexts.  Summing "exactly one
`true` per context" over the nine contexts gives `9`, while counting vector by vector gives
an even number — a contradiction.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- Four-dimensional real Euclidean space. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The real inner product of two explicitly given vectors of `E4`. -/
lemma inner_vec4 (a b c d a' b' c' d' : ℝ) :
    ⟪(!₂[a, b, c, d] : E4), !₂[a', b', c', d']⟫ = a * a' + b * b' + c * c' + d * d' := by
  simp [PiLp.inner_apply, Fin.sum_univ_four, mul_comm]

/-- The counting relation attached to one context (orthogonal quadruple of nonzero vectors). -/
lemma ks_ctx4 (f : E4 → Bool)
    (h : ∀ b : Fin 4 → E4, Orthonormal ℝ b → ∃! i, f (b i) = true)
    (w0 w1 w2 w3 : E4)
    (n0 : ⟪w0, w0⟫ ≠ 0) (n1 : ⟪w1, w1⟫ ≠ 0) (n2 : ⟪w2, w2⟫ ≠ 0) (n3 : ⟪w3, w3⟫ ≠ 0)
    (h01 : ⟪w0, w1⟫ = 0) (h02 : ⟪w0, w2⟫ = 0) (h03 : ⟪w0, w3⟫ = 0)
    (h12 : ⟪w1, w2⟫ = 0) (h13 : ⟪w1, w3⟫ = 0) (h23 : ⟪w2, w3⟫ = 0) :
    (f (nrm w0)).toNat + (f (nrm w1)).toNat + (f (nrm w2)).toNat + (f (nrm w3)).toNat = 1 := by
  have hon : Orthonormal ℝ (fun i => nrm (![w0, w1, w2, w3] i)) := by
    apply orthonormal_nrm
    · intro i
      fin_cases i <;> intro hz <;> simp_all
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  simpa using ks_count4 f _ (h _ hon)

/-- **Kochen–Specker theorem**, dimension four: there is no noncontextual assignment of
truth values to the unit vectors (equivalently, rank-one projections) of `ℝ⁴` giving
exactly one `true` in every orthonormal basis. -/
theorem kochen_specker_four (f : E4 → Bool)
    (h : ∀ b : Fin 4 → E4, Orthonormal ℝ b → ∃! i, f (b i) = true) : False := by
  have e1 : (f (nrm !₂[0, 0, 0, 1])).toNat + (f (nrm !₂[0, 0, 1, 0])).toNat
      + (f (nrm !₂[1, 1, 0, 0])).toNat + (f (nrm (!₂[1, -1, 0, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e2 : (f (nrm !₂[0, 0, 0, 1])).toNat + (f (nrm !₂[0, 1, 0, 0])).toNat
      + (f (nrm !₂[1, 0, 1, 0])).toNat + (f (nrm (!₂[1, 0, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e3 : (f (nrm !₂[1, -1, 1, -1])).toNat + (f (nrm !₂[1, -1, -1, 1])).toNat
      + (f (nrm !₂[1, 1, 0, 0])).toNat + (f (nrm (!₂[0, 0, 1, 1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e4 : (f (nrm !₂[1, -1, 1, -1])).toNat + (f (nrm !₂[1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, -1, 0])).toNat + (f (nrm (!₂[0, 1, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e5 : (f (nrm !₂[0, 0, 1, 0])).toNat + (f (nrm !₂[0, 1, 0, 0])).toNat
      + (f (nrm !₂[1, 0, 0, 1])).toNat + (f (nrm (!₂[1, 0, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e6 : (f (nrm !₂[1, -1, -1, 1])).toNat + (f (nrm !₂[1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 0, -1])).toNat + (f (nrm (!₂[0, 1, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e7 : (f (nrm !₂[1, 1, -1, 1])).toNat + (f (nrm !₂[1, 1, 1, -1])).toNat
      + (f (nrm !₂[1, -1, 0, 0])).toNat + (f (nrm (!₂[0, 0, 1, 1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e8 : (f (nrm !₂[1, 1, -1, 1])).toNat + (f (nrm !₂[-1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 1, 0])).toNat + (f (nrm (!₂[0, 1, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e9 : (f (nrm !₂[1, 1, 1, -1])).toNat + (f (nrm !₂[-1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 0, 1])).toNat + (f (nrm (!₂[0, 1, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  omega

end Frontier

