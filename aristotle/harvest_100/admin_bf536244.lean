import Mathlib

/-!
# Kochen–Specker: the three-dimensional core

This file contains the combinatorial/geometric heart of the Kochen–Specker theorem:
there is no `{0,1}`-valued "frame function" on `ℝ³`, i.e. no map assigning to every
unit vector a truth value in such a way that every orthonormal basis contains
exactly one vector with value `true`.

The proof uses the 33 rays of Peres, whose coordinates lie in `{0, ±1, ±√2}`.
Each constraint is certified by an explicit orthogonal triple of vectors, and the
resulting propositional constraint system is refuted by an explicit case analysis.
-/

namespace KochenSpecker

open scoped RealInnerProductSpace

/-- Three-dimensional real Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `ℝ³` given by its three coordinates. -/
noncomputable def vec (a b c : ℝ) : E3 := !₂[a, b, c]

/-- The normalization of a vector. -/
noncomputable def nrm (u : E3) : E3 := ‖u‖⁻¹ • u

noncomputable abbrev s2 : ℝ := Real.sqrt 2

lemma hs2 : s2 * s2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma s2_ne : s2 ≠ 0 := by positivity

lemma inner_vec (a b c x y z : ℝ) : ⟪vec a b c, vec x y z⟫ = a * x + b * y + c * z := by
  simp [vec, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma vec_ne_zero0 {a b c : ℝ} (h : a ≠ 0) : vec a b c ≠ 0 := by
  intro hz
  apply h
  have : (vec a b c).ofLp 0 = (0 : E3).ofLp 0 := by rw [hz]
  simpa [vec] using this

lemma vec_ne_zero1 {a b c : ℝ} (h : b ≠ 0) : vec a b c ≠ 0 := by
  intro hz
  apply h
  have : (vec a b c).ofLp 1 = (0 : E3).ofLp 1 := by rw [hz]
  simpa [vec] using this

lemma vec_ne_zero2 {a b c : ℝ} (h : c ≠ 0) : vec a b c ≠ 0 := by
  intro hz
  apply h
  have : (vec a b c).ofLp 2 = (0 : E3).ofLp 2 := by rw [hz]
  simpa [vec] using this

lemma norm_nrm {u : E3} (hu : u ≠ 0) : ‖nrm u‖ = 1 := by
  simp [nrm, norm_smul, norm_ne_zero_iff.2 hu]

lemma inner_nrm (u v : E3) (h : ⟪u, v⟫ = 0) : ⟪nrm u, nrm v⟫ = 0 := by
  simp [nrm, inner_smul_left, inner_smul_right, h]

/-- Normalizing a triple of nonzero pairwise orthogonal vectors gives an orthonormal family. -/
lemma orthonormal_triple {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    Orthonormal ℝ ![nrm u, nrm v, nrm w] := by
  constructor
  · intro i; fin_cases i <;> simp [norm_nrm, hu, hv, hw]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact inner_nrm _ _ huv
        | exact inner_nrm _ _ huw
        | exact inner_nrm _ _ hvw
        | (rw [real_inner_comm]
           first
             | exact inner_nrm _ _ huv
             | exact inner_nrm _ _ huw
             | exact inner_nrm _ _ hvw)

variable {f : E3 → Bool}

/-- A frame function is `true` on at least one member of an orthogonal triple. -/
theorem clause (H : ∀ v : Fin 3 → E3, Orthonormal ℝ v → ∃! i, f (v i) = true)
    {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    f (nrm u) = true ∨ f (nrm v) = true ∨ f (nrm w) = true := by
  obtain ⟨i, hi, -⟩ := H _ (orthonormal_triple hu hv hw huv huw hvw)
  fin_cases i
  · exact Or.inl (by simpa using hi)
  · exact Or.inr (Or.inl (by simpa using hi))
  · exact Or.inr (Or.inr (by simpa using hi))

/-- A frame function cannot be `true` on two orthogonal vectors. -/
theorem nboth (H : ∀ v : Fin 3 → E3, Orthonormal ℝ v → ∃! i, f (v i) = true)
    {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    ¬ (f (nrm u) = true ∧ f (nrm v) = true) := by
  rintro ⟨h1, h2⟩
  obtain ⟨i, -, huniq⟩ := H _ (orthonormal_triple hu hv hw huv huw hvw)
  have e0 : (0 : Fin 3) = i := huniq 0 (by simpa using h1)
  have e1 : (1 : Fin 3) = i := huniq 1 (by simpa using h2)
  simp [← e0] at e1

section Propositional

variable {A B C : Prop}

theorem or3_1 (h : A ∨ B ∨ C) (hb : ¬B) (hc : ¬C) : A := by tauto
theorem or3_2 (h : A ∨ B ∨ C) (ha : ¬A) (hc : ¬C) : B := by tauto
theorem or3_3 (h : A ∨ B ∨ C) (ha : ¬A) (hb : ¬B) : C := by tauto
theorem or3_absurd (h : A ∨ B ∨ C) (ha : ¬A) (hb : ¬B) (hc : ¬C) : False := by tauto
theorem pair_left (h : ¬(A ∧ B)) (ha : A) : ¬B := fun hb => h ⟨ha, hb⟩
theorem pair_right (h : ¬(A ∧ B)) (hb : B) : ¬A := fun ha => h ⟨ha, hb⟩

end Propositional

/-- **Kochen–Specker, dimension three.**  There is no `{0,1}`-valued frame function on
three-dimensional Euclidean space: no assignment of truth values to unit vectors such
that every orthonormal basis carries exactly one `true` value. -/
theorem no_frame_function_three (f : E3 → Bool)
    (H : ∀ v : Fin 3 → E3, Orthonormal ℝ v → ∃! i, f (v i) = true) : False := by
  have T0 : f (nrm (vec 0 0 1)) = true ∨ f (nrm (vec 0 1 0)) = true ∨ f (nrm (vec 1 0 0)) = true :=
    clause H (vec_ne_zero2 (by norm_num)) (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T1 : f (nrm (vec 0 0 1)) = true ∨ f (nrm (vec 1 s2 0)) = true ∨ f (nrm (vec s2 (-1) 0)) = true :=
    clause H (vec_ne_zero2 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T2 : f (nrm (vec 0 0 1)) = true ∨ f (nrm (vec 1 (-s2) 0)) = true ∨ f (nrm (vec s2 1 0)) = true :=
    clause H (vec_ne_zero2 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T3 : f (nrm (vec 0 1 0)) = true ∨ f (nrm (vec 1 0 s2)) = true ∨ f (nrm (vec s2 0 (-1))) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T4 : f (nrm (vec 0 1 0)) = true ∨ f (nrm (vec 1 0 (-s2))) = true ∨ f (nrm (vec s2 0 1)) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T5 : f (nrm (vec 0 1 1)) = true ∨ f (nrm (vec s2 1 (-1))) = true ∨ f (nrm (vec s2 (-1) 1)) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have T6 : f (nrm (vec 0 1 (-1))) = true ∨ f (nrm (vec s2 1 1)) = true ∨ f (nrm (vec s2 (-1) (-1))) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have T7 : f (nrm (vec 0 1 s2)) = true ∨ f (nrm (vec 0 s2 (-1))) = true ∨ f (nrm (vec 1 0 0)) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T8 : f (nrm (vec 0 1 (-s2))) = true ∨ f (nrm (vec 0 s2 1)) = true ∨ f (nrm (vec 1 0 0)) = true :=
    clause H (vec_ne_zero1 (by norm_num)) (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have T9 : f (nrm (vec 1 0 1)) = true ∨ f (nrm (vec 1 s2 (-1))) = true ∨ f (nrm (vec 1 (-s2) (-1))) = true :=
    clause H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have T10 : f (nrm (vec 1 0 (-1))) = true ∨ f (nrm (vec 1 s2 1)) = true ∨ f (nrm (vec 1 (-s2) 1)) = true :=
    clause H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have T11 : f (nrm (vec 1 1 0)) = true ∨ f (nrm (vec 1 (-1) s2)) = true ∨ f (nrm (vec 1 (-1) (-s2))) = true :=
    clause H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have T12 : f (nrm (vec 1 1 s2)) = true ∨ f (nrm (vec 1 1 (-s2))) = true ∨ f (nrm (vec 1 (-1) 0)) = true :=
    clause H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P0 : ¬ (f (nrm (vec 0 0 1)) = true ∧ f (nrm (vec 0 1 0)) = true) :=
    nboth (w := (vec (-1) 0 0)) H (vec_ne_zero2 (by norm_num)) (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P1 : ¬ (f (nrm (vec 0 0 1)) = true ∧ f (nrm (vec 1 0 0)) = true) :=
    nboth (w := (vec 0 1 0)) H (vec_ne_zero2 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero1 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P2 : ¬ (f (nrm (vec 0 0 1)) = true ∧ f (nrm (vec 1 1 0)) = true) :=
    nboth (w := (vec (-1) 1 0)) H (vec_ne_zero2 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P3 : ¬ (f (nrm (vec 0 0 1)) = true ∧ f (nrm (vec 1 (-1) 0)) = true) :=
    nboth (w := (vec 1 1 0)) H (vec_ne_zero2 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P4 : ¬ (f (nrm (vec 0 1 0)) = true ∧ f (nrm (vec 1 0 0)) = true) :=
    nboth (w := (vec 0 0 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero2 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P5 : ¬ (f (nrm (vec 0 1 0)) = true ∧ f (nrm (vec 1 0 1)) = true) :=
    nboth (w := (vec 1 0 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P6 : ¬ (f (nrm (vec 0 1 0)) = true ∧ f (nrm (vec 1 0 (-1))) = true) :=
    nboth (w := (vec (-1) 0 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P7 : ¬ (f (nrm (vec 0 1 1)) = true ∧ f (nrm (vec 0 1 (-1))) = true) :=
    nboth (w := (vec (-1) 0 0)) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P8 : ¬ (f (nrm (vec 0 1 1)) = true ∧ f (nrm (vec 1 0 0)) = true) :=
    nboth (w := (vec 0 1 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero1 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P9 : ¬ (f (nrm (vec 0 1 (-1))) = true ∧ f (nrm (vec 1 0 0)) = true) :=
    nboth (w := (vec 0 (-1) (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero1 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P10 : ¬ (f (nrm (vec 0 1 s2)) = true ∧ f (nrm (vec 1 s2 (-1))) = true) :=
    nboth (w := (vec (-3) s2 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P11 : ¬ (f (nrm (vec 0 1 s2)) = true ∧ f (nrm (vec 1 (-s2) 1)) = true) :=
    nboth (w := (vec 3 s2 (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P12 : ¬ (f (nrm (vec 0 1 (-s2))) = true ∧ f (nrm (vec 1 s2 1)) = true) :=
    nboth (w := (vec 3 (-s2) (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P13 : ¬ (f (nrm (vec 0 1 (-s2))) = true ∧ f (nrm (vec 1 (-s2) (-1))) = true) :=
    nboth (w := (vec (-3) (-s2) (-1))) H (vec_ne_zero1 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P14 : ¬ (f (nrm (vec 0 s2 1)) = true ∧ f (nrm (vec 1 1 (-s2))) = true) :=
    nboth (w := (vec (-3) 1 (-s2))) H (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P15 : ¬ (f (nrm (vec 0 s2 1)) = true ∧ f (nrm (vec 1 (-1) s2)) = true) :=
    nboth (w := (vec 3 1 (-s2))) H (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P16 : ¬ (f (nrm (vec 0 s2 (-1))) = true ∧ f (nrm (vec 1 1 s2)) = true) :=
    nboth (w := (vec 3 (-1) (-s2))) H (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P17 : ¬ (f (nrm (vec 0 s2 (-1))) = true ∧ f (nrm (vec 1 (-1) (-s2))) = true) :=
    nboth (w := (vec (-3) (-1) (-s2))) H (vec_ne_zero1 s2_ne) (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P18 : ¬ (f (nrm (vec 1 0 1)) = true ∧ f (nrm (vec 1 0 (-1))) = true) :=
    nboth (w := (vec 0 1 0)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero1 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P19 : ¬ (f (nrm (vec 1 0 s2)) = true ∧ f (nrm (vec s2 1 (-1))) = true) :=
    nboth (w := (vec (-s2) 3 1)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (neg_ne_zero.2 s2_ne))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P20 : ¬ (f (nrm (vec 1 0 s2)) = true ∧ f (nrm (vec s2 (-1) (-1))) = true) :=
    nboth (w := (vec s2 3 (-1))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P21 : ¬ (f (nrm (vec 1 0 (-s2))) = true ∧ f (nrm (vec s2 1 1)) = true) :=
    nboth (w := (vec s2 (-3) 1)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P22 : ¬ (f (nrm (vec 1 0 (-s2))) = true ∧ f (nrm (vec s2 (-1) 1)) = true) :=
    nboth (w := (vec (-s2) (-3) (-1))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (neg_ne_zero.2 s2_ne))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P23 : ¬ (f (nrm (vec 1 1 0)) = true ∧ f (nrm (vec 1 (-1) 0)) = true) :=
    nboth (w := (vec 0 0 (-1))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 (by norm_num)) (vec_ne_zero2 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; ring)
  have P24 : ¬ (f (nrm (vec 1 1 s2)) = true ∧ f (nrm (vec s2 0 (-1))) = true) :=
    nboth (w := (vec (-1) 3 (-s2))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P25 : ¬ (f (nrm (vec 1 1 (-s2))) = true ∧ f (nrm (vec s2 0 1)) = true) :=
    nboth (w := (vec 1 (-3) (-s2))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P26 : ¬ (f (nrm (vec 1 (-1) s2)) = true ∧ f (nrm (vec s2 0 (-1))) = true) :=
    nboth (w := (vec 1 3 s2)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P27 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true ∧ f (nrm (vec s2 0 1)) = true) :=
    nboth (w := (vec (-1) (-3) s2)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P28 : ¬ (f (nrm (vec 1 s2 0)) = true ∧ f (nrm (vec s2 (-1) 1)) = true) :=
    nboth (w := (vec s2 (-1) (-3))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P29 : ¬ (f (nrm (vec 1 s2 0)) = true ∧ f (nrm (vec s2 (-1) (-1))) = true) :=
    nboth (w := (vec (-s2) 1 (-3))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (neg_ne_zero.2 s2_ne))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P30 : ¬ (f (nrm (vec 1 s2 1)) = true ∧ f (nrm (vec s2 (-1) 0)) = true) :=
    nboth (w := (vec 1 s2 (-3))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P31 : ¬ (f (nrm (vec 1 s2 (-1))) = true ∧ f (nrm (vec s2 (-1) 0)) = true) :=
    nboth (w := (vec (-1) (-s2) (-3))) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P32 : ¬ (f (nrm (vec 1 (-s2) 0)) = true ∧ f (nrm (vec s2 1 1)) = true) :=
    nboth (w := (vec (-s2) (-1) 3)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (neg_ne_zero.2 s2_ne))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2)
  have P33 : ¬ (f (nrm (vec 1 (-s2) 0)) = true ∧ f (nrm (vec s2 1 (-1))) = true) :=
    nboth (w := (vec s2 1 3)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 s2_ne)
      (by rw [inner_vec]; ring) (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2)
  have P34 : ¬ (f (nrm (vec 1 (-s2) 1)) = true ∧ f (nrm (vec s2 1 0)) = true) :=
    nboth (w := (vec (-1) s2 3)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (-1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  have P35 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true ∧ f (nrm (vec s2 1 0)) = true) :=
    nboth (w := (vec 1 (-s2) 3)) H (vec_ne_zero0 (by norm_num)) (vec_ne_zero0 s2_ne) (vec_ne_zero0 (by norm_num))
      (by rw [inner_vec]; ring) (by rw [inner_vec]; linear_combination (1 : ℝ) * hs2) (by rw [inner_vec]; ring)
  by_cases h1 : f (nrm (vec 0 0 1)) = true
  · have u2 : ¬ (f (nrm (vec 0 1 0)) = true) := pair_left P0 h1
    have u3 : ¬ (f (nrm (vec 1 0 0)) = true) := pair_left P1 h1
    have u4 : ¬ (f (nrm (vec 1 1 0)) = true) := pair_left P2 h1
    have u5 : ¬ (f (nrm (vec 1 (-1) 0)) = true) := pair_left P3 h1
    by_cases h6 : f (nrm (vec 1 s2 0)) = true
    · have u7 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P28 h6
      have u8 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P29 h6
      by_cases h9 : f (nrm (vec s2 (-1) 0)) = true
      · have u10 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_right P30 h9
        have u11 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_right P31 h9
        by_cases h12 : f (nrm (vec 1 (-s2) 0)) = true
        · have u13 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h12
          have u14 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h12
          have u15 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u14 u7
          have u16 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u13 u8
          exact P7 ⟨u15, u16⟩
        · by_cases h17 : f (nrm (vec s2 1 0)) = true
          · have u18 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h17
            have u19 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h17
            have u20 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u11 u19
            have u21 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u10 u18
            exact P18 ⟨u20, u21⟩
          · by_cases h22 : f (nrm (vec 1 0 s2)) = true
            · have u23 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h22
              have u24 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u23 u7
              have u25 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u24
              have u26 : f (nrm (vec s2 1 1)) = true := or3_2 T6 u25 u8
              have u27 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P21 u26
              have u28 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u27
              have u29 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u28
              have u30 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u28
              have u31 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u30
              have u32 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u29 u5
              have u33 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u31
              have u34 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u32
              have u35 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u32
              have u36 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u34 u3
              have u37 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u33 u3
              have u38 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u36
              have u39 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u37
              have u40 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u11 u39
              have u41 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u10 u38
              exact P18 ⟨u40, u41⟩
            · have u42 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h22
              have u43 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u42
              have u44 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u42
              have u45 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u44
              have u46 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u43 u5
              have u47 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u46
              have u48 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u45
              have u49 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u46
              have u50 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u49
              have u51 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u48 u3
              have u52 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u47 u3
              have u53 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u51
              have u54 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u52
              have u55 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u50
              have u56 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u55 u8
              have u57 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u11 u54
              have u58 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u10 u53
              have u59 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u56
              exact P18 ⟨u57, u58⟩
      · by_cases h60 : f (nrm (vec 1 (-s2) 0)) = true
        · have u61 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h60
          have u62 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h60
          have u63 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u62 u7
          have u64 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u61 u8
          exact P7 ⟨u63, u64⟩
        · by_cases h65 : f (nrm (vec s2 1 0)) = true
          · have u66 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h65
            have u67 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h65
            by_cases h68 : f (nrm (vec 1 0 s2)) = true
            · have u69 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h68
              have u70 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u69 u7
              have u71 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u70
              have u72 : f (nrm (vec s2 1 1)) = true := or3_2 T6 u71 u8
              have u73 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P21 u72
              have u74 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u73
              have u75 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u74
              have u76 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u74
              have u77 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u76
              have u78 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u75 u5
              have u79 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u77
              have u80 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u78
              have u81 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u78
              have u82 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u80 u3
              have u83 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u79 u3
              have u84 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u82
              have u85 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u83
              have u86 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u84 u67
              have u87 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u85 u66
              exact P18 ⟨u86, u87⟩
            · have u88 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h68
              have u89 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u88
              have u90 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u88
              have u91 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u90
              have u92 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u89 u5
              have u93 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u92
              have u94 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u91
              have u95 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u92
              have u96 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u95
              have u97 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u94 u3
              have u98 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u93 u3
              have u99 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u97
              have u100 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u98
              have u101 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u96
              have u102 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u101 u8
              have u103 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u99 u67
              have u104 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u100 u66
              have u105 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u102
              exact P18 ⟨u103, u104⟩
          · by_cases h106 : f (nrm (vec 1 0 s2)) = true
            · have u107 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h106
              have u108 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u107 u7
              have u109 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u108
              have u110 : f (nrm (vec s2 1 1)) = true := or3_2 T6 u109 u8
              have u111 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P21 u110
              have u112 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u111
              have u113 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u112
              have u114 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u112
              have u115 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u114
              have u116 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u113 u5
              have u117 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u115
              have u118 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u116
              have u119 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u116
              have u120 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u118 u3
              have u121 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u117 u3
              have u122 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u120
              have u123 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u120
              have u124 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u121
              have u125 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u121
              have u126 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u122 u125
              have u127 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u124 u123
              exact P18 ⟨u126, u127⟩
            · have u128 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h106
              have u129 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u128
              have u130 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u128
              have u131 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u130
              have u132 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u129 u5
              have u133 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u132
              have u134 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u131
              have u135 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u132
              have u136 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u135
              have u137 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u134 u3
              have u138 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u133 u3
              have u139 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u137
              have u140 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u137
              have u141 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u138
              have u142 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u138
              have u143 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u136
              have u144 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u143 u8
              have u145 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u139 u142
              have u146 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u141 u140
              have u147 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u144
              exact P18 ⟨u145, u146⟩
    · by_cases h148 : f (nrm (vec s2 (-1) 0)) = true
      · have u149 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_right P30 h148
        have u150 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_right P31 h148
        by_cases h151 : f (nrm (vec 1 (-s2) 0)) = true
        · have u152 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h151
          have u153 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h151
          by_cases h154 : f (nrm (vec s2 1 0)) = true
          · have u155 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h154
            have u156 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h154
            have u157 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u156
            have u158 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u155
            exact P18 ⟨u157, u158⟩
          · by_cases h159 : f (nrm (vec 1 0 s2)) = true
            · have u160 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h159
              have u161 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u152 u160
              have u162 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u161
              have u163 : f (nrm (vec s2 (-1) 1)) = true := or3_3 T5 u162 u153
              have u164 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P22 u163
              have u165 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u164
              have u166 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u165
              have u167 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u165
              have u168 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u167
              have u169 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u166 u5
              have u170 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u168
              have u171 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u169
              have u172 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u169
              have u173 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u171 u3
              have u174 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u170 u3
              have u175 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u173
              have u176 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u174
              have u177 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u176
              have u178 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u175
              exact P18 ⟨u177, u178⟩
            · have u179 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h159
              have u180 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u179
              have u181 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u179
              have u182 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u181
              have u183 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u180 u5
              have u184 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u183
              have u185 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u182
              have u186 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u183
              have u187 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u186
              have u188 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u185 u3
              have u189 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u184 u3
              have u190 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u188
              have u191 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u189
              have u192 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u187
              have u193 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u153 u192
              have u194 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u191
              have u195 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u190
              have u196 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u193
              exact P18 ⟨u194, u195⟩
        · by_cases h197 : f (nrm (vec s2 1 0)) = true
          · have u198 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h197
            have u199 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h197
            have u200 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u199
            have u201 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u198
            exact P18 ⟨u200, u201⟩
          · by_cases h202 : f (nrm (vec 1 0 s2)) = true
            · have u203 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h202
              have u204 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h202
              by_cases h205 : f (nrm (vec s2 0 (-1))) = true
              · have u206 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 h205
                have u207 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 h205
                have u208 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u207
                have u209 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u206 u5
                have u210 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u209
                have u211 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u208
                have u212 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u209
                have u213 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u212
                have u214 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u211 u3
                have u215 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u210 u3
                have u216 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u214
                have u217 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u215
                have u218 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u213
                have u219 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u213
                have u220 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u203 u219
                have u221 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u218 u204
                have u222 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u217
                have u223 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u216
                exact P7 ⟨u220, u221⟩
              · by_cases h224 : f (nrm (vec 1 0 (-s2))) = true
                · have u225 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 h224
                  have u226 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 h224
                  have u227 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u203 u226
                  have u228 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u225 u204
                  exact P7 ⟨u227, u228⟩
                · have u229 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 h224
                  have u230 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u229
                  have u231 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u229
                  have u232 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u231
                  have u233 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u230 u5
                  have u234 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u232
                  have u235 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u233
                  have u236 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u235 u3
                  have u237 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u234 u3
                  have u238 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u236
                  have u239 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u237
                  have u240 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u239
                  have u241 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u238
                  exact P18 ⟨u240, u241⟩
            · have u242 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h202
              have u243 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u242
              have u244 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u242
              have u245 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u244
              have u246 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u243 u5
              have u247 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u246
              have u248 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u245
              have u249 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u246
              have u250 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u249
              have u251 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u248 u3
              have u252 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u247 u3
              have u253 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u251
              have u254 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u252
              have u255 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u250
              have u256 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u250
              have u257 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u150 u254
              have u258 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u149 u253
              exact P18 ⟨u257, u258⟩
      · by_cases h259 : f (nrm (vec 1 (-s2) 0)) = true
        · have u260 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h259
          have u261 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h259
          by_cases h262 : f (nrm (vec s2 1 0)) = true
          · have u263 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h262
            have u264 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h262
            by_cases h265 : f (nrm (vec 1 0 s2)) = true
            · have u266 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h265
              have u267 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u260 u266
              have u268 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u267
              have u269 : f (nrm (vec s2 (-1) 1)) = true := or3_3 T5 u268 u261
              have u270 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P22 u269
              have u271 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u270
              have u272 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u271
              have u273 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u271
              have u274 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u273
              have u275 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u272 u5
              have u276 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u274
              have u277 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u275
              have u278 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u275
              have u279 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u277 u3
              have u280 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u276 u3
              have u281 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u279
              have u282 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u280
              have u283 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u281 u264
              have u284 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u282 u263
              exact P18 ⟨u283, u284⟩
            · have u285 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h265
              have u286 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u285
              have u287 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u285
              have u288 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u287
              have u289 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u286 u5
              have u290 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u289
              have u291 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u288
              have u292 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u289
              have u293 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u292
              have u294 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u291 u3
              have u295 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u290 u3
              have u296 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u294
              have u297 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u295
              have u298 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u293
              have u299 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u261 u298
              have u300 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u296 u264
              have u301 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u297 u263
              have u302 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u299
              exact P18 ⟨u300, u301⟩
          · by_cases h303 : f (nrm (vec 1 0 s2)) = true
            · have u304 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h303
              have u305 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u260 u304
              have u306 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P7 u305
              have u307 : f (nrm (vec s2 (-1) 1)) = true := or3_3 T5 u306 u261
              have u308 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P22 u307
              have u309 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 u308
              have u310 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u309
              have u311 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u309
              have u312 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u311
              have u313 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u310 u5
              have u314 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u312
              have u315 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u313
              have u316 : ¬ (f (nrm (vec s2 0 (-1))) = true) := pair_left P24 u313
              have u317 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u315 u3
              have u318 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u314 u3
              have u319 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u317
              have u320 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u317
              have u321 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u318
              have u322 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u318
              have u323 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u319 u322
              have u324 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u321 u320
              exact P18 ⟨u323, u324⟩
            · have u325 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h303
              have u326 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u325
              have u327 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u325
              have u328 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u327
              have u329 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u326 u5
              have u330 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u329
              have u331 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u328
              have u332 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u329
              have u333 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u332
              have u334 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u331 u3
              have u335 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u330 u3
              have u336 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u334
              have u337 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u334
              have u338 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u335
              have u339 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u335
              have u340 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u333
              have u341 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u261 u340
              have u342 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u336 u339
              have u343 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u338 u337
              have u344 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_left P7 u341
              exact P18 ⟨u342, u343⟩
        · by_cases h345 : f (nrm (vec s2 1 0)) = true
          · have u346 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 h345
            have u347 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 h345
            by_cases h348 : f (nrm (vec 1 0 s2)) = true
            · have u349 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h348
              have u350 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h348
              by_cases h351 : f (nrm (vec s2 0 (-1))) = true
              · have u352 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 h351
                have u353 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 h351
                have u354 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u353
                have u355 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u352 u5
                have u356 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u355
                have u357 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u354
                have u358 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u355
                have u359 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u358
                have u360 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u357 u3
                have u361 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u356 u3
                have u362 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u360
                have u363 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u361
                have u364 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u359
                have u365 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u359
                have u366 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u349 u365
                have u367 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u364 u350
                have u368 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u362 u347
                have u369 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u363 u346
                exact P7 ⟨u366, u367⟩
              · by_cases h370 : f (nrm (vec 1 0 (-s2))) = true
                · have u371 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 h370
                  have u372 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 h370
                  have u373 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u349 u372
                  have u374 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u371 u350
                  exact P7 ⟨u373, u374⟩
                · have u375 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 h370
                  have u376 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u375
                  have u377 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u375
                  have u378 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u377
                  have u379 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u376 u5
                  have u380 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u378
                  have u381 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u379
                  have u382 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u381 u3
                  have u383 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u380 u3
                  have u384 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u382
                  have u385 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u383
                  have u386 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u384 u347
                  have u387 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u385 u346
                  exact P18 ⟨u386, u387⟩
            · have u388 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h348
              have u389 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u388
              have u390 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u388
              have u391 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u390
              have u392 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u389 u5
              have u393 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u392
              have u394 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u391
              have u395 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u392
              have u396 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u395
              have u397 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u394 u3
              have u398 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u393 u3
              have u399 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u397
              have u400 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u398
              have u401 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u396
              have u402 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u396
              have u403 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u399 u347
              have u404 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u400 u346
              exact P18 ⟨u403, u404⟩
          · by_cases h405 : f (nrm (vec 1 0 s2)) = true
            · have u406 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P19 h405
              have u407 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P20 h405
              by_cases h408 : f (nrm (vec s2 0 (-1))) = true
              · have u409 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 h408
                have u410 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 h408
                have u411 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u410
                have u412 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u409 u5
                have u413 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u412
                have u414 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u411
                have u415 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u412
                have u416 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u415
                have u417 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u414 u3
                have u418 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u413 u3
                have u419 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u417
                have u420 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u417
                have u421 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u418
                have u422 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u418
                have u423 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u416
                have u424 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u416
                have u425 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u406 u424
                have u426 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u423 u407
                have u427 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u419 u422
                have u428 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u421 u420
                exact P7 ⟨u425, u426⟩
              · by_cases h429 : f (nrm (vec 1 0 (-s2))) = true
                · have u430 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 h429
                  have u431 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 h429
                  have u432 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u406 u431
                  have u433 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u430 u407
                  exact P7 ⟨u432, u433⟩
                · have u434 : f (nrm (vec s2 0 1)) = true := or3_3 T4 u2 h429
                  have u435 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u434
                  have u436 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u434
                  have u437 : f (nrm (vec 1 (-1) s2)) = true := or3_2 T11 u4 u436
                  have u438 : f (nrm (vec 1 1 s2)) = true := or3_1 T12 u435 u5
                  have u439 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P15 u437
                  have u440 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P16 u438
                  have u441 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u440 u3
                  have u442 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u439 u3
                  have u443 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u441
                  have u444 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u441
                  have u445 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u442
                  have u446 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u442
                  have u447 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u443 u446
                  have u448 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u445 u444
                  exact P18 ⟨u447, u448⟩
            · have u449 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 u2 h405
              have u450 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u449
              have u451 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u449
              have u452 : f (nrm (vec 1 (-1) (-s2))) = true := or3_3 T11 u4 u451
              have u453 : f (nrm (vec 1 1 (-s2))) = true := or3_2 T12 u450 u5
              have u454 : ¬ (f (nrm (vec 0 s2 1)) = true) := pair_right P14 u453
              have u455 : ¬ (f (nrm (vec 0 s2 (-1))) = true) := pair_right P17 u452
              have u456 : ¬ (f (nrm (vec s2 0 1)) = true) := pair_left P25 u453
              have u457 : f (nrm (vec 1 0 (-s2))) = true := or3_2 T4 u2 u456
              have u458 : f (nrm (vec 0 1 s2)) = true := or3_1 T7 u455 u3
              have u459 : f (nrm (vec 0 1 (-s2))) = true := or3_1 T8 u454 u3
              have u460 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_left P10 u458
              have u461 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_left P11 u458
              have u462 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_left P12 u459
              have u463 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_left P13 u459
              have u464 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P21 u457
              have u465 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P22 u457
              have u466 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u460 u463
              have u467 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u462 u461
              exact P18 ⟨u466, u467⟩
  · by_cases h468 : f (nrm (vec 0 1 0)) = true
    · have u469 : ¬ (f (nrm (vec 1 0 0)) = true) := pair_left P4 h468
      have u470 : ¬ (f (nrm (vec 1 0 1)) = true) := pair_left P5 h468
      have u471 : ¬ (f (nrm (vec 1 0 (-1))) = true) := pair_left P6 h468
      by_cases h472 : f (nrm (vec 1 s2 0)) = true
      · have u473 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P28 h472
        have u474 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P29 h472
        by_cases h475 : f (nrm (vec s2 (-1) 0)) = true
        · have u476 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_right P30 h475
          have u477 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_right P31 h475
          have u478 : f (nrm (vec 1 (-s2) (-1))) = true := or3_3 T9 u470 u477
          have u479 : f (nrm (vec 1 (-s2) 1)) = true := or3_3 T10 u471 u476
          have u480 : ¬ (f (nrm (vec 0 1 s2)) = true) := pair_right P11 u479
          have u481 : ¬ (f (nrm (vec 0 1 (-s2))) = true) := pair_right P13 u478
          have u482 : ¬ (f (nrm (vec s2 1 0)) = true) := pair_left P34 u479
          have u483 : f (nrm (vec 1 (-s2) 0)) = true := or3_2 T2 h1 u482
          have u484 : f (nrm (vec 0 s2 (-1))) = true := or3_2 T7 u480 u469
          have u485 : f (nrm (vec 0 s2 1)) = true := or3_2 T8 u481 u469
          have u486 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_left P14 u485
          have u487 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_left P15 u485
          have u488 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_left P16 u484
          have u489 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_left P17 u484
          have u490 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 u483
          have u491 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 u483
          have u492 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u491 u473
          have u493 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u490 u474
          have u494 : f (nrm (vec 1 1 0)) = true := or3_1 T11 u487 u489
          have u495 : f (nrm (vec 1 (-1) 0)) = true := or3_3 T12 u488 u486
          exact P7 ⟨u492, u493⟩
        · by_cases h496 : f (nrm (vec 1 (-s2) 0)) = true
          · have u497 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h496
            have u498 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h496
            have u499 : f (nrm (vec 0 1 1)) = true := or3_1 T5 u498 u473
            have u500 : f (nrm (vec 0 1 (-1))) = true := or3_1 T6 u497 u474
            exact P7 ⟨u499, u500⟩
          · have u501 : f (nrm (vec s2 1 0)) = true := or3_3 T2 h1 h496
            have u502 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 u501
            have u503 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 u501
            have u504 : f (nrm (vec 1 s2 (-1))) = true := or3_2 T9 u470 u503
            have u505 : f (nrm (vec 1 s2 1)) = true := or3_2 T10 u471 u502
            have u506 : ¬ (f (nrm (vec 0 1 s2)) = true) := pair_right P10 u504
            have u507 : ¬ (f (nrm (vec 0 1 (-s2))) = true) := pair_right P12 u505
            have u508 : f (nrm (vec 0 s2 (-1))) = true := or3_2 T7 u506 u469
            have u509 : f (nrm (vec 0 s2 1)) = true := or3_2 T8 u507 u469
            have u510 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_left P14 u509
            have u511 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_left P15 u509
            have u512 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_left P16 u508
            have u513 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_left P17 u508
            have u514 : f (nrm (vec 1 1 0)) = true := or3_1 T11 u511 u513
            have u515 : f (nrm (vec 1 (-1) 0)) = true := or3_3 T12 u512 u510
            exact P23 ⟨u514, u515⟩
      · have u516 : f (nrm (vec s2 (-1) 0)) = true := or3_3 T1 h1 h472
        have u517 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_right P30 u516
        have u518 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_right P31 u516
        have u519 : f (nrm (vec 1 (-s2) (-1))) = true := or3_3 T9 u470 u518
        have u520 : f (nrm (vec 1 (-s2) 1)) = true := or3_3 T10 u471 u517
        have u521 : ¬ (f (nrm (vec 0 1 s2)) = true) := pair_right P11 u520
        have u522 : ¬ (f (nrm (vec 0 1 (-s2))) = true) := pair_right P13 u519
        have u523 : ¬ (f (nrm (vec s2 1 0)) = true) := pair_left P34 u520
        have u524 : f (nrm (vec 1 (-s2) 0)) = true := or3_2 T2 h1 u523
        have u525 : f (nrm (vec 0 s2 (-1))) = true := or3_2 T7 u521 u469
        have u526 : f (nrm (vec 0 s2 1)) = true := or3_2 T8 u522 u469
        have u527 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_left P14 u526
        have u528 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_left P15 u526
        have u529 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_left P16 u525
        have u530 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_left P17 u525
        have u531 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 u524
        have u532 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 u524
        have u533 : f (nrm (vec 1 1 0)) = true := or3_1 T11 u528 u530
        have u534 : f (nrm (vec 1 (-1) 0)) = true := or3_3 T12 u529 u527
        exact P23 ⟨u533, u534⟩
    · have u535 : f (nrm (vec 1 0 0)) = true := or3_3 T0 h1 h468
      have u536 : ¬ (f (nrm (vec 0 1 1)) = true) := pair_right P8 u535
      have u537 : ¬ (f (nrm (vec 0 1 (-1))) = true) := pair_right P9 u535
      by_cases h538 : f (nrm (vec 1 s2 0)) = true
      · have u539 : ¬ (f (nrm (vec s2 (-1) 1)) = true) := pair_left P28 h538
        have u540 : ¬ (f (nrm (vec s2 (-1) (-1))) = true) := pair_left P29 h538
        have u541 : f (nrm (vec s2 1 (-1))) = true := or3_2 T5 u536 u539
        have u542 : f (nrm (vec s2 1 1)) = true := or3_2 T6 u537 u540
        have u543 : ¬ (f (nrm (vec 1 0 s2)) = true) := pair_right P19 u541
        have u544 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P21 u542
        have u545 : ¬ (f (nrm (vec 1 (-s2) 0)) = true) := pair_right P32 u542
        have u546 : f (nrm (vec s2 1 0)) = true := or3_3 T2 h1 u545
        have u547 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 h468 u543
        have u548 : f (nrm (vec s2 0 1)) = true := or3_3 T4 h468 u544
        have u549 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u547
        have u550 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u548
        have u551 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u547
        have u552 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u548
        have u553 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 u546
        have u554 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 u546
        have u555 : f (nrm (vec 1 1 0)) = true := or3_1 T11 u551 u552
        have u556 : f (nrm (vec 1 (-1) 0)) = true := or3_3 T12 u549 u550
        exact P23 ⟨u555, u556⟩
      · have u557 : f (nrm (vec s2 (-1) 0)) = true := or3_3 T1 h1 h538
        have u558 : ¬ (f (nrm (vec 1 s2 1)) = true) := pair_right P30 u557
        have u559 : ¬ (f (nrm (vec 1 s2 (-1))) = true) := pair_right P31 u557
        by_cases h560 : f (nrm (vec 1 (-s2) 0)) = true
        · have u561 : ¬ (f (nrm (vec s2 1 1)) = true) := pair_left P32 h560
          have u562 : ¬ (f (nrm (vec s2 1 (-1))) = true) := pair_left P33 h560
          have u563 : f (nrm (vec s2 (-1) 1)) = true := or3_3 T5 u536 u562
          have u564 : f (nrm (vec s2 (-1) (-1))) = true := or3_3 T6 u537 u561
          have u565 : ¬ (f (nrm (vec 1 0 s2)) = true) := pair_right P20 u564
          have u566 : ¬ (f (nrm (vec 1 0 (-s2))) = true) := pair_right P22 u563
          have u567 : f (nrm (vec s2 0 (-1))) = true := or3_3 T3 h468 u565
          have u568 : f (nrm (vec s2 0 1)) = true := or3_3 T4 h468 u566
          have u569 : ¬ (f (nrm (vec 1 1 s2)) = true) := pair_right P24 u567
          have u570 : ¬ (f (nrm (vec 1 1 (-s2))) = true) := pair_right P25 u568
          have u571 : ¬ (f (nrm (vec 1 (-1) s2)) = true) := pair_right P26 u567
          have u572 : ¬ (f (nrm (vec 1 (-1) (-s2))) = true) := pair_right P27 u568
          have u573 : f (nrm (vec 1 1 0)) = true := or3_1 T11 u571 u572
          have u574 : f (nrm (vec 1 (-1) 0)) = true := or3_3 T12 u569 u570
          exact P23 ⟨u573, u574⟩
        · have u575 : f (nrm (vec s2 1 0)) = true := or3_3 T2 h1 h560
          have u576 : ¬ (f (nrm (vec 1 (-s2) 1)) = true) := pair_right P34 u575
          have u577 : ¬ (f (nrm (vec 1 (-s2) (-1))) = true) := pair_right P35 u575
          have u578 : f (nrm (vec 1 0 1)) = true := or3_1 T9 u559 u577
          have u579 : f (nrm (vec 1 0 (-1))) = true := or3_1 T10 u558 u576
          exact P18 ⟨u578, u579⟩

end KochenSpecker

import Mathlib
import RequestProject.KochenSpecker

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
# The Kochen–Specker theorem

There is no noncontextual hidden-variable assignment for quantum mechanics in
dimension `n ≥ 3`: no map assigning to each vector of `ℝⁿ` a truth value in such
a way that every orthonormal basis carries exactly one `true` value.

The three-dimensional core (using Peres' 33 rays) is proved in
`RequestProject.KochenSpecker`; here we reduce the general case to it.
-/

namespace Frontier

open scoped RealInnerProductSpace

open KochenSpecker (E3 no_frame_function_three)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The isometric embedding of `ℝ³` into a space with orthonormal family `b`,
sending the `t`-th coordinate to the direction `b t` for `t < 3`. -/
noncomputable def emb {n : ℕ} (hn : 3 ≤ n) (b : Fin n → E) (x : E3) : E :=
  ∑ t : Fin 3, x t • b (Fin.castLE hn t)

private lemma castLE_inj {n : ℕ} (hn : 3 ≤ n) : Function.Injective (Fin.castLE hn) :=
  fun _ _ h => by simpa [Fin.ext_iff] using h

lemma inner_emb {n : ℕ} (hn : 3 ≤ n) {b : Fin n → E} (hb : Orthonormal ℝ b) (x y : E3) :
    ⟪emb hn b x, emb hn b y⟫ = ⟪x, y⟫ := by
  have hb' : Orthonormal ℝ (b ∘ Fin.castLE hn) := hb.comp _ (castLE_inj hn)
  have key := hb'.inner_sum (fun t => x t) (fun t => y t) Finset.univ
  simp only [Function.comp_apply] at key
  rw [emb, emb, key]
  simp [PiLp.inner_apply, mul_comm]

lemma inner_emb_basis {n : ℕ} (hn : 3 ≤ n) {b : Fin n → E} (hb : Orthonormal ℝ b) (x : E3)
    {m : Fin n} (hm : 3 ≤ (m : ℕ)) : ⟪emb hn b x, b m⟫ = 0 := by
  rw [emb, sum_inner]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [real_inner_smul_left, hb.2 (by simp [Fin.ext_iff]; omega), mul_zero]

/-- If a valuation `f` is `true` at exactly one member of every orthonormal basis, and if
`b` is an orthonormal basis all of whose members except `b z` are given the value `false`,
then restricting `f` to the three-dimensional subspace spanned by `b 0, b 1, b 2`
(which contains `b z`) yields a three-dimensional frame function, which is impossible. -/
private lemma reduction {n : ℕ} (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool)
    (H : ∀ v : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ v → ∃! i, f (v i) = true)
    {b : Fin n → EuclideanSpace ℝ (Fin n)} (hb : Orthonormal ℝ b)
    {z : Fin n} (hzval : (z : ℕ) = 0)
    (hbfalse : ∀ m : Fin n, m ≠ z → f (b m) = false) : False := by
  refine no_frame_function_three (fun x => f (emb hn b x)) ?_
  intro v hv
  set w : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun m => if h : (m : ℕ) < 3 then emb hn b (v ⟨m, h⟩) else b m with hw
  have hvite := orthonormal_iff_ite.1 hv
  have hbite := orthonormal_iff_ite.1 hb
  have hwo : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : (i : ℕ) < 3 <;> by_cases hj : (j : ℕ) < 3 <;>
      simp only [hw, dif_pos, hi, hj, dite_false]
    · rw [inner_emb hn hb, hvite]
      congr 1
      simp [Fin.ext_iff]
    · rw [inner_emb_basis hn hb _ (by omega), if_neg (by rintro rfl; omega)]
    · rw [real_inner_comm, inner_emb_basis hn hb _ (by omega), if_neg (by rintro rfl; omega)]
    · exact hbite i j
  obtain ⟨M, hM, hMu⟩ := H w hwo
  have hM3 : (M : ℕ) < 3 := by
    by_contra hc
    have hwM : w M = b M := dif_neg hc
    rw [hwM, hbfalse M (by rintro rfl; omega)] at hM
    exact absurd hM (by simp)
  refine ⟨⟨M, hM3⟩, ?_, ?_⟩
  · have hwM : w M = emb hn b (v ⟨M, hM3⟩) := dif_pos hM3
    rw [hwM] at hM
    exact hM
  · intro j hj
    have hcast : w (Fin.castLE hn j) = emb hn b (v j) := by
      simp only [hw]
      rw [dif_pos (show ((Fin.castLE hn j : Fin n) : ℕ) < 3 by simp)]
      rfl
    have hjM := hMu (Fin.castLE hn j) (show f (w (Fin.castLE hn j)) = true by rw [hcast]; exact hj)
    exact Fin.ext (by simpa [Fin.ext_iff] using hjM)

/-- **The Kochen–Specker theorem.**  In dimension `n ≥ 3` there is no noncontextual
hidden-variable assignment: there is no map `f` assigning a truth value to each vector of
`ℝⁿ` such that every orthonormal basis contains exactly one vector with value `true`.

(Such an `f` is what a noncontextual assignment of definite outcomes to the rank-one
projections would provide: for a complete family of orthogonal rank-one projections
exactly one outcome must occur, independently of which basis the projection is measured in.) -/
theorem kochen_specker (n : ℕ) (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool) :
    ¬ ∀ v : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ v → ∃! i, f (v i) = true := by
  intro H
  set B : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  have hb0 : Orthonormal ℝ (fun i => B i) := B.orthonormal
  obtain ⟨i₀, hi₀, huniq₀⟩ := H _ hb0
  set z : Fin n := ⟨0, by omega⟩ with hz
  set σ : Equiv.Perm (Fin n) := Equiv.swap z i₀ with hσ
  set b : Fin n → EuclideanSpace ℝ (Fin n) := fun m => B (σ m) with hbdef
  have hb : Orthonormal ℝ b := hb0.comp σ σ.injective
  have hbfalse : ∀ m : Fin n, m ≠ z → f (b m) = false := by
    intro m hm
    by_contra hcon
    have htrue : f (b m) = true := by simpa using hcon
    have hσm := huniq₀ (σ m) (by simpa [hbdef] using htrue)
    exact hm (σ.injective (by simpa [hσ] using hσm))
  exact reduction hn f H hb (by simp [hz]) hbfalse

/-- **The Kochen–Specker theorem**, stated for orthonormal bases: in dimension `n ≥ 3`
no truth-value assignment makes exactly one member of each orthonormal basis `true`. -/
theorem kochen_specker_orthonormalBasis (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → Bool) :
    ¬ ∀ B : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∃! i, f (B i) = true := by
  intro H
  refine kochen_specker n hn f ?_
  intro v hv
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let Bv := basisOfOrthonormalOfCardEqFinrank hv hcard
  have hcoe : ⇑Bv = v := coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  let OB := Bv.toOrthonormalBasis (by rw [hcoe]; exact hv)
  have hOB : ∀ i, OB i = v i := by
    intro i
    show (OB : Fin n → _) i = v i
    rw [Module.Basis.coe_toOrthonormalBasis, hcoe]
  obtain ⟨i, hi, hu⟩ := H OB
  exact ⟨i, by simp only [hOB] at hi; exact hi, fun j hj => hu j (by simp only [hOB]; exact hj)⟩

end Frontier

