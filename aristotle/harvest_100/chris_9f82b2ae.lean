/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The Kochen–Specker theorem states that in a Hilbert space of dimension at least three there is
no noncontextual hidden-variable assignment: one cannot assign to every ray a value in `{0, 1}`,
independently of the measurement context, in such a way that every orthonormal basis contains
exactly one ray of value `1`.

We formalise the four dimensional case, which is the base case admitting a purely combinatorial
(parity) proof, due to Cabello, Estebaranz and García-Alcaine: there are `18` vectors in
`ℝ⁴` arranged into `9` orthogonal frames so that every vector lies in exactly two frames.
Summing the value `1` over the nine frames counts each vector twice, giving `9 = 2 * k`,
which is impossible.

The main statement is `Frontier.kochen_specker`, with `Frontier.kochen_specker_basis` an
equivalent restatement in terms of `OrthonormalBasis`.
-/

set_option maxHeartbeats 1000000

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of four vectors which is *orthogonal and nondegenerate*: the inner product of
`v i` and `v j` vanishes exactly when `i ≠ j`.  Equivalently, the `v i` are nonzero and
pairwise orthogonal. -/
def OrthFrame (v : Fin 4 → E) : Prop :=
  ∀ i j, inner ℝ (v i) (v j) = (0 : ℝ) ↔ i ≠ j

/-- If exactly one of four vectors receives the value `true`, the corresponding indicators
sum to `1`. -/
lemma count_eq_one {A : Type*} (F : A → Bool) (v : Fin 4 → A)
    (h : ∃! i, F (v i) = true) :
    (if F (v 0) = true then 1 else 0) + (if F (v 1) = true then 1 else 0) +
      (if F (v 2) = true then 1 else 0) + (if F (v 3) = true then 1 else 0) = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j : Fin 4, F (v j) = true ↔ j = i :=
    fun j => ⟨fun hj => hu j hj, fun hj => hj ▸ hi⟩
  rw [if_congr (key 0) rfl rfl, if_congr (key 1) rfl rfl, if_congr (key 2) rfl rfl,
    if_congr (key 3) rfl rfl]
  fin_cases i <;> decide

/-- Normalising an orthogonal frame yields an orthonormal family. -/
lemma orthonormal_normalize {v : Fin 4 → E} (hv : OrthFrame v) :
    Orthonormal ℝ (fun i => ‖v i‖⁻¹ • v i) := by
  have hne : ∀ i, v i ≠ 0 := by
    intro i hi
    have := (hv i i).mp
    simp [hi] at this
  refine ⟨fun i => norm_smul_inv_norm (hne i), ?_⟩
  intro i j hij
  simp only [real_inner_smul_left, real_inner_smul_right, (hv i j).mpr hij, mul_zero]

section Frames

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine configuration. -/
def ksv : Fin 18 → EuclideanSpace ℝ (Fin 4) :=
  ![!₂[0, 0, 0, 1], !₂[0, 0, 1, 0], !₂[1, 1, 0, 0], !₂[1, -1, 0, 0], !₂[0, 1, 0, 0],
    !₂[1, 0, 1, 0], !₂[1, 0, -1, 0], !₂[1, -1, 1, -1], !₂[1, -1, -1, 1], !₂[0, 0, 1, 1],
    !₂[1, 1, 1, 1], !₂[0, 1, 0, -1], !₂[1, 0, 0, 1], !₂[1, 0, 0, -1], !₂[0, 1, -1, 0],
    !₂[1, 1, -1, 1], !₂[1, 1, 1, -1], !₂[-1, 1, 1, 1]]

/-- The nine orthogonal frames of the configuration, given as index quadruples into `ksv`.
Each of the eighteen indices occurs in exactly two of the nine frames. -/
def ksb : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3], ![0, 4, 5, 6], ![7, 8, 2, 9], ![7, 10, 6, 11], ![1, 4, 12, 13],
    ![8, 10, 13, 14], ![15, 16, 3, 9], ![15, 17, 5, 11], ![16, 17, 12, 14]]

/-- Each of the nine listed quadruples really is an orthogonal frame. -/
lemma ksb_orthFrame (j : Fin 9) : OrthFrame (fun i => ksv (ksb j i)) := by
  fin_cases j <;>
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ksv, ksb, PiLp.inner_apply, Fin.sum_univ_four]

end Frames

/-- **Core combinatorial step.**  There is no `{0,1}`-assignment on the vectors of
`EuclideanSpace ℝ (Fin 4)` giving exactly one `1` in each orthogonal frame. -/
theorem no_frame_valuation (F : EuclideanSpace ℝ (Fin 4) → Bool) :
    ¬ ∀ v : Fin 4 → EuclideanSpace ℝ (Fin 4), OrthFrame v → ∃! i, F (v i) = true := by
  intro h
  set x : Fin 18 → ℕ := fun k => if F (ksv k) = true then 1 else 0 with hx
  have e : ∀ j : Fin 9, x (ksb j 0) + x (ksb j 1) + x (ksb j 2) + x (ksb j 3) = 1 :=
    fun j => count_eq_one F _ (h _ (ksb_orthFrame j))
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  have e6 := e 6
  have e7 := e 7
  have e8 := e 8
  simp only [ksb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val] at e0 e1 e2 e3 e4 e5 e6 e7 e8
  omega

/-- **Kochen–Specker theorem** (base case, dimension four).
There is no noncontextual hidden-variable assignment: there is no function `f` assigning to
every vector of a four dimensional real Hilbert space a value in `{0, 1}` (here `Bool`),
depending on the vector alone and not on the measurement context, such that in every
orthonormal basis exactly one vector receives the value `1`. -/
theorem kochen_specker :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 4) → Bool,
        ∀ v : Fin 4 → EuclideanSpace ℝ (Fin 4), Orthonormal ℝ v → ∃! i, f (v i) = true := by
  rintro ⟨f, hf⟩
  refine no_frame_valuation (fun x => f (‖x‖⁻¹ • x)) ?_
  intro v hv
  exact hf _ (orthonormal_normalize hv)

/-- Restatement of the Kochen–Specker theorem in terms of orthonormal bases: no
noncontextual assignment of values in `{0, 1}` to the vectors of a four dimensional real
Hilbert space gives exactly one `1` in every orthonormal basis. -/
theorem kochen_specker_basis (f : EuclideanSpace ℝ (Fin 4) → Bool) :
    ¬ ∀ b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)), ∃! i, f (b i) = true := by
  intro h
  refine kochen_specker ⟨f, ?_⟩
  intro v hv
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by simp
  have hb : Orthonormal ℝ ⇑(basisOfOrthonormalOfCardEqFinrank hv hcard) := by
    rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hv
  have hcoe : ⇑((basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis hb) = v := by
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  have := h ((basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis hb)
  rwa [hcoe] at this

end Frontier

/-
# Kochen Specker (all finite dimensions ≥ 4)
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.KochenSpecker

/-!
# Kochen–Specker in every finite dimension at least four

Starting from the four dimensional case `Frontier.kochen_specker`, we deduce the
Kochen–Specker theorem in every finite dimension `n ≥ 4`: for a real inner product space `E`
of finite dimension at least four there is no map `f : E → Bool` such that every orthonormal
basis of `E` contains exactly one vector of value `true`.

The reduction is the standard one.  Fix an orthonormal basis `b` of `E` and let `b k` be its
unique vector of value `true`.  Reindex so that `k` belongs to a distinguished four element
block; all basis vectors outside that block then have value `false`.  Every orthonormal
`4`-frame inside the span of the block, together with the basis vectors outside the block, is
again an orthonormal basis of `E`, hence carries exactly one `true`, which must sit in the
frame.  Thus `f` would induce a Kochen–Specker valuation in dimension four.
-/

set_option maxHeartbeats 1000000

namespace Frontier

open Module

section FrameMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The image of a vector of `EuclideanSpace ℝ (Fin 4)` under the frame `u`, i.e. the
coordinate map of the four dimensional subspace spanned by `u`. -/
noncomputable def frameMap (u : Fin 4 → E) (x : EuclideanSpace ℝ (Fin 4)) : E :=
  ∑ k, WithLp.ofLp x k • u k

/-- For an orthonormal frame `u`, `frameMap u` preserves inner products. -/
lemma inner_frameMap {u : Fin 4 → E} (hu : Orthonormal ℝ u) (x y : EuclideanSpace ℝ (Fin 4)) :
    inner ℝ (frameMap u x) (frameMap u y) = inner ℝ x y := by
  rw [frameMap, frameMap, hu.inner_sum]
  simp [PiLp.inner_apply, mul_comm]

/-- An orthonormal family stays orthonormal after applying `frameMap u`. -/
lemma orthonormal_frameMap {u : Fin 4 → E} (hu : Orthonormal ℝ u)
    {v : Fin 4 → EuclideanSpace ℝ (Fin 4)} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (fun i => frameMap u (v i)) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  rw [inner_frameMap hu, hv i j]

/-- A vector orthogonal to each member of the frame `u` is orthogonal to the whole range of
`frameMap u`. -/
lemma inner_frameMap_eq_zero {u : Fin 4 → E} {w : E} (hw : ∀ k, inner ℝ (u k) w = (0 : ℝ))
    (x : EuclideanSpace ℝ (Fin 4)) : inner ℝ (frameMap u x) w = (0 : ℝ) := by
  simp [frameMap, sum_inner, real_inner_smul_left, hw]

end FrameMap

/-- Uniqueness transported to the left summand when nothing in the right summand qualifies. -/
lemma existsUnique_inl {A B : Type*} {p : A ⊕ B → Prop} (h : ∃! s, p s)
    (hB : ∀ j, ¬ p (Sum.inr j)) : ∃! i, p (Sum.inl i) := by
  obtain ⟨s, hs, hu⟩ := h
  cases s with
  | inl i => exact ⟨i, hs, fun i' hi' => Sum.inl_injective (hu (Sum.inl i') hi')⟩
  | inr j => exact absurd hs (hB j)

/-- Transport of a unique-existence statement along an equivalence. -/
lemma existsUnique_of_equiv {A B : Type*} (e : A ≃ B) {p : A → Prop}
    (h : ∃! y, p (e.symm y)) : ∃! x, p x := by
  obtain ⟨y, hy, hu⟩ := h
  refine ⟨e.symm y, hy, fun x hx => ?_⟩
  have hxy : e x = y := hu (e x) (by simpa using hx)
  rw [← hxy, Equiv.symm_apply_apply]

/-- **Kochen–Specker theorem in every finite dimension `n ≥ 4`.**
If `E` is a real inner product space of finite dimension at least four, there is no
noncontextual assignment of values in `{0, 1}` (here `Bool`) to the vectors of `E` such that
every orthonormal basis of `E` contains exactly one vector of value `1`. -/
theorem kochen_specker_finrank_ge_four
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 4 ≤ finrank ℝ E) (f : E → Bool) :
    ¬ ∀ b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E, ∃! i, f (b i) = true := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = 4 + m := ⟨finrank ℝ E - 4, by omega⟩
  set b0 : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hb0
  obtain ⟨k, hk, hku⟩ := h b0
  set e0 : Fin 4 ⊕ Fin m ≃ Fin (finrank ℝ E) := finSumFinEquiv.trans (finCongr hm.symm) with he0
  set ε : Fin 4 ⊕ Fin m ≃ Fin (finrank ℝ E) := e0.trans (Equiv.swap (e0 (Sum.inl 0)) k) with hε
  have hεinl0 : ε (Sum.inl 0) = k := by simp [hε]
  set u : Fin 4 → E := fun i => b0 (ε (Sum.inl i)) with hu_def
  have hu : Orthonormal ℝ u :=
    b0.orthonormal.comp (fun i => ε (Sum.inl i)) (fun a b hab => by simpa using ε.injective hab)
  have hfalse : ∀ j : Fin m, f (b0 (ε (Sum.inr j))) = false := by
    intro j
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have hjk := hku _ hcon
    rw [← hεinl0] at hjk
    exact absurd (ε.injective hjk) (by simp)
  refine kochen_specker ⟨fun x => f (frameMap u x), ?_⟩
  intro v hv
  set w : Fin 4 ⊕ Fin m → E :=
    Sum.elim (fun i => frameMap u (v i)) (fun j => b0 (ε (Sum.inr j))) with hw_def
  have hperp : ∀ (i : Fin 4) (j : Fin m), inner ℝ (u i) (b0 (ε (Sum.inr j))) = (0 : ℝ) := by
    intro i j
    exact b0.orthonormal.2 (fun hcon => absurd (ε.injective hcon) (by simp))
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro s t
    cases s with
    | inl i =>
      cases t with
      | inl i' =>
        simpa [hw_def] using (orthonormal_iff_ite.mp (orthonormal_frameMap hu hv)) i i'
      | inr j =>
        simp only [hw_def, Sum.elim_inl, Sum.elim_inr]
        rw [inner_frameMap_eq_zero (fun kk => hperp kk j)]
        simp
    | inr j =>
      cases t with
      | inl i =>
        simp only [hw_def, Sum.elim_inl, Sum.elim_inr]
        rw [real_inner_comm, inner_frameMap_eq_zero (fun kk => hperp kk j)]
        simp
      | inr j' =>
        simp only [hw_def, Sum.elim_inr]
        rcases eq_or_ne j j' with rfl | hne
        · simp [b0.orthonormal.1 _]
        · have hne2 : ε (Sum.inr j) ≠ ε (Sum.inr j') :=
            fun hcon => hne (by simpa using ε.injective hcon)
          rw [b0.orthonormal.2 hne2]
          simp [hne]
  have hcard : Fintype.card (Fin 4 ⊕ Fin m) = finrank ℝ E := by simp [hm]
  set bb : OrthonormalBasis (Fin 4 ⊕ Fin m) ℝ E :=
    (basisOfOrthonormalOfCardEqFinrank hw hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hw) with hbb_def
  have hbb : ⇑bb = w := by
    rw [hbb_def, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  have h2 : ∃! s : Fin 4 ⊕ Fin m, f (w s) = true := by
    refine existsUnique_of_equiv e0 ?_
    simpa [OrthonormalBasis.reindex_apply, hbb] using h (bb.reindex e0)
  exact existsUnique_inl h2 (fun j => by simp [hw_def, hfalse j])

end Frontier

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

