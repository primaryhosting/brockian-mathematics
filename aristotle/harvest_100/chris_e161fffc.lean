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
open scoped InnerProductSpace

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

/-- The four dimensional real Hilbert space in which we work. -/
abbrev KSSpace : Type := EuclideanSpace ℝ (Fin 4)

/-- A vector of `KSSpace` given by its four coordinates. -/
noncomputable def ksVec (a b c d : ℝ) : KSSpace := WithLp.toLp 2 ![a, b, c, d]

lemma ksVec_inner (a b c d a' b' c' d' : ℝ) :
    ⟪ksVec a b c d, ksVec a' b' c' d'⟫_ℝ = a * a' + b * b' + c * c' + d * d' := by
  simp [ksVec, PiLp.inner_apply, Fin.sum_univ_four]
  ring

lemma ksVec_ne_zero (a b c d : ℝ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    ksVec a b c d ≠ 0 := by
  intro hz
  have h0 := congrFun (congrArg WithLp.ofLp hz) 0
  have h1 := congrFun (congrArg WithLp.ofLp hz) 1
  have h2 := congrFun (congrArg WithLp.ofLp hz) 2
  have h3 := congrFun (congrArg WithLp.ofLp hz) 3
  simp [ksVec] at h0 h1 h2 h3
  rcases h with h | h | h | h <;> simp_all

/-- The `0/1`-valued weight attached to a vector by a candidate valuation `v`. -/
noncomputable def ksCount (v : KSSpace → Bool) (x : KSSpace) : ℕ := if v x = true then 1 else 0

/-- If `v` assigns the value `true` to exactly one member of each orthogonal basis, then the
weights of the four members of an orthogonal basis sum to `1`. -/
lemma ksCount_sum_eq_one (v : KSSpace → Bool)
    (hv : ∀ e : Fin 4 → KSSpace, (∀ i, e i ≠ 0) → (∀ i j, i ≠ j → ⟪e i, e j⟫_ℝ = 0) →
      ∃! i, v (e i) = true)
    (x0 x1 x2 x3 : KSSpace)
    (h0 : x0 ≠ 0) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (h3 : x3 ≠ 0)
    (o01 : ⟪x0, x1⟫_ℝ = 0) (o02 : ⟪x0, x2⟫_ℝ = 0) (o03 : ⟪x0, x3⟫_ℝ = 0)
    (o12 : ⟪x1, x2⟫_ℝ = 0) (o13 : ⟪x1, x3⟫_ℝ = 0) (o23 : ⟪x2, x3⟫_ℝ = 0) :
    ksCount v x0 + ksCount v x1 + ksCount v x2 + ksCount v x3 = 1 := by
  have hne : ∀ i : Fin 4, (![x0, x1, x2, x3] : Fin 4 → KSSpace) i ≠ 0 := by
    intro i; fin_cases i <;> simpa using ‹_›
  have hor : ∀ i j : Fin 4, i ≠ j →
      ⟪(![x0, x1, x2, x3] : Fin 4 → KSSpace) i,
        (![x0, x1, x2, x3] : Fin 4 → KSSpace) j⟫_ℝ = 0 := by
    have o10 : ⟪x1, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o01
    have o20 : ⟪x2, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o02
    have o30 : ⟪x3, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o03
    have o21 : ⟪x2, x1⟫_ℝ = 0 := by rw [real_inner_comm]; exact o12
    have o31 : ⟪x3, x1⟫_ℝ = 0 := by rw [real_inner_comm]; exact o13
    have o32 : ⟪x3, x2⟫_ℝ = 0 := by rw [real_inner_comm]; exact o23
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨i, hi, hu⟩ := hv _ hne hor
  have e0 : v x0 = true → (0 : Fin 4) = i := fun h => hu 0 (by simpa using h)
  have e1 : v x1 = true → (1 : Fin 4) = i := fun h => hu 1 (by simpa using h)
  have e2 : v x2 = true → (2 : Fin 4) = i := fun h => hu 2 (by simpa using h)
  have e3 : v x3 = true → (3 : Fin 4) = i := fun h => hu 3 (by simpa using h)
  have c0 : ksCount v x0 = if (0 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (0 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e0 hc))]
  have c1 : ksCount v x1 = if (1 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (1 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e1 hc))]
  have c2 : ksCount v x2 = if (2 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (2 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e2 hc))]
  have c3 : ksCount v x3 = if (3 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (3 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e3 hc))]
  rw [c0, c1, c2, c3]
  fin_cases i <;> decide

/-- **Kochen–Specker theorem** (base case: dimension four).

There is no noncontextual hidden-variable assignment for quantum mechanics: no map `v` sending
each nonzero vector `x` of the four dimensional Hilbert space (equivalently, the rank-one
projection onto `ℝ ∙ x`) to a definite truth value `v x`, depending on the vector alone and not
on the measurement context, can have the property that in every orthogonal decomposition of the
identity into four rank-one projections exactly one projection is assigned the value `true`.

The proof is the parity argument of Cabello–Estebaranz–García-Alcaine, using 18 vectors arranged
into 9 orthogonal bases in which each vector occurs exactly twice. -/
theorem kochen_specker :
    ¬ ∃ v : EuclideanSpace ℝ (Fin 4) → Bool,
        ∀ e : Fin 4 → EuclideanSpace ℝ (Fin 4),
          (∀ i, e i ≠ 0) → (∀ i j : Fin 4, i ≠ j → ⟪e i, e j⟫_ℝ = 0) →
          ∃! i, v (e i) = true := by
  rintro ⟨v, hv⟩
  -- the eighteen vectors
  set u1 : KSSpace := ksVec 0 0 0 1 with hu1
  set u2 : KSSpace := ksVec 0 0 1 0 with hu2
  set u3 : KSSpace := ksVec 1 1 0 0 with hu3
  set u4 : KSSpace := ksVec 1 (-1) 0 0 with hu4
  set u5 : KSSpace := ksVec 0 1 0 0 with hu5
  set u6 : KSSpace := ksVec 1 0 1 0 with hu6
  set u7 : KSSpace := ksVec 1 0 (-1) 0 with hu7
  set u8 : KSSpace := ksVec 1 (-1) 1 (-1) with hu8
  set u9 : KSSpace := ksVec 1 (-1) (-1) 1 with hu9
  set u10 : KSSpace := ksVec 0 0 1 1 with hu10
  set u11 : KSSpace := ksVec 1 1 1 1 with hu11
  set u12 : KSSpace := ksVec 0 1 0 (-1) with hu12
  set u13 : KSSpace := ksVec 1 0 0 1 with hu13
  set u14 : KSSpace := ksVec 1 0 0 (-1) with hu14
  set u15 : KSSpace := ksVec 0 1 (-1) 0 with hu15
  set u16 : KSSpace := ksVec 1 1 (-1) 1 with hu16
  set u17 : KSSpace := ksVec 1 1 1 (-1) with hu17
  set u18 : KSSpace := ksVec (-1) 1 1 1 with hu18
  have b1 := ksCount_sum_eq_one v hv u1 u2 u3 u4
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu1, hu2, ksVec_inner]; norm_num) (by rw [hu1, hu3, ksVec_inner]; norm_num)
    (by rw [hu1, hu4, ksVec_inner]; norm_num) (by rw [hu2, hu3, ksVec_inner]; norm_num)
    (by rw [hu2, hu4, ksVec_inner]; norm_num) (by rw [hu3, hu4, ksVec_inner]; norm_num)
  have b2 := ksCount_sum_eq_one v hv u1 u5 u6 u7
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu1, hu5, ksVec_inner]; norm_num) (by rw [hu1, hu6, ksVec_inner]; norm_num)
    (by rw [hu1, hu7, ksVec_inner]; norm_num) (by rw [hu5, hu6, ksVec_inner]; norm_num)
    (by rw [hu5, hu7, ksVec_inner]; norm_num) (by rw [hu6, hu7, ksVec_inner]; norm_num)
  have b3 := ksCount_sum_eq_one v hv u8 u9 u3 u10
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu8, hu9, ksVec_inner]; norm_num) (by rw [hu8, hu3, ksVec_inner]; norm_num)
    (by rw [hu8, hu10, ksVec_inner]; norm_num) (by rw [hu9, hu3, ksVec_inner]; norm_num)
    (by rw [hu9, hu10, ksVec_inner]; norm_num) (by rw [hu3, hu10, ksVec_inner]; norm_num)
  have b4 := ksCount_sum_eq_one v hv u8 u11 u7 u12
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu8, hu11, ksVec_inner]; norm_num) (by rw [hu8, hu7, ksVec_inner]; norm_num)
    (by rw [hu8, hu12, ksVec_inner]; norm_num) (by rw [hu11, hu7, ksVec_inner]; norm_num)
    (by rw [hu11, hu12, ksVec_inner]; norm_num) (by rw [hu7, hu12, ksVec_inner]; norm_num)
  have b5 := ksCount_sum_eq_one v hv u2 u5 u13 u14
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu2, hu5, ksVec_inner]; norm_num) (by rw [hu2, hu13, ksVec_inner]; norm_num)
    (by rw [hu2, hu14, ksVec_inner]; norm_num) (by rw [hu5, hu13, ksVec_inner]; norm_num)
    (by rw [hu5, hu14, ksVec_inner]; norm_num) (by rw [hu13, hu14, ksVec_inner]; norm_num)
  have b6 := ksCount_sum_eq_one v hv u9 u11 u14 u15
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu9, hu11, ksVec_inner]; norm_num) (by rw [hu9, hu14, ksVec_inner]; norm_num)
    (by rw [hu9, hu15, ksVec_inner]; norm_num) (by rw [hu11, hu14, ksVec_inner]; norm_num)
    (by rw [hu11, hu15, ksVec_inner]; norm_num) (by rw [hu14, hu15, ksVec_inner]; norm_num)
  have b7 := ksCount_sum_eq_one v hv u16 u17 u4 u10
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu16, hu17, ksVec_inner]; norm_num) (by rw [hu16, hu4, ksVec_inner]; norm_num)
    (by rw [hu16, hu10, ksVec_inner]; norm_num) (by rw [hu17, hu4, ksVec_inner]; norm_num)
    (by rw [hu17, hu10, ksVec_inner]; norm_num) (by rw [hu4, hu10, ksVec_inner]; norm_num)
  have b8 := ksCount_sum_eq_one v hv u16 u18 u6 u12
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu16, hu18, ksVec_inner]; norm_num) (by rw [hu16, hu6, ksVec_inner]; norm_num)
    (by rw [hu16, hu12, ksVec_inner]; norm_num) (by rw [hu18, hu6, ksVec_inner]; norm_num)
    (by rw [hu18, hu12, ksVec_inner]; norm_num) (by rw [hu6, hu12, ksVec_inner]; norm_num)
  have b9 := ksCount_sum_eq_one v hv u17 u18 u13 u15
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (ksVec_ne_zero _ _ _ _ (by norm_num)) (ksVec_ne_zero _ _ _ _ (by norm_num))
    (by rw [hu17, hu18, ksVec_inner]; norm_num) (by rw [hu17, hu13, ksVec_inner]; norm_num)
    (by rw [hu17, hu15, ksVec_inner]; norm_num) (by rw [hu18, hu13, ksVec_inner]; norm_num)
    (by rw [hu18, hu15, ksVec_inner]; norm_num) (by rw [hu13, hu15, ksVec_inner]; norm_num)
  -- each of the 18 vectors occurs in exactly two of the nine bases, so the sum of the nine
  -- equations reads `2 * (total weight) = 9`, which is impossible.
  omega

/-- The Kochen–Specker theorem in its usual quantum-mechanical phrasing (base case: dimension
four): there is no scale-invariant assignment `v` of definite truth values to the rays of a four
dimensional Hilbert space such that every orthonormal basis contains exactly one ray of value
`true`. -/
theorem kochen_specker_orthonormal :
    ¬ ∃ v : EuclideanSpace ℝ (Fin 4) → Bool,
        (∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin 4)), 0 < c → v (c • x) = v x) ∧
        ∀ e : Fin 4 → EuclideanSpace ℝ (Fin 4), Orthonormal ℝ e → ∃! i, v (e i) = true := by
  rintro ⟨v, hscale, hbasis⟩
  refine kochen_specker ⟨v, ?_⟩
  intro e hne hor
  set f : Fin 4 → EuclideanSpace ℝ (Fin 4) := fun i => ‖e i‖⁻¹ • e i with hf
  have hpos : ∀ i, 0 < ‖e i‖⁻¹ := fun i => inv_pos.2 (norm_pos_iff.2 (hne i))
  have hvf : ∀ i, v (f i) = v (e i) := fun i => hscale _ _ (hpos i)
  have horth : Orthonormal ℝ f := by
    constructor
    · intro i
      rw [hf]
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hne i))]
    · intro i j hij
      rw [hf]
      simp only [real_inner_smul_left, real_inner_smul_right, hor i j hij]
      ring
  obtain ⟨i, hi, hu⟩ := hbasis f horth
  refine ⟨i, by rwa [hvf] at hi, fun j hj => hu j ?_⟩
  simp only [hvf]
  exact hj

end Frontier

