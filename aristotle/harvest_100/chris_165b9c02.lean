/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Proof outline

Write `E` for the orthogonal projection onto the range of `P` (so `tr E = rank P`), `Π` for the
spectral projection of `Q` onto its positive eigenvalues (so `tr Π = posIndex Q`), `S = 1 - Π`
and `R = S E S`.  Testing the Hermitian matrix `A = P + Q` against the Hermitian matrix
`B = c Π + (c/2) R` via `0 ≤ ‖A - B‖_F²` gives `2 tr (A B) - ‖B‖_F² ≤ ‖A‖_F²`.  Since `Π R = 0`,
`‖B‖_F² = c² tr Π + (c²/4) tr (R²)`, and `tr (R²) ≤ tr E` because
`E S E - (E S E)² = ((1 - E) S E)ᴴ ((1 - E) S E)` is positive semidefinite.  The linear term
splits into a `P`-part, `2 tr (P Π) + tr (P R) ≥ tr P`, which is exactly
`0 ≤ tr ((1 - E S E) P (1 - E S E))`, and a `Q`-part, `2 tr (Q Π) + tr (Q R) ≥ 2 tr Q`, which is
checked eigenvalue by eigenvalue using `0 ≤ R ≤ 1` and `R Π = 0`.
-/

namespace Zeta23Redux.LinAlg

open Matrix Finset
open scoped ComplexOrder

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/
noncomputable def rtrace (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace X).re

/-- The squared Frobenius norm `Re (trace (Xᴴ * X))` of a matrix. -/
noncomputable def frobSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hQ.eigenvalues i).card

/-! ### Basic facts about `rtrace` and `frobSq` -/

@[simp] lemma rtrace_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (X + Y) = rtrace X + rtrace Y := by
  simp [rtrace]

@[simp] lemma rtrace_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (X - Y) = rtrace X - rtrace Y := by
  simp [rtrace]

lemma rtrace_smul (t : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (((t : ℂ)) • X) = t * rtrace X := by
  simp [rtrace, Matrix.trace_smul]

lemma rtrace_comm (X Y : Matrix (Fin d) (Fin d) ℂ) : rtrace (X * Y) = rtrace (Y * X) := by
  unfold rtrace
  rw [Matrix.trace_mul_comm]

lemma rtrace_nonneg_of_posSemidef {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) :
    0 ≤ rtrace X := by
  have := hX.trace_nonneg
  simpa [rtrace] using (Complex.le_def.mp this).1

lemma frobSq_eq_rtrace (X : Matrix (Fin d) (Fin d) ℂ) : frobSq X = rtrace (Xᴴ * X) := rfl

lemma frobSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ frobSq X :=
  rtrace_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X)

/-- The key "test matrix" inequality: for Hermitian `A` and `B`,
`2⟪A, B⟫ - ‖B‖² ≤ ‖A‖²`. -/
lemma two_rtrace_mul_sub_frobSq_le {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : 2 * rtrace (A * B) - frobSq B ≤ frobSq A := by
  have h0 : 0 ≤ frobSq (A - B) := frobSq_nonneg _
  have hexp : frobSq (A - B) = frobSq A - 2 * rtrace (A * B) + frobSq B := by
    have h1 : (A - B)ᴴ = A - B := by
      rw [Matrix.conjTranspose_sub, hA.eq, hB.eq]
    have h2 : frobSq A = rtrace (A * A) := by
      rw [frobSq_eq_rtrace, hA.eq]
    have h3 : frobSq B = rtrace (B * B) := by
      rw [frobSq_eq_rtrace, hB.eq]
    rw [frobSq_eq_rtrace, h1, h2, h3, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      rtrace_sub, rtrace_sub, rtrace_sub, rtrace_comm B A]
    ring
  linarith

/-! ### Spectral functional calculus -/

/-- `sfc hA f` is `U * diagonal (f ∘ eigenvalues) * Uᴴ`, the functional calculus of the
Hermitian matrix `A` applied to `f`. -/
noncomputable def sfc {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => f (hA.eigenvalues i)) *
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)

variable {A : Matrix (Fin d) (Fin d) ℂ}

lemma u_mul_star (hA : A.IsHermitian) : (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2

lemma star_mul_u (hA : A.IsHermitian) : star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2

lemma sfc_mul (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    sfc hA f * sfc hA g = sfc hA (fun x => f x * g x) := by
  simp only [sfc, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * _) (star _) _,
    star_mul_u hA, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]

lemma sfc_add (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    sfc hA f + sfc hA g = sfc hA (fun x => f x + g x) := by
  simp [sfc, ← Matrix.add_mul, ← Matrix.mul_add, ← diagonal_add]

lemma sfc_sub (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    sfc hA f - sfc hA g = sfc hA (fun x => f x - g x) := by
  simp [sfc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← diagonal_sub]

lemma sfc_trace (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (sfc hA f).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [sfc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_u hA, Matrix.one_mul,
    trace_diagonal]

lemma sfc_conjTranspose (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (sfc hA f)ᴴ = sfc hA (fun x => starRingEnd ℂ (f x)) := by
  simp only [sfc, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def,
    RCLike.star_def]

lemma sfc_isHermitian (hA : A.IsHermitian) {f : ℝ → ℂ} (hf : ∀ x, starRingEnd ℂ (f x) = f x) :
    (sfc hA f).IsHermitian := by
  rw [Matrix.IsHermitian, sfc_conjTranspose hA]
  simp only [hf]

lemma sfc_self (hA : A.IsHermitian) : sfc hA (fun x => (x : ℂ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  simp [sfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma sfc_one (hA : A.IsHermitian) : sfc hA (fun _ => 1) = 1 := by
  simp [sfc, u_mul_star hA]

lemma sfc_posSemidef (hA : A.IsHermitian) {f : ℝ → ℂ} (hf : ∀ x, 0 ≤ f x) :
    (sfc hA f).PosSemidef := by
  have hd : (diagonal (fun i => f (hA.eigenvalues i))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => hf _)
  have := hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  simpa [sfc, Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using this

/-! ### The support projection of a positive semidefinite matrix -/

/-- The orthogonal projection onto the range of a Hermitian matrix. -/
noncomputable def suppProj (hA : A.IsHermitian) : Matrix (Fin d) (Fin d) ℂ :=
  sfc hA (fun x => if x = 0 then 0 else 1)

/-- The orthogonal projection onto the sum of eigenspaces with positive eigenvalue. -/
noncomputable def posProj (hA : A.IsHermitian) : Matrix (Fin d) (Fin d) ℂ :=
  sfc hA (fun x => if 0 < x then 1 else 0)

lemma suppProj_isHermitian (hA : A.IsHermitian) : (suppProj hA).IsHermitian := by
  refine sfc_isHermitian hA fun x => ?_
  by_cases h : x = 0 <;> simp [h]

lemma suppProj_mul_self (hA : A.IsHermitian) : suppProj hA * suppProj hA = suppProj hA := by
  rw [suppProj, sfc_mul]
  congr 1
  funext x
  by_cases h : x = 0 <;> simp [h]

lemma one_sub_suppProj_posSemidef (hA : A.IsHermitian) : (1 - suppProj hA).PosSemidef := by
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) - suppProj hA
      = sfc hA (fun x => if x = 0 then 1 else 0) := by
    rw [← sfc_one hA, suppProj, sfc_sub]
    congr 1
    funext x
    by_cases h : x = 0 <;> simp [h]
  rw [h1]
  refine sfc_posSemidef hA fun x => ?_
  by_cases h : x = 0 <;> simp [h]

lemma mul_suppProj (hA : A.IsHermitian) : A * suppProj hA = A := by
  have h := sfc_mul hA (fun x => (x : ℂ)) (fun x => if x = 0 then 0 else 1)
  rw [sfc_self hA] at h
  have h2 : (fun x : ℝ => (x : ℂ) * (if x = 0 then 0 else 1)) = fun x : ℝ => (x : ℂ) := by
    funext x; by_cases hx : x = 0 <;> simp [hx]
  rw [suppProj, h, h2, sfc_self hA]

lemma suppProj_mul (hA : A.IsHermitian) : suppProj hA * A = A := by
  have h := sfc_mul hA (fun x => if x = 0 then 0 else 1) (fun x => (x : ℂ))
  rw [sfc_self hA] at h
  have h2 : (fun x : ℝ => (if x = 0 then (0:ℂ) else 1) * (x : ℂ)) = fun x : ℝ => (x : ℂ) := by
    funext x; by_cases hx : x = 0 <;> simp [hx]
  rw [suppProj, h, h2, sfc_self hA]

lemma rtrace_suppProj (hA : A.IsHermitian) : rtrace (suppProj hA) = A.rank := by
  classical
  rw [rtrace, suppProj, sfc_trace]
  have h : (∑ i, if hA.eigenvalues i = 0 then (0 : ℂ) else 1)
      = ((Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℂ) := by
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by by_cases h : hA.eigenvalues i = 0 <;> simp [h]
  rw [h, Complex.natCast_re, hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]

lemma posProj_isHermitian (hA : A.IsHermitian) : (posProj hA).IsHermitian := by
  refine sfc_isHermitian hA fun x => ?_
  by_cases h : 0 < x <;> simp [h]

lemma posProj_mul_self (hA : A.IsHermitian) : posProj hA * posProj hA = posProj hA := by
  rw [posProj, sfc_mul]
  congr 1
  funext x
  by_cases h : 0 < x <;> simp [h]

lemma rtrace_posProj (hA : A.IsHermitian) : rtrace (posProj hA) = posIndex hA := by
  classical
  rw [rtrace, posProj, sfc_trace, posIndex]
  have h : (∑ i, if 0 < hA.eigenvalues i then (1 : ℂ) else 0)
      = ((Finset.univ.filter fun i => 0 < hA.eigenvalues i).card : ℂ) := by
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by by_cases h : 0 < hA.eigenvalues i <;> simp [h]
  rw [h, Complex.natCast_re]

lemma suppProj_posSemidef (hA : A.IsHermitian) : (suppProj hA).PosSemidef := by
  refine sfc_posSemidef hA fun x => ?_
  by_cases h : x = 0 <;> simp [h]

lemma posProj_posSemidef (hA : A.IsHermitian) : (posProj hA).PosSemidef := by
  refine sfc_posSemidef hA fun x => ?_
  by_cases h : 0 < x <;> simp [h]

/-! ### Bilinear bookkeeping for the test matrix -/

lemma frobSq_smul_add_smul {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (hXY : X * Y = 0) (hYX : Y * X = 0) (s t : ℝ) :
    frobSq (((s : ℂ)) • X + ((t : ℂ)) • Y) = s ^ 2 * frobSq X + t ^ 2 * frobSq Y := by
  have hh : (((s : ℂ)) • X + ((t : ℂ)) • Y)ᴴ = ((s : ℂ)) • X + ((t : ℂ)) • Y := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq, hY.eq]
  have hprod : (((s : ℂ)) • X + ((t : ℂ)) • Y) * (((s : ℂ)) • X + ((t : ℂ)) • Y)
      = (((s ^ 2 : ℝ) : ℂ)) • (X * X) + (((t ^ 2 : ℝ) : ℂ)) • (Y * Y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hXY, hYX,
      smul_zero, add_zero, zero_add, smul_smul]
    push_cast
    rw [sq, sq]
  rw [frobSq_eq_rtrace, hh, hprod, rtrace_add, rtrace_smul, rtrace_smul, frobSq_eq_rtrace,
    frobSq_eq_rtrace, hX.eq, hY.eq]

lemma rtrace_mul_smul_add_smul (A : Matrix (Fin d) (Fin d) ℂ) (X Y : Matrix (Fin d) (Fin d) ℂ)
    (s t : ℝ) :
    rtrace (A * (((s : ℂ)) • X + ((t : ℂ)) • Y)) = s * rtrace (A * X) + t * rtrace (A * Y) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, rtrace_add, rtrace_smul, rtrace_smul]

/-! ### The two main estimates -/

/-- The abstract form of the estimate coming from the positive semidefinite part `P`:
`0 ≤ tr (P (1 - E S E)²)`, where `E` is any Hermitian idempotent supporting `P`. -/
lemma p_part_aux {P E S : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hEh : E.IsHermitian)
    (hEE : E * E = E) (hEP : E * P = P) (hPE : P * E = P) (hS : S.IsHermitian) :
    0 ≤ rtrace P - 2 * rtrace (P * S) + rtrace (P * (S * E * S)) := by
  set G := E * S * E with hGdef
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hEh.eq, Matrix.mul_assoc]
  have hHh : ((1 : Matrix (Fin d) (Fin d) ℂ) - G)ᴴ = 1 - G := by
    rw [Matrix.conjTranspose_sub, hGh, Matrix.conjTranspose_one]
  have h0 : 0 ≤ rtrace ((1 - G)ᴴ * P * (1 - G)) :=
    rtrace_nonneg_of_posSemidef (hP.conjTranspose_mul_mul_same _)
  have hexp : (1 - G)ᴴ * P * (1 - G) = P - G * P - P * G + G * P * G := by
    rw [hHh]; noncomm_ring
  have eq2 : rtrace (P * G) = rtrace (P * S) := by
    have h : P * G = P * S * E := by
      rw [hGdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPE]
    rw [h, rtrace_comm, ← Matrix.mul_assoc, hEP]
  have eq1 : rtrace (G * P) = rtrace (P * S) := by
    have h : G * P = E * (S * P) := by
      rw [hGdef, Matrix.mul_assoc, hEP, Matrix.mul_assoc]
    rw [h, rtrace_comm, Matrix.mul_assoc, hPE, rtrace_comm]
  have eq3 : rtrace (G * P * G) = rtrace (P * (S * E * S)) := by
    have h1 : rtrace (G * P * G) = rtrace (P * (G * G)) := by
      rw [Matrix.mul_assoc, rtrace_comm, Matrix.mul_assoc]
    have h2 : G * G = E * S * E * S * E := by
      rw [hGdef, show (E * S * E) * (E * S * E) = E * S * (E * E) * S * E by noncomm_ring, hEE]
    have h3 : P * (E * S * E * S * E) = P * S * E * S * E := by
      rw [show P * (E * S * E * S * E) = (P * E) * (S * E * S * E) by noncomm_ring, hPE]
      noncomm_ring
    rw [h1, h2, h3, rtrace_comm,
      show E * (P * S * E * S) = (E * P) * (S * E * S) by noncomm_ring, hEP]
  rw [hexp] at h0
  simp only [rtrace_add, rtrace_sub] at h0
  rw [eq1, eq2, eq3] at h0
  linarith

/-- The estimate coming from the positive semidefinite part `P`. -/
lemma p_part {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) {S : Matrix (Fin d) (Fin d) ℂ}
    (hS : S.IsHermitian) :
    0 ≤ rtrace P - 2 * rtrace (P * S) + rtrace (P * (S * suppProj hP.isHermitian * S)) :=
  p_part_aux hP (suppProj_isHermitian _) (suppProj_mul_self _) (suppProj_mul _)
    (mul_suppProj _) hS

/-- The estimate coming from the Hermitian matrix `Q`. -/
lemma q_part {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) {R : Matrix (Fin d) (Fin d) ℂ}
    (hR : R.PosSemidef) (hR1 : (1 - R).PosSemidef) (hRP : R * posProj hQ = 0) :
    2 * rtrace Q ≤ 2 * rtrace (Q * posProj hQ) + rtrace (Q * R) := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hQ.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set W : Matrix (Fin d) (Fin d) ℂ := star U * R * U with hW
  have hUs : star U = Uᴴ := rfl
  have hUU : star U * U = 1 := star_mul_u hQ
  have hWpsd : W.PosSemidef := by rw [hW, hUs]; exact hR.conjTranspose_mul_mul_same U
  have hW1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - W).PosSemidef := by
    have h := hR1.conjTranspose_mul_mul_same U
    rw [← hUs, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUU, ← hW] at h
    exact h
  have hd0 : ∀ i, 0 ≤ (W i i).re := fun i => by
    simpa using (Complex.le_def.mp (hWpsd.diag_nonneg (i := i))).1
  have hd1 : ∀ i, (W i i).re ≤ 1 := fun i => by
    have h := (Complex.le_def.mp (hW1.diag_nonneg (i := i))).1
    simp [Matrix.sub_apply, Matrix.one_apply_eq] at h
    linarith
  set D : Matrix (Fin d) (Fin d) ℂ :=
    diagonal (fun i => if 0 < hQ.eigenvalues i then (1 : ℂ) else 0) with hD
  have hWD : W * D = 0 := by
    have h : star U * (R * posProj hQ) * U = W * D := by
      rw [posProj, sfc, ← hU, ← hD]
      rw [show star U * (R * (U * D * star U)) * U = (star U * R * U) * D * (star U * U) by
        noncomm_ring, hUU, Matrix.mul_one, ← hW]
    rw [hRP] at h
    simpa using h.symm
  have hzero : ∀ i, 0 < hQ.eigenvalues i → W i i = 0 := by
    intro i hi
    have h := congrFun (congrFun hWD i) i
    rw [hD, Matrix.mul_diagonal] at h
    simpa [hi] using h
  have htQ : rtrace Q = ∑ i, hQ.eigenvalues i := by
    rw [rtrace, hQ.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htQP : rtrace (Q * posProj hQ)
      = ∑ i, (if 0 < hQ.eigenvalues i then hQ.eigenvalues i else 0) := by
    have h1 := sfc_mul hQ (fun x => (x : ℂ)) (fun x => if 0 < x then 1 else 0)
    rw [sfc_self hQ] at h1
    rw [rtrace, posProj, h1, sfc_trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  have htQR : rtrace (Q * R) = ∑ i, hQ.eigenvalues i * (W i i).re := by
    have h1 : (Q * R).trace = (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * W).trace := by
      conv_lhs => rw [← sfc_self hQ]
      rw [sfc, ← hU, Matrix.trace_mul_comm]
      rw [show R * (U * diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * star U)
          = (R * U) * (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * star U) by noncomm_ring]
      rw [Matrix.trace_mul_comm]
      congr 1
      rw [hW]
      noncomm_ring
    rw [rtrace, h1,
      show (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * W).trace
        = ∑ i, ((hQ.eigenvalues i : ℝ) : ℂ) * W i i by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq],
      Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [htQ, htQP, htQR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : 0 < hQ.eigenvalues i
  · simp [h, hzero i h]
  · push_neg at h
    have h0 := hd0 i
    have h1 := hd1 i
    simp only [if_neg (not_lt.mpr h), mul_zero, zero_add]
    nlinarith

/-- The abstract Frobenius norm bound: for Hermitian idempotents `E` and `T`,
`tr (((1-T) E (1-T))²) ≤ tr E`. -/
lemma r_bound_aux {E T : Matrix (Fin d) (Fin d) ℂ} (hEh : E.IsHermitian) (hEE : E * E = E)
    (hTh : T.IsHermitian) (hTT : T * T = T) :
    rtrace (((1 - T) * E * (1 - T)) * ((1 - T) * E * (1 - T))) ≤ rtrace E := by
  set S : Matrix (Fin d) (Fin d) ℂ := 1 - T with hSdef
  have hSh : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_sub, hTh.eq, Matrix.conjTranspose_one]
  have hSS : S * S = S := by
    rw [hSdef,
      show ((1 : Matrix (Fin d) (Fin d) ℂ) - T) * (1 - T) = 1 - T - T + T * T by noncomm_ring, hTT]
    abel
  set G := E * S * E with hGdef
  have hRR : rtrace ((S * E * S) * (S * E * S)) = rtrace (E * S * E * S) := by
    rw [show (S * E * S) * (S * E * S) = S * (E * (S * S) * E * S) by noncomm_ring, hSS,
      rtrace_comm, show (E * S * E * S) * S = E * S * E * (S * S) by noncomm_ring, hSS]
  have e2 : G * G = E * S * E * S * E := by
    rw [hGdef, show (E * S * E) * (E * S * E) = E * S * (E * E) * S * E by noncomm_ring, hEE]
  have hGG : rtrace (G * G) = rtrace (E * S * E * S) := by
    rw [e2, rtrace_comm, show E * (E * S * E * S) = (E * E) * S * E * S by noncomm_ring, hEE]
  have hZ : G - G * G = ((1 - E) * S * E)ᴴ * ((1 - E) * S * E) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hEh.eq, hSh,
      Matrix.conjTranspose_sub, hEh.eq, Matrix.conjTranspose_one, e2, hGdef,
      show E * (S * (1 - E)) * ((1 - E) * S * E)
        = E * (S * S) * E - E * S * E * S * E - E * S * E * S * E + E * S * ((E * E) * S * E)
        by noncomm_ring, hSS, hEE]
    noncomm_ring
  have h1 : rtrace (G * G) ≤ rtrace G := by
    have h := rtrace_nonneg_of_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self ((1 - E) * S * E))
    rw [← hZ, rtrace_sub] at h
    linarith
  have h2 : rtrace G ≤ rtrace E := by
    have hET : 0 ≤ rtrace (E * T) := by
      have h := rtrace_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self (T * E))
      rw [Matrix.conjTranspose_mul, hEh.eq, hTh.eq] at h
      rw [show (E * T) * (T * E) = E * (T * T) * E by noncomm_ring, hTT, rtrace_comm,
        show E * (E * T) = (E * E) * T by noncomm_ring, hEE] at h
      exact h
    have hg : rtrace G = rtrace E - rtrace (E * T) := by
      rw [hGdef, rtrace_comm, show E * (E * S) = (E * E) * S by noncomm_ring, hEE, hSdef,
        Matrix.mul_sub, Matrix.mul_one, rtrace_sub]
    linarith
  rw [hRR, ← hGG]
  linarith

/-- The Frobenius norm bound on the "test matrix" piece built from the support projection. -/
lemma r_bound {P T : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hT : T.IsHermitian)
    (hT2 : T * T = T) :
    rtrace (((1 - T) * suppProj hP.isHermitian * (1 - T)) *
      ((1 - T) * suppProj hP.isHermitian * (1 - T))) ≤ rtrace (suppProj hP.isHermitian) :=
  r_bound_aux (suppProj_isHermitian _) (suppProj_mul_self _) hT hT2

/-! ### The main theorem -/

/-- **The rank-trace inequality**. For `P` positive semidefinite with `rank P ≤ r`, and `Q`
Hermitian with at most `b` strictly positive eigenvalues, and every `c > 0`,
`c * rtrace P - (c²/4) * r + 2 * c * rtrace Q - c² * b ≤ frobSq (P + Q)`. -/
theorem rank_trace_ineq {r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef)
    (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  have hEh : (suppProj hP.isHermitian).IsHermitian := suppProj_isHermitian _
  have hEpsd : (suppProj hP.isHermitian).PosSemidef := suppProj_posSemidef _
  have hE1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - suppProj hP.isHermitian).PosSemidef :=
    one_sub_suppProj_posSemidef _
  have hTh : (posProj hQ).IsHermitian := posProj_isHermitian hQ
  have hT2 : posProj hQ * posProj hQ = posProj hQ := posProj_mul_self hQ
  have hTpsd : (posProj hQ).PosSemidef := posProj_posSemidef hQ
  have hrb := r_bound hP hTh hT2
  have hpp := p_part hP (S := 1 - posProj hQ) (Matrix.isHermitian_one.sub hTh)
  set E := suppProj hP.isHermitian with hEdef
  set T := posProj hQ with hTdef
  set S : Matrix (Fin d) (Fin d) ℂ := 1 - T with hSdef
  have hSh : S.IsHermitian := Matrix.isHermitian_one.sub hTh
  have hSS : S * S = S := by
    rw [hSdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hT2]
    simp
  have hTS : T * S = 0 := by rw [hSdef, Matrix.mul_sub, hT2, Matrix.mul_one, sub_self]
  have hST : S * T = 0 := by rw [hSdef, Matrix.sub_mul, hT2, Matrix.one_mul, sub_self]
  set R := S * E * S with hRdef
  have hRh : R.IsHermitian := by
    show Rᴴ = R
    rw [hRdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh.eq, hEh.eq,
      Matrix.mul_assoc]
  have hRpsd : R.PosSemidef := by
    have h := hEpsd.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at h
  have hR1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - R).PosSemidef := by
    have h2 : (1 : Matrix (Fin d) (Fin d) ℂ) - R = T + S * (1 - E) * S := by
      have h3 : S * (1 - E) * S = S * S - S * E * S := by
        noncomm_ring
      rw [h3, hSS, ← hRdef, hSdef]
      abel
    rw [h2]
    refine hTpsd.add ?_
    have h := hE1.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at h
  have hTR : T * R = 0 := by
    rw [hRdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTS, Matrix.zero_mul, Matrix.zero_mul]
  have hRT : R * T = 0 := by rw [hRdef, Matrix.mul_assoc, hST, Matrix.mul_zero]
  set B := ((c : ℝ) : ℂ) • T + ((c / 2 : ℝ) : ℂ) • R with hBdef
  have hBh : B.IsHermitian := by
    show Bᴴ = B
    rw [hBdef, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      hTh.eq, hRh.eq]
    simp
  have hAh : (P + Q).IsHermitian := hP.isHermitian.add hQ
  have key := two_rtrace_mul_sub_frobSq_le hAh hBh
  -- the Frobenius norm of the test matrix
  have hfB : frobSq B = c ^ 2 * rtrace T + (c ^ 2 / 4) * rtrace (R * R) := by
    rw [hBdef, frobSq_smul_add_smul hTh hRh hTR hRT, frobSq_eq_rtrace, frobSq_eq_rtrace,
      hTh.eq, hRh.eq, hT2]
    ring
  -- the linear term
  have hlin : rtrace ((P + Q) * B)
      = c * (rtrace (P * T) + rtrace (Q * T)) + (c / 2) * (rtrace (P * R) + rtrace (Q * R)) := by
    rw [hBdef, rtrace_mul_smul_add_smul, Matrix.add_mul, Matrix.add_mul, rtrace_add, rtrace_add]
  -- the two estimates
  have hPS : rtrace (P * S) = rtrace P - rtrace (P * T) := by
    rw [hSdef, Matrix.mul_sub, Matrix.mul_one, rtrace_sub]
  rw [hPS] at hpp
  have hq := q_part hQ hRpsd hR1 hRT
  rw [← hTdef] at hq
  have hEr : rtrace E ≤ (r : ℝ) := by
    rw [hEdef, rtrace_suppProj]
    exact_mod_cast hr
  have hTb : rtrace T ≤ (b : ℝ) := by
    rw [hTdef, rtrace_posProj]
    exact_mod_cast hb
  -- combine
  have hA1 : c * rtrace P ≤ c * (2 * rtrace (P * T) + rtrace (P * R)) := by nlinarith
  have hA2 : 2 * c * rtrace Q ≤ c * (2 * rtrace (Q * T) + rtrace (Q * R)) := by nlinarith
  have hA3 : c ^ 2 * rtrace T ≤ c ^ 2 * b := by nlinarith [sq_nonneg c]
  have hA4 : (c ^ 2 / 4) * rtrace (R * R) ≤ (c ^ 2 / 4) * r := by nlinarith [sq_nonneg c]
  linarith

/-- The specialization of `rank_trace_ineq` at `c = 2`. -/
theorem rank_trace_ineq_two {r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef)
    (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  norm_num at this ⊢
  linarith

end Zeta23Redux.LinAlg

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

