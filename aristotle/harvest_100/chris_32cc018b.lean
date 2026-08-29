/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/
noncomputable def vnEntropy {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

theorem isHermitian_diagonal_real {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : ℂ)).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Pi.star_apply])

/-- The eigenvalues of a real diagonal matrix are its diagonal entries (as a multiset). -/
theorem eigenvalues_diagonal_multiset {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ)
    (h : (diagonal fun i => ((d i : ℝ) : ℂ)).IsHermitian) :
    Multiset.map h.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
  have h1 := h.roots_charpoly_eq_eigenvalues
  have h2 : (diagonal fun i => ((d i : ℝ) : ℂ)).charpoly.roots
      = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [h1] at h2
  have h3 := congrArg (Multiset.map Complex.re) h2
  simpa [Multiset.map_map, Function.comp_def] using h3

/-- The von Neumann entropy of a matrix that is diagonal with real entries is the Shannon
entropy of its diagonal. -/
theorem vnEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (diagonal fun i => ((d i : ℝ) : ℂ)) = ∑ i, Real.negMulLog (d i) := by
  have h := isHermitian_diagonal_real d
  rw [vnEntropy, dif_pos h]
  have key := congrArg (fun m => (Multiset.map Real.negMulLog m).sum)
    (eigenvalues_diagonal_multiset d h)
  simpa [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using key

section Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-! ## Marginals of a joint distribution -/

/-- The `A × B` marginal of a distribution on `A × B × C`. -/
def margAB (p : A × B × C → ℝ) : A × B → ℝ := fun x => ∑ c, p (x.1, x.2, c)

/-- The `B × C` marginal of a distribution on `A × B × C`. -/
def margBC (p : A × B × C → ℝ) : B × C → ℝ := fun y => ∑ a, p (a, y)

/-- The `B` marginal of a distribution on `A × B × C`. -/
def margB (p : A × B × C → ℝ) : B → ℝ := fun b => ∑ a, ∑ c, p (a, b, c)

/-! ## Basic facts about marginals -/

variable (p : A × B × C → ℝ)

omit [Fintype B] in
theorem sum_margAB_eq_margB (b : B) : ∑ a, margAB p (a, b) = margB p b := rfl

omit [Fintype B] in
theorem sum_margBC_eq_margB (b : B) : ∑ c, margBC p (b, c) = margB p b := by
  simp only [margBC, margB]
  exact Finset.sum_comm

theorem sum_margB_eq (h : ∑ x, p x = 1) : ∑ b, margB p b = 1 := by
  rw [← h]
  simp only [margB, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype A] [Fintype B] in
theorem le_margAB (hp0 : ∀ x, 0 ≤ p x) (a : A) (b : B) (c : C) : p (a, b, c) ≤ margAB p (a, b) :=
  Finset.single_le_sum (f := fun c => p (a, b, c)) (fun _ _ => hp0 _) (mem_univ c)

omit [Fintype B] [Fintype C] in
theorem le_margBC (hp0 : ∀ x, 0 ≤ p x) (a : A) (b : B) (c : C) : p (a, b, c) ≤ margBC p (b, c) :=
  Finset.single_le_sum (f := fun a => p (a, b, c)) (fun _ _ => hp0 _) (mem_univ a)

omit [Fintype B] in
theorem le_margB (hp0 : ∀ x, 0 ≤ p x) (a : A) (b : B) (c : C) : p (a, b, c) ≤ margB p b :=
  le_trans (le_margAB p hp0 a b c) <| Finset.single_le_sum (f := fun a => margAB p (a, b))
    (fun _ _ => Finset.sum_nonneg fun _ _ => hp0 _) (mem_univ a)

omit [Fintype A] [Fintype B] in
theorem margAB_nonneg (hp0 : ∀ x, 0 ≤ p x) (y : A × B) : 0 ≤ margAB p y :=
  Finset.sum_nonneg fun _ _ => hp0 _

omit [Fintype B] [Fintype C] in
theorem margBC_nonneg (hp0 : ∀ x, 0 ≤ p x) (y : B × C) : 0 ≤ margBC p y :=
  Finset.sum_nonneg fun _ _ => hp0 _

omit [Fintype B] in
theorem margB_nonneg (hp0 : ∀ x, 0 ≤ p x) (b : B) : 0 ≤ margB p b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hp0 _

/-! ## The classical (Shannon) strong subadditivity inequality -/

/-- Pointwise Gibbs-type inequality: `p - q ≤ p * log (p / q)`. -/
theorem sub_le_mul_log_div {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ≠ 0 → v ≠ 0) :
    u - v ≤ u * Real.log (u / v) := by
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · simp [← hu0]; linarith
  · have hv0 : 0 < v := lt_of_le_of_ne hv (Ne.symm (h (ne_of_gt hu0)))
    have h1 : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (u / v) = -Real.log (v / u) := by
      rw [← Real.log_inv]; congr 1; field_simp
    have h3 : u * (v / u - 1) = v - u := by field_simp
    rw [h2]
    nlinarith [h1]

/-- The auxiliary (subnormalised) distribution `q(a,b,c) = p(a,b) p(b,c) / p(b)`. -/
theorem q_sum_le_one (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∑ x : A × B × C, margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1 ≤ 1 := by
  have step : ∑ x : A × B × C, margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1
      = ∑ b, (∑ a, margAB p (a, b)) * (∑ c, margBC p (b, c)) / margB p b := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [step]
  calc ∑ b, (∑ a, margAB p (a, b)) * (∑ c, margBC p (b, c)) / margB p b
      ≤ ∑ b, margB p b := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [sum_margAB_eq_margB, sum_margBC_eq_margB]
        rcases eq_or_lt_of_le (margB_nonneg p hp0 b) with h | h
        · simp [← h]
        · rw [mul_div_assoc, div_self (ne_of_gt h), mul_one]
    _ = 1 := sum_margB_eq p hp1

theorem sum_p_mul_log_margAB :
    ∑ x : A × B × C, p x * Real.log (margAB p (x.1, x.2.1))
      = ∑ y : A × B, margAB p y * Real.log (margAB p y) := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  rfl

theorem sum_p_mul_log_margBC :
    ∑ x : A × B × C, p x * Real.log (margBC p (x.2.1, x.2.2))
      = ∑ y : B × C, margBC p y * Real.log (margBC p y) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  rfl

theorem sum_p_mul_log_margB :
    ∑ x : A × B × C, p x * Real.log (margB p x.2.1)
      = ∑ b, margB p b * Real.log (margB p b) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [← Finset.sum_mul]
  rfl

/-- **Strong subadditivity for the Shannon entropy**:
`H(ABC) + H(B) ≤ H(AB) + H(BC)` for a probability distribution on `A × B × C`. -/
theorem shannon_strong_subadditivity (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    (∑ x, Real.negMulLog (p x)) + (∑ b, Real.negMulLog (margB p b)) ≤
      (∑ x, Real.negMulLog (margAB p x)) + (∑ y, Real.negMulLog (margBC p y)) := by
  set q : A × B × C → ℝ :=
    fun x => margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1 with hq
  have hqnn : ∀ x, 0 ≤ q x := fun x =>
    div_nonneg (mul_nonneg (margAB_nonneg p hp0 _) (margBC_nonneg p hp0 _)) (margB_nonneg p hp0 _)
  have hpos : ∀ x : A × B × C, p x ≠ 0 → 0 < q x := by
    rintro ⟨a, b, c⟩ hx
    have hx0 : 0 < p (a, b, c) := lt_of_le_of_ne (hp0 _) (Ne.symm hx)
    have h1 : 0 < margAB p (a, b) := lt_of_lt_of_le hx0 (le_margAB p hp0 a b c)
    have h2 : 0 < margBC p (b, c) := lt_of_lt_of_le hx0 (le_margBC p hp0 a b c)
    have h3 : 0 < margB p b := lt_of_lt_of_le hx0 (le_margB p hp0 a b c)
    exact div_pos (mul_pos h1 h2) h3
  -- Gibbs' inequality for the subnormalised distribution `q`
  have main : 0 ≤ ∑ x, p x * Real.log (p x / q x) := by
    have h1 : ∑ x : A × B × C, (p x - q x) ≤ ∑ x, p x * Real.log (p x / q x) :=
      Finset.sum_le_sum fun x _ =>
        sub_le_mul_log_div (hp0 x) (hqnn x) fun hx => ne_of_gt (hpos x hx)
    have h2 : ∑ x : A × B × C, (p x - q x) = 1 - ∑ x, q x := by
      rw [Finset.sum_sub_distrib, hp1]
    have h3 : ∑ x, q x ≤ 1 := q_sum_le_one p hp0 hp1
    linarith
  -- expand the summand
  have expand : ∑ x : A × B × C, p x * Real.log (p x / q x)
      = ((∑ x, p x * Real.log (p x)) - (∑ x, p x * Real.log (margAB p (x.1, x.2.1)))
        - (∑ x, p x * Real.log (margBC p (x.2.1, x.2.2)))) + ∑ x, p x * Real.log (margB p x.2.1) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨a, b, c⟩ := x
    by_cases hx : p (a, b, c) = 0
    · simp [hx]
    · have hx0 : 0 < p (a, b, c) := lt_of_le_of_ne (hp0 _) (Ne.symm hx)
      have h1 : 0 < margAB p (a, b) := lt_of_lt_of_le hx0 (le_margAB p hp0 a b c)
      have h2 : 0 < margBC p (b, c) := lt_of_lt_of_le hx0 (le_margBC p hp0 a b c)
      have h3 : 0 < margB p b := lt_of_lt_of_le hx0 (le_margB p hp0 a b c)
      have hqx : q (a, b, c) = margAB p (a, b) * margBC p (b, c) / margB p b := rfl
      rw [Real.log_div hx (ne_of_gt (hpos _ hx)), hqx,
        Real.log_div (ne_of_gt (mul_pos h1 h2)) (ne_of_gt h3),
        Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
      ring
  rw [sum_p_mul_log_margAB, sum_p_mul_log_margBC, sum_p_mul_log_margB] at expand
  -- rewrite entropies
  have e1 : ∑ x, Real.negMulLog (p x) = -∑ x : A × B × C, p x * Real.log (p x) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e2 : ∑ y, Real.negMulLog (margAB p y)
      = -∑ y : A × B, margAB p y * Real.log (margAB p y) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e3 : ∑ y, Real.negMulLog (margBC p y)
      = -∑ y : B × C, margBC p y * Real.log (margBC p y) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e4 : ∑ b, Real.negMulLog (margB p b) = -∑ b : B, margB p b * Real.log (margB p b) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  rw [e1, e2, e3, e4]
  rw [expand] at main
  linarith

end Classical

section Quantum

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-! ## Partial traces of a tripartite system -/

/-- Partial trace over the first factor `A` of a tripartite system `A ⊗ B ⊗ C`. -/
noncomputable def ptraceA (M : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (B × C) (B × C) ℂ :=
  fun x y => ∑ a, M (a, x) (a, y)

/-- Partial trace over the last factor `C` of a tripartite system `A ⊗ B ⊗ C`. -/
noncomputable def ptraceC (M : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun x y => ∑ c, M (x.1, x.2, c) (y.1, y.2, c)

/-- Partial trace over both `A` and `C` of a tripartite system `A ⊗ B ⊗ C`. -/
noncomputable def ptraceAC (M : Matrix (A × B × C) (A × B × C) ℂ) : Matrix B B ℂ :=
  fun x y => ∑ a, ∑ c, M (a, x, c) (a, y, c)

omit [Fintype A] [Fintype B] in
theorem ptraceC_diagonal (p : A × B × C → ℝ) :
    ptraceC (diagonal fun x => ((p x : ℝ) : ℂ)) = diagonal fun x => ((margAB p x : ℝ) : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [ptraceC, margAB, diagonal_apply_eq, Complex.ofReal_sum]
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [diagonal_apply_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h1 h2
    exact absurd (Prod.ext h1 h2) h

omit [Fintype B] [Fintype C] in
theorem ptraceA_diagonal (p : A × B × C → ℝ) :
    ptraceA (diagonal fun x => ((p x : ℝ) : ℂ)) = diagonal fun y => ((margBC p y : ℝ) : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [ptraceA, margBC, diagonal_apply_eq, Complex.ofReal_sum]
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [diagonal_apply_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _ h2
    exact absurd h2 h

omit [Fintype B] in
theorem ptraceAC_diagonal (p : A × B × C → ℝ) :
    ptraceAC (diagonal fun x => ((p x : ℝ) : ℂ)) = diagonal fun b => ((margB p b : ℝ) : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [ptraceAC, margB, diagonal_apply_eq, Complex.ofReal_sum]
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun a _ => ?_
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [diagonal_apply_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _ h2 _
    exact absurd h2 h

variable (p : A × B × C → ℝ)

/-! ## Strong subadditivity of the von Neumann entropy -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai), for tripartite states
that are diagonal in a product basis.

If `ρ` is a density matrix on `A ⊗ B ⊗ C` which is diagonal in the product basis, with
diagonal given by a probability distribution `p`, then
`S(ABC) + S(B) ≤ S(AB) + S(BC)`,
where the subsystem states are the partial traces of `ρ`.

Note: only the case of states diagonal in a product basis is established here; the
general (noncommutative) Lieb–Ruskai inequality is not proved in this file. -/
theorem strong_subadditivity (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ρ : Matrix (A × B × C) (A × B × C) ℂ) (hρ : ρ = diagonal fun x => ((p x : ℝ) : ℂ)) :
    vnEntropy ρ + vnEntropy (ptraceAC ρ) ≤ vnEntropy (ptraceC ρ) + vnEntropy (ptraceA ρ) := by
  subst hρ
  rw [ptraceC_diagonal, ptraceA_diagonal, ptraceAC_diagonal, vnEntropy_diagonal,
    vnEntropy_diagonal, vnEntropy_diagonal, vnEntropy_diagonal]
  exact shannon_strong_subadditivity p hp0 hp1

end Quantum

end QI

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

