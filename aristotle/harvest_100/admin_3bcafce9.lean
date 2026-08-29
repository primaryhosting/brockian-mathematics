import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/
noncomputable def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The reduced density matrix on the subsystem `A ⊗ B`, obtained by tracing out `C`. -/
noncomputable def ptrC (ρ : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun x y => ∑ c, ρ (x.1, x.2, c) (y.1, y.2, c)

/-- The reduced density matrix on the subsystem `B ⊗ C`, obtained by tracing out `A`. -/
noncomputable def ptrA (ρ : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (B × C) (B × C) ℂ :=
  fun x y => ∑ a, ρ (a, x.1, x.2) (a, y.1, y.2)

/-- The reduced density matrix on the subsystem `B`, obtained by tracing out `A` and `C`. -/
noncomputable def ptrAC (ρ : Matrix (A × B × C) (A × B × C) ℂ) : Matrix B B ℂ :=
  fun x y => ∑ a, ∑ c, ρ (a, x, c) (a, y, c)

/-! ## The entropy of a diagonal matrix -/

theorem isHermitian_diagonal_ofReal {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal fun i => (d i : ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [Matrix.diagonal_conjTranspose]

/-- The eigenvalue multiset of a real diagonal matrix is its diagonal, hence its von Neumann
entropy is the Shannon entropy of the diagonal. -/
theorem vonNeumannEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vonNeumannEntropy (Matrix.diagonal fun i => (d i : ℂ)) = ∑ i, Real.negMulLog (d i) := by
  have hH : (Matrix.diagonal fun i => (d i : ℂ)).IsHermitian := isHermitian_diagonal_ofReal d
  rw [vonNeumannEntropy, dif_pos hH]
  have h2 := hH.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun i => (Polynomial.X - Polynomial.C ((d i : ℂ)))) Finset.univ.val)
      = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val) by
          rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C] at h2
  have h3 : Multiset.map (fun (x : ℝ) => (x : ℂ)) (Multiset.map hH.eigenvalues Finset.univ.val)
      = Multiset.map (fun (x : ℝ) => (x : ℂ)) (Multiset.map d Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    exact h2.symm
  have h4 : Multiset.map hH.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val :=
    Multiset.map_injective (fun _ _ hab => Complex.ofReal_injective hab) h3
  calc ∑ i, Real.negMulLog (hH.eigenvalues i)
      = (Multiset.map Real.negMulLog (Multiset.map hH.eigenvalues Finset.univ.val)).sum := by
        rw [Multiset.map_map]; rfl
    _ = (Multiset.map Real.negMulLog (Multiset.map d Finset.univ.val)).sum := by rw [h4]
    _ = ∑ i, Real.negMulLog (d i) := by rw [Multiset.map_map]; rfl

/-! ## The classical (Shannon) strong subadditivity inequality -/

/-- Gibbs' inequality in pointwise form: `u * log (v / u) ≤ v - u`. -/
theorem gibbs_ineq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u * (Real.log v - Real.log u) ≤ v - u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at h
  calc u * (Real.log v - Real.log u) ≤ u * (v / u - 1) := mul_le_mul_of_nonneg_left h hu.le
    _ = v - u := by field_simp

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
/-- Strong subadditivity for the Shannon entropy of a nonnegative weight function on a
product of three finite sets, with the marginals given as explicit data. -/
theorem classical_ssa_aux (p : A × B × C → ℝ) (hp : ∀ x, 0 ≤ p x)
    (pAB : A → B → ℝ) (pBC : B → C → ℝ) (pB : B → ℝ)
    (hAB : ∀ a b, pAB a b = ∑ c, p (a, b, c))
    (hBC : ∀ b c, pBC b c = ∑ a, p (a, b, c))
    (hB : ∀ b, pB b = ∑ a, ∑ c, p (a, b, c)) :
    (∑ x, Real.negMulLog (p x)) + ∑ b, Real.negMulLog (pB b)
      ≤ (∑ a, ∑ b, Real.negMulLog (pAB a b)) + ∑ b, ∑ c, Real.negMulLog (pBC b c) := by
  have hpAB : ∀ a b, 0 ≤ pAB a b := fun a b => by
    rw [hAB]; exact Finset.sum_nonneg fun c _ => hp _
  have hpBC : ∀ b c, 0 ≤ pBC b c := fun b c => by
    rw [hBC]; exact Finset.sum_nonneg fun a _ => hp _
  have hpB : ∀ b, 0 ≤ pB b := fun b => by
    rw [hB]; exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => hp _
  have hmarg1 : ∀ b, ∑ a, pAB a b = pB b := fun b => by simp [hAB, hB]
  have hmarg2 : ∀ b, ∑ c, pBC b c = pB b := fun b => by
    simp only [hBC, hB]; exact Finset.sum_comm
  have htot : ∑ b, pB b = ∑ x : A × B × C, p x := by
    rw [Fintype.sum_prod_type]
    simp only [hB]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ =>
      (Fintype.sum_prod_type (f := fun y : B × C => p (a, y))).symm
  -- the pointwise Gibbs bound
  have key : ∀ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
      - Real.log (pB x.2.1) - Real.log (p x))
      ≤ pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1 - p x := by
    rintro ⟨a, b, c⟩
    simp only
    rcases eq_or_lt_of_le (hp (a, b, c)) with h0 | h0
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact div_nonneg (mul_nonneg (hpAB a b) (hpBC b c)) (hpB b)
    · have h1 : 0 < pAB a b := by
        rw [hAB]
        exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun c => p (a, b, c))
          (fun c _ => hp _) (Finset.mem_univ c))
      have h2 : 0 < pBC b c := by
        rw [hBC]
        exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun a => p (a, b, c))
          (fun a _ => hp _) (Finset.mem_univ a))
      have h3 : 0 < pB b := by
        rw [hB]
        refine lt_of_lt_of_le h0 ?_
        refine le_trans (Finset.single_le_sum (f := fun c => p (a, b, c))
          (fun c _ => hp _) (Finset.mem_univ c)) ?_
        exact Finset.single_le_sum (f := fun a => ∑ c, p (a, b, c))
          (fun a _ => Finset.sum_nonneg fun c _ => hp _) (Finset.mem_univ a)
      have hkey := gibbs_ineq h0 (div_pos (mul_pos h1 h2) h3)
      rw [Real.log_div (ne_of_gt (mul_pos h1 h2)) (ne_of_gt h3),
        Real.log_mul (ne_of_gt h1) (ne_of_gt h2)] at hkey
      linarith [hkey]
  -- the total mass of the comparison weight is at most that of `p`
  have hq : ∑ x : A × B × C, pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1 ≤ ∑ x, p x := by
    have inner : ∀ b : B, ∑ c, ∑ a, pAB a b * pBC b c / pB b ≤ pB b := by
      intro b
      have e1 : ∑ c, ∑ a, pAB a b * pBC b c / pB b = pB b * pB b / pB b := by
        have h : ∀ c : C, ∑ a, pAB a b * pBC b c / pB b = pB b * pBC b c / pB b := by
          intro c
          rw [← Finset.sum_div, ← Finset.sum_mul, hmarg1]
        rw [Finset.sum_congr rfl fun c _ => h c, ← Finset.sum_div, ← Finset.mul_sum, hmarg2]
      rw [e1]
      rcases eq_or_lt_of_le (hpB b) with h | h
      · simp [← h]
      · rw [mul_div_assoc, div_self (ne_of_gt h), mul_one]
    calc ∑ x : A × B × C, pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1
        = ∑ b, ∑ c, ∑ a, pAB a b * pBC b c / pB b := by
          rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
      _ ≤ ∑ b, pB b := Finset.sum_le_sum fun b _ => inner b
      _ = ∑ x, p x := htot
  -- the three marginal identities
  have E1 : ∑ x : A × B × C, p x * Real.log (pAB x.1 x.2.1)
      = ∑ a, ∑ b, pAB a b * Real.log (pAB a b) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hAB, Finset.sum_mul]
  have E2 : ∑ x : A × B × C, p x * Real.log (pBC x.2.1 x.2.2)
      = ∑ b, ∑ c, pBC b c * Real.log (pBC b c) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hBC, Finset.sum_mul]
  have E3 : ∑ x : A × B × C, p x * Real.log (pB x.2.1) = ∑ b, pB b * Real.log (pB b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hB, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Finset.sum_mul, ← hB]
  -- putting it together
  have expand : ∑ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
        - Real.log (pB x.2.1) - Real.log (p x))
      = (∑ x : A × B × C, p x * Real.log (pAB x.1 x.2.1))
        + (∑ x : A × B × C, p x * Real.log (pBC x.2.1 x.2.2))
        - (∑ x : A × B × C, p x * Real.log (pB x.2.1))
        - ∑ x : A × B × C, p x * Real.log (p x) := by
    simp only [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have main : ∑ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
      - Real.log (pB x.2.1) - Real.log (p x)) ≤ 0 := by
    refine le_trans (Finset.sum_le_sum fun x _ => key x) ?_
    rw [Finset.sum_sub_distrib]
    linarith [hq]
  simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  linarith [E1, E2, E3, expand, main]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
/-- Strong subadditivity for the Shannon entropy of a nonnegative weight function on a
product of three finite sets. -/
theorem classical_ssa (p : A × B × C → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, Real.negMulLog (p x)) + ∑ b, Real.negMulLog (∑ a, ∑ c, p (a, b, c))
      ≤ (∑ a, ∑ b, Real.negMulLog (∑ c, p (a, b, c)))
        + ∑ b, ∑ c, Real.negMulLog (∑ a, p (a, b, c)) :=
  classical_ssa_aux p hp _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

/-! ## Strong subadditivity -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai), for a tripartite
density matrix `ρ` on `A ⊗ B ⊗ C` that is diagonal in the product basis:
`S(ABC) + S(B) ≤ S(AB) + S(BC)`.

The normalisation hypothesis `htr : ρ.trace = 1` is part of the definition of a density
matrix; the proof does not actually need it. -/
theorem strong_subadditivity (ρ : Matrix (A × B × C) (A × B × C) ℂ)
    (hpos : ρ.PosSemidef) (htr : ρ.trace = 1) (hdiag : ∀ x y, x ≠ y → ρ x y = 0) :
    vonNeumannEntropy ρ + vonNeumannEntropy (ptrAC ρ)
      ≤ vonNeumannEntropy (ptrC ρ) + vonNeumannEntropy (ptrA ρ) := by
  set p : A × B × C → ℝ := fun x => (ρ x x).re with hp_def
  have hp : ∀ x, 0 ≤ p x := fun x => by
    have := hpos.diag_nonneg (i := x)
    exact (Complex.nonneg_iff.1 this).1
  have hentry : ∀ x, ρ x x = ((p x : ℝ) : ℂ) := fun x =>
    Complex.eq_re_of_ofReal_le (hpos.diag_nonneg (i := x))
  -- `ρ` and its three reduced density matrices are all diagonal
  have hρ : ρ = Matrix.diagonal fun x => ((p x : ℝ) : ℂ) := by
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [Matrix.diagonal_apply_eq, hentry]
    · rw [Matrix.diagonal_apply_ne _ hxy, hdiag x y hxy]
  have hC : ptrC ρ = Matrix.diagonal fun y : A × B => ((∑ c, p (y.1, y.2, c) : ℝ) : ℂ) := by
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [Matrix.diagonal_apply_eq]
      simp only [ptrC, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun c _ => hentry _
    · rw [Matrix.diagonal_apply_ne _ hxy]
      refine Finset.sum_eq_zero fun c _ => hdiag _ _ fun h => hxy ?_
      exact Prod.ext (congrArg (fun z : A × B × C => z.1) h)
        (congrArg (fun z : A × B × C => z.2.1) h)
  have hA : ptrA ρ = Matrix.diagonal fun y : B × C => ((∑ a, p (a, y.1, y.2) : ℝ) : ℂ) := by
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [Matrix.diagonal_apply_eq]
      simp only [ptrA, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun a _ => hentry _
    · rw [Matrix.diagonal_apply_ne _ hxy]
      refine Finset.sum_eq_zero fun a _ => hdiag _ _ fun h => hxy ?_
      exact Prod.ext (congrArg (fun z : A × B × C => z.2.1) h)
        (congrArg (fun z : A × B × C => z.2.2) h)
  have hAC : ptrAC ρ = Matrix.diagonal fun b : B => ((∑ a, ∑ c, p (a, b, c) : ℝ) : ℂ) := by
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [Matrix.diagonal_apply_eq]
      simp only [ptrAC, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hentry _
    · rw [Matrix.diagonal_apply_ne _ hxy]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ =>
        hdiag _ _ fun h => hxy (congrArg (fun z : A × B × C => z.2.1) h)
  -- reduce to the classical inequality
  rw [hC, hA, hAC, hρ, vonNeumannEntropy_diagonal, vonNeumannEntropy_diagonal,
    vonNeumannEntropy_diagonal, vonNeumannEntropy_diagonal]
  simpa [Fintype.sum_prod_type] using classical_ssa p hp

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

