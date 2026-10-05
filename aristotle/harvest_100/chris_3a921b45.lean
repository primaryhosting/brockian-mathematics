/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/
theorem exists_ratLinearMap_pos {S : Type*} [Fintype S] (x : S → ℝ) (hx : ∀ s, 0 < x s) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, ∀ s, 0 < f (x s) := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, fun s => (hS.false s).elim⟩
  -- a uniform positive lower bound for the finitely many positive reals `x s`
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ x s := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty x, ?_,
      fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    rw [Finset.lt_inf'_iff]
    intro s _
    exact hx s
  -- the `ℚ`-span of the `x s` is a finite dimensional `ℚ`-vector space
  set W := Submodule.span ℚ (Set.range x) with hWdef
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  set b := Module.finBasis ℚ W with hb
  set v : S → W := fun s => ⟨x s, Submodule.subset_span (Set.mem_range_self s)⟩ with hv
  set c : S → Fin (Module.finrank ℚ W) → ℚ := fun s i => b.repr (v s) i with hc
  have hxr : ∀ s, ∑ i, ((c s i : ℚ) : ℝ) * ((b i : W) : ℝ) = x s := by
    intro s
    have h1 : ∑ i, (b.repr (v s)) i • b i = v s := b.sum_repr (v s)
    have h2 : (((∑ i, (b.repr (v s)) i • b i : W)) : ℝ) = x s := by rw [h1]
    rw [AddSubmonoidClass.coe_finset_sum] at h2
    simp only [SetLike.val_smul, Rat.smul_def] at h2
    exact h2
  set D : ℝ := 1 + ∑ s, ∑ i, |((c s i : ℚ) : ℝ)| with hDdef
  have hD1 : (1:ℝ) ≤ D := by
    have : (0:ℝ) ≤ ∑ s, ∑ i, |((c s i : ℚ) : ℝ)| :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hD0 : (0:ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hcbound : ∀ s, ∑ i, |((c s i : ℚ) : ℝ)| ≤ D := by
    intro s
    have : ∑ i, |((c s i : ℚ) : ℝ)| ≤ ∑ t, ∑ i, |((c t i : ℚ) : ℝ)| :=
      Finset.single_le_sum (f := fun t => ∑ i, |((c t i : ℚ) : ℝ)|)
        (fun t _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ s)
    linarith
  -- rational approximations of the basis vectors
  set eps : ℝ := m / (2 * D) with hepsdef
  have heps : 0 < eps := div_pos hm0 (by linarith)
  have hqex : ∀ i, ∃ q : ℚ, |((b i : W) : ℝ) - (q:ℝ)| < eps := fun i => exists_rat_near _ heps
  choose q hq using hqex
  set f₀ : W →ₗ[ℚ] ℚ := ∑ i, q i • b.coord i with hf₀
  obtain ⟨f, hf⟩ := f₀.exists_extend
  refine ⟨f, fun s => ?_⟩
  have hfx : f (x s) = f₀ (v s) := by
    have := congrArg (fun g : W →ₗ[ℚ] ℚ => g (v s)) hf
    simpa [hv] using this
  have hval : f₀ (v s) = ∑ i, q i * c s i := by
    simp [hf₀, LinearMap.sum_apply, Module.Basis.coord_apply, hc]
  have hdiff : ((f₀ (v s) : ℚ) : ℝ) - x s
      = ∑ i, ((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ) := by
    rw [hval, ← hxr s]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hbound : |((f₀ (v s) : ℚ) : ℝ) - x s| ≤ m / 2 := by
    rw [hdiff]
    calc |∑ i, ((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ)|
        ≤ ∑ i, |((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, eps * |((c s i : ℚ) : ℝ)| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact (hq i).le) (abs_nonneg _)
      _ = eps * ∑ i, |((c s i : ℚ) : ℝ)| := by rw [Finset.mul_sum]
      _ ≤ eps * D := mul_le_mul_of_nonneg_left (hcbound s) heps.le
      _ = m / 2 := by rw [hepsdef]; field_simp
  have hpos : (0:ℝ) < ((f₀ (v s) : ℚ) : ℝ) := by
    have h1 := (abs_le.mp hbound).1
    have h2 := hm s
    linarith
  rw [hfx]
  exact_mod_cast hpos

/-! ## From a positive real null vector to a positive rational one -/

theorem exists_pos_rat_null {E S : Type*} [Fintype S] (A : Matrix E S ℤ) (x : S → ℝ)
    (hx : ∀ s, 0 < x s) (h : ∀ e, ∑ s, (A e s : ℝ) * x s = 0) :
    ∃ y : S → ℚ, (∀ s, 0 < y s) ∧ ∀ e, ∑ s, (A e s : ℚ) * y s = 0 := by
  obtain ⟨f, hf⟩ := exists_ratLinearMap_pos x hx
  refine ⟨fun s => f (x s), hf, fun e => ?_⟩
  have h0 : ∑ s, f (((A e s : ℚ) : ℝ) * x s) = 0 := by
    rw [← map_sum]
    have h1 : ∑ s, ((A e s : ℚ) : ℝ) * x s = 0 := by push_cast; exact h e
    rw [h1, map_zero]
  have h3 : ∑ s, (A e s : ℚ) * f (x s) = ∑ s, f (((A e s : ℚ) : ℝ) * x s) :=
    Finset.sum_congr rfl fun s _ => by rw [← Rat.smul_def, map_smul, smul_eq_mul]
  rw [h3, h0]

/-! ## Clearing denominators -/

theorem exists_pos_int_null {E S : Type*} [Fintype S] (A : Matrix E S ℤ) (y : S → ℚ)
    (hy : ∀ s, 0 < y s) (h : ∀ e, ∑ s, (A e s : ℚ) * y s = 0) :
    ∃ n : S → ℤ, (∀ s, 0 < n s) ∧ ∀ e, ∑ s, A e s * n s = 0 := by
  classical
  set d : ℕ := ∏ s, (y s).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun s _ => (y s).pos
  have key : ∀ s, ((d : ℚ)) * y s = ((((d : ℚ)) * y s).num : ℚ) := by
    intro s
    obtain ⟨k, hk⟩ : (y s).den ∣ d :=
      Finset.dvd_prod_of_mem (fun t => (y t).den) (Finset.mem_univ s)
    have hz : ∃ z : ℤ, ((d : ℚ)) * y s = (z : ℚ) := by
      refine ⟨k * (y s).num, ?_⟩
      have hstep : ((d : ℚ)) * y s = (k : ℚ) * (((y s).den : ℚ) * y s) := by
        rw [hk]; push_cast; ring
      rw [hstep, Rat.den_mul_eq_num]
      push_cast; ring
    obtain ⟨z, hzz⟩ := hz
    rw [hzz, Rat.num_intCast]
  refine ⟨fun s => (((d : ℚ)) * y s).num, fun s => ?_, fun e => ?_⟩
  · have hpos : (0:ℚ) < ((((d : ℚ)) * y s).num : ℚ) := by
      rw [← key s]
      exact mul_pos (by exact_mod_cast hdpos) (hy s)
    exact_mod_cast hpos
  · have hcast : ((∑ s, A e s * (((d : ℚ)) * y s).num : ℤ) : ℚ) = 0 := by
      push_cast
      have hstep : ∑ s, (A e s : ℚ) * ((((d : ℚ)) * y s).num : ℚ)
          = (d : ℚ) * ∑ s, (A e s : ℚ) * y s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← key s]; ring
      rw [hstep, h e, mul_zero]
    exact_mod_cast hcast

/-! ## The linear-algebra core -/

/-- For an integer matrix `A`, having a coordinatewise positive *real* null vector is
equivalent to having a coordinatewise positive *integer* null vector. -/
theorem Matrix.exists_pos_int_nullVector_iff {E S : Type*} [Fintype S] (A : Matrix E S ℤ) :
    (∃ x : S → ℝ, (∀ s, 0 < x s) ∧ (A.map (Int.cast : ℤ → ℝ)).mulVec x = 0) ↔
      (∃ n : S → ℤ, (∀ s, 0 < n s) ∧ A.mulVec n = 0) := by
  constructor
  · rintro ⟨x, hxpos, hx⟩
    have hx' : ∀ e, ∑ s, (A e s : ℝ) * x s = 0 := by
      intro e
      have := congrFun hx e
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
    obtain ⟨y, hypos, hy⟩ := exists_pos_rat_null A x hxpos hx'
    obtain ⟨n, hnpos, hn⟩ := exists_pos_int_null A y hypos hy
    exact ⟨n, hnpos, funext fun e => by simpa [Matrix.mulVec, dotProduct] using hn e⟩
  · rintro ⟨n, hnpos, hn⟩
    refine ⟨fun s => (n s : ℝ), fun s => Int.cast_pos.mpr (hnpos s), funext fun e => ?_⟩
    have hne := congrFun hn e
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hne ⊢
    have hcast : ((∑ s, A e s * n s : ℤ) : ℝ) = 0 := by exact_mod_cast hne
    push_cast at hcast
    simpa using hcast

/-! ## Chemical reactions -/

/-- A chemical reaction: `atoms e s` is the number of atoms of element `e` in one formula
unit of species `s`, and `isProduct s` says whether the species `s` appears on the product
side of the reaction arrow (the remaining species being reactants). -/
structure Reaction (Elem Species : Type*) where
  /-- number of atoms of element `e` in one formula unit of species `s` -/
  atoms : Elem → Species → ℕ
  /-- `true` for products, `false` for reactants -/
  isProduct : Species → Bool

/-- The stoichiometric matrix of a reaction: atom counts, taken positively for products and
negatively for reactants. -/
def Reaction.stoich {Elem Species : Type*} (R : Reaction Elem Species) :
    Matrix Elem Species ℤ :=
  Matrix.of fun e s => if R.isProduct s then (R.atoms e s : ℤ) else -(R.atoms e s : ℤ)

/-- A reaction *balances* if one can assign a positive (real) amount to every species so
that every element is conserved, i.e. the amounts form a null vector of the stoichiometric
matrix. -/
def Reaction.Balances {Elem Species : Type*} [Fintype Species]
    (R : Reaction Elem Species) : Prop :=
  ∃ c : Species → ℝ, (∀ s, 0 < c s) ∧
    ((R.stoich).map (Int.cast : ℤ → ℝ)).mulVec c = 0

/-- **Balancing a chemical reaction is a nullspace problem.**  A reaction balances if and
only if its stoichiometric matrix admits a coordinatewise positive integer null vector,
i.e. a genuine set of stoichiometric coefficients. -/
theorem balance_nullspace {Elem Species : Type*} [Fintype Species]
    (R : Reaction Elem Species) :
    R.Balances ↔ ∃ n : Species → ℤ, (∀ s, 0 < n s) ∧ (R.stoich).mulVec n = 0 :=
  Matrix.exists_pos_int_nullVector_iff R.stoich

/-! ## A worked example: `2 H₂ + O₂ → 2 H₂O` -/

/-- The formation of water from hydrogen and oxygen.  The species are `H₂`, `O₂`, `H₂O`
(the first two being reactants), the elements are `H` and `O`. -/
def waterFormation : Reaction (Fin 2) (Fin 3) where
  atoms := ![![2, 0, 2], ![0, 2, 1]]
  isProduct := ![false, false, true]

/-- The reaction `2 H₂ + O₂ → 2 H₂O` balances; the witnessing null vector of the
stoichiometric matrix is `(2, 1, 2)`. -/
theorem waterFormation_balances : waterFormation.Balances := by
  rw [balance_nullspace]
  refine ⟨![2, 1, 2], by decide, funext fun e => ?_⟩
  fin_cases e <;>
    simp [Reaction.stoich, Matrix.mulVec, dotProduct, waterFormation, Fin.sum_univ_succ]

end Chem

