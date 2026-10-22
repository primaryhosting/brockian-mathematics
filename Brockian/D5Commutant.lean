import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Brockian.D5Representation

/-!
# The commutant of the pentagon action

This file gives a coordinate proof of the classical commutant classification
for the five-vertex dihedral action. An invariant matrix is constant on the
three ordered-pair orbits: equal vertices, cyclic distance one, and cyclic
distance two. Consequently it has unique coefficients in `I, A₁, A₂`.

These are newly formalized integration results in this research package,
not claims of new mathematical or historical priority.
-/

open BigOperators

namespace Brockian.D5Commutant

noncomputable section

abbrev Vertex := Fin 5
abbrev VertexMatrix := Matrix Vertex Vertex ℂ

/-- The entries are invariant under every simultaneous rotation and under
simultaneous reflection. These transformations generate the full D₅ action. -/
def IsDihedralInvariant (M : VertexMatrix) : Prop :=
  (∀ k x y : Vertex, M (x + k) (y + k) = M x y) ∧
    ∀ x y : Vertex, M (-x) (-y) = M x y

/-- A matrix specified by its three ordered-pair orbits. -/
def orbitForm (a b c : ℂ) : VertexMatrix :=
  Matrix.of fun x y =>
    if y - x = 0 then a
    else if y - x = 1 ∨ y - x = -1 then b else c

/-- Adjacency at cyclic distance one. -/
def adjacencyOne : VertexMatrix :=
  Matrix.of fun x y => if y - x = 1 ∨ y - x = -1 then 1 else 0

/-- Adjacency at cyclic distance two. -/
def adjacencyTwo : VertexMatrix :=
  Matrix.of fun x y => if y - x = 2 ∨ y - x = -2 then 1 else 0

theorem orbitForm_invariant (a b c : ℂ) :
    IsDihedralInvariant (orbitForm a b c) := by
  constructor
  · intro k x y
    simp [orbitForm, add_sub_add_right_eq_sub]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp +decide [orbitForm]

/-- Explicit orbit classification; the coefficients are entries of row zero. -/
theorem invariant_eq_orbitForm {M : VertexMatrix} (hM : IsDihedralInvariant M) :
    M = orbitForm (M 0 0) (M 0 1) (M 0 2) := by
  have hrow (x y : Vertex) : M x y = M 0 (y - x) := by
    simpa [sub_eq_add_neg] using (hM.1 (-x) x y).symm
  have hfour : M 0 4 = M 0 1 := by
    simpa only [neg_zero, show -(1 : Vertex) = 4 from by decide] using hM.2 0 1
  have hthree : M 0 3 = M 0 2 := by
    simpa only [neg_zero, show -(2 : Vertex) = 3 from by decide] using hM.2 0 2
  ext x y
  change M x y =
    if y - x = 0 then M 0 0
    else if y - x = 1 ∨ y - x = -1 then M 0 1 else M 0 2
  rw [hrow x y]
  generalize y - x = d
  fin_cases d <;> simp +decide [hfour, hthree]

/-- The orbit form is exactly `a I + b A₁ + c A₂`. -/
theorem orbitForm_eq_linearCombination (a b c : ℂ) :
    orbitForm a b c =
      a • (1 : VertexMatrix) + b • adjacencyOne + c • adjacencyTwo := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp +decide [orbitForm, adjacencyOne, adjacencyTwo]

theorem invariant_iff_linearCombination (M : VertexMatrix) :
    IsDihedralInvariant M ↔
      ∃ a b c : ℂ,
        M = a • (1 : VertexMatrix) + b • adjacencyOne + c • adjacencyTwo := by
  constructor
  · intro hM
    exact ⟨M 0 0, M 0 1, M 0 2,
      (invariant_eq_orbitForm hM).trans (orbitForm_eq_linearCombination _ _ _)⟩
  · rintro ⟨a, b, c, rfl⟩
    rw [← orbitForm_eq_linearCombination]
    exact orbitForm_invariant a b c

/-- The three coefficients are unique; in particular these matrices form a
three-dimensional coordinate description of the commutant. -/
theorem linearCombination_injective {a b c a' b' c' : ℂ}
    (h : a • (1 : VertexMatrix) + b • adjacencyOne + c • adjacencyTwo =
      a' • (1 : VertexMatrix) + b' • adjacencyOne + c' • adjacencyTwo) :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [← orbitForm_eq_linearCombination, ← orbitForm_eq_linearCombination] at h
  have h0 := congrFun (congrFun h (0 : Vertex)) (0 : Vertex)
  have h1 := congrFun (congrFun h (0 : Vertex)) (1 : Vertex)
  have h2 := congrFun (congrFun h (0 : Vertex)) (2 : Vertex)
  simpa +decide [orbitForm] using And.intro h0 (And.intro h1 h2)

/-- A unique coefficient triple for every invariant matrix. -/
theorem invariant_exists_unique (M : VertexMatrix) (hM : IsDihedralInvariant M) :
    ∃! coeff : ℂ × ℂ × ℂ,
      M = coeff.1 • (1 : VertexMatrix) +
        coeff.2.1 • adjacencyOne + coeff.2.2 • adjacencyTwo := by
  refine ⟨(M 0 0, M 0 1, M 0 2), ?_, ?_⟩
  · exact (invariant_eq_orbitForm hM).trans (orbitForm_eq_linearCombination _ _ _)
  · rintro ⟨a, b, c⟩ h
    have hcanonical := (invariant_eq_orbitForm hM).trans
      (orbitForm_eq_linearCombination _ _ _)
    obtain ⟨ha, hb, hc⟩ := linearCombination_injective (h.symm.trans hcanonical)
    simp only [Prod.mk.injEq]
    exact ⟨ha, hb, hc⟩

/-- Pullback by a rotation on the vertex coordinates. -/
def rotationPull (k : Vertex) (f : Vertex → ℂ) : Vertex → ℂ :=
  fun x => f (x - k)

/-- Pullback matching Mathlib's `sr k` convention: the vertex map is `-k-x`. -/
def reflectionPull (k : Vertex) (f : Vertex → ℂ) : Vertex → ℂ :=
  fun x => f (-k - x)

/-- Commutation with all rotations and all reflections as actual operators. -/
def IsDihedralEquivariant (M : VertexMatrix) : Prop :=
  (∀ k f, M.mulVec (rotationPull k f) = rotationPull k (M.mulVec f)) ∧
    ∀ k f, M.mulVec (reflectionPull k f) = reflectionPull k (M.mulVec f)

/-- Matrix entries and permutation pullbacks give equivalent equivariance tests. -/
theorem mulVec_pull_comm_iff (M : VertexMatrix) (e : Equiv.Perm Vertex) :
    (∀ f : Vertex → ℂ,
      M.mulVec (fun x => f (e.symm x)) =
        fun x => M.mulVec f (e.symm x)) ↔
      ∀ x y, M (e x) (e y) = M x y := by
  constructor
  · intro h x y
    have hsingle :
        (fun z => (Pi.single y (1 : ℂ) : Vertex → ℂ) (e.symm z)) =
          Pi.single (e y) 1 := by
      funext z
      by_cases hz : z = e y
      · subst z
        simp
      · have he : e.symm z ≠ y := by
          intro he
          apply hz
          simpa using congrArg e he
        simp [hz, he]
    have hxy := congrFun (h (Pi.single y 1)) (e x)
    rw [hsingle] at hxy
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
      Equiv.symm_apply_apply] using hxy
  · intro h f
    funext x
    change (∑ y, M x y * f (e.symm y)) =
      ∑ y, M (e.symm x) y * f y
    calc
      (∑ y, M x y * f (e.symm y)) =
          ∑ y, M x (e y) * f y := by
        simpa only [Equiv.symm_apply_apply] using
          (Equiv.sum_comp e (fun y => M x y * f (e.symm y))).symm
      _ = ∑ y, M (e.symm x) y * f y := by
        apply Finset.sum_congr rfl
        intro y _
        have hxy := h (e.symm x) y
        simpa only [Equiv.apply_symm_apply] using congrArg (fun z => z * f y) hxy

/-- Reflection permutation in the `sr k` index convention. -/
def reflectionEquiv (k : Vertex) : Equiv.Perm Vertex where
  toFun x := -k - x
  invFun x := -k - x
  left_inv x := by simp [sub_eq_add_neg]
  right_inv x := by simp [sub_eq_add_neg]

theorem equivariant_iff_invariant (M : VertexMatrix) :
    IsDihedralEquivariant M ↔ IsDihedralInvariant M := by
  constructor
  · rintro ⟨hrot, href⟩
    constructor
    · intro k
      apply (mulVec_pull_comm_iff M (Equiv.addRight k)).mp
      intro f
      change M.mulVec (fun x => f (x + -k)) = fun x => M.mulVec f (x + -k)
      have h := hrot k f
      change M.mulVec (fun x => f (x - k)) = (fun x => M.mulVec f (x - k)) at h
      simpa only [sub_eq_add_neg] using h
    · have h := (mulVec_pull_comm_iff M (reflectionEquiv 0)).mp
        (by intro f; exact href 0 f)
      simpa [reflectionEquiv] using h
  · rintro ⟨hrot, href⟩
    constructor
    · intro k
      have h := (mulVec_pull_comm_iff M (Equiv.addRight k)).mpr (hrot k)
      intro f
      change M.mulVec (fun x => f (x - k)) = fun x => M.mulVec f (x - k)
      have hf := h f
      change M.mulVec (fun x => f (x + -k)) = (fun x => M.mulVec f (x + -k)) at hf
      simpa only [sub_eq_add_neg] using hf
    · intro k
      have hentry : ∀ x y,
          M (reflectionEquiv k x) (reflectionEquiv k y) = M x y := by
        intro x y
        change M (-k - x) (-k - y) = M x y
        calc
          M (-k - x) (-k - y) = M (-x + -k) (-y + -k) := by
            congr 1 <;> abel
          _ = M (-x) (-y) := hrot (-k) (-x) (-y)
          _ = M x y := href x y
      have h := (mulVec_pull_comm_iff M (reflectionEquiv k)).mpr hentry
      intro f
      exact h f

/-- Full five-vertex D₅ equivariance is precisely the three-parameter commutant. -/
theorem equivariant_iff_linearCombination (M : VertexMatrix) :
    IsDihedralEquivariant M ↔
      ∃ a b c : ℂ,
        M = a • (1 : VertexMatrix) + b • adjacencyOne + c • adjacencyTwo :=
  (equivariant_iff_invariant M).trans (invariant_iff_linearCombination M)

/-- Unique coefficients for an actual equivariant vertex operator. -/
theorem equivariant_exists_unique (M : VertexMatrix) (hM : IsDihedralEquivariant M) :
    ∃! coeff : ℂ × ℂ × ℂ,
      M = coeff.1 • (1 : VertexMatrix) +
        coeff.2.1 • adjacencyOne + coeff.2.2 • adjacencyTwo :=
  invariant_exists_unique M ((equivariant_iff_invariant M).mp hM)


/-- The distance-one adjacency as a linear map on the vertex space. -/
def adjacencyOneLinear : (Vertex → ℂ) →ₗ[ℂ] (Vertex → ℂ) :=
  Matrix.toLin' adjacencyOne

/-- The distance-two adjacency as a linear map on the vertex space. -/
def adjacencyTwoLinear : (Vertex → ℂ) →ₗ[ℂ] (Vertex → ℂ) :=
  Matrix.toLin' adjacencyTwo

theorem adjacencyOneLinear_apply (f : Vertex → ℂ) (x : Vertex) :
    adjacencyOneLinear f x = f (x - 1) + f (x + 1) := by
  fin_cases x <;>
    simp +decide [adjacencyOneLinear, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, adjacencyOne, add_comm] <;> first | rfl | ring

theorem adjacencyTwoLinear_apply (f : Vertex → ℂ) (x : Vertex) :
    adjacencyTwoLinear f x = f (x - 2) + f (x + 2) := by
  fin_cases x <;>
    simp +decide [adjacencyTwoLinear, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, adjacencyTwo, add_comm] <;> first | rfl | ring

/-- Positive Laplacian for the distance-one edges. -/
def laplacianOne : VertexMatrix := (2 : ℂ) • (1 : VertexMatrix) - adjacencyOne

/-- Positive Laplacian for the distance-two edges. -/
def laplacianTwo : VertexMatrix := (2 : ℂ) • (1 : VertexMatrix) - adjacencyTwo

theorem laplacianCombination_eq_orbitForm (a b : ℂ) :
    a • laplacianOne + b • laplacianTwo = orbitForm (2 * a + 2 * b) (-a) (-b) := by
  rw [orbitForm_eq_linearCombination]
  ext x y
  simp only [laplacianOne, laplacianTwo, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem laplacianCombination_injective {a b a' b' : ℂ}
    (h : a • laplacianOne + b • laplacianTwo =
      a' • laplacianOne + b' • laplacianTwo) :
    a = a' ∧ b = b' := by
  rw [laplacianCombination_eq_orbitForm, laplacianCombination_eq_orbitForm] at h
  have h1 := congrFun (congrFun h (0 : Vertex)) (1 : Vertex)
  have h2 := congrFun (congrFun h (0 : Vertex)) (2 : Vertex)
  simpa +decide [orbitForm] using And.intro h1 h2

/-- Actual real-matrix Markov conditions, expressed inside complex matrices:
real entries, zero row sums, and nonpositive off-diagonal entries. -/
def IsRealMarkovLaplacian (M : VertexMatrix) : Prop :=
  (∀ x y, (M x y).im = 0) ∧
    (∀ x, ∑ y, M x y = 0) ∧
      ∀ x y, x ≠ y → (M x y).re ≤ 0

theorem orbitForm_row_zero (a b c : ℂ) :
    (∑ y : Vertex, orbitForm a b c 0 y) = a + 2 * b + 2 * c := by
  simp +decide [orbitForm, Fin.sum_univ_succ]
  ring

/-- The cone generators give genuine Markov Laplacians for nonnegative rates. -/
theorem laplacianCombination_isRealMarkov (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsRealMarkovLaplacian ((a : ℂ) • laplacianOne + (b : ℂ) • laplacianTwo) := by
  rw [laplacianCombination_eq_orbitForm]
  constructor
  · intro x y
    fin_cases x <;> fin_cases y <;> simp +decide [orbitForm]
  · constructor
    · intro x
      fin_cases x <;> simp +decide [orbitForm, Fin.sum_univ_succ] <;> ring
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp +decide [orbitForm] at * <;> linarith

/-- Every fully invariant real Markov Laplacian has exactly two nonnegative
rates. The hypotheses are actual entry and row-sum conditions. -/
theorem invariant_markov_exists_unique (M : VertexMatrix)
    (hM : IsDihedralInvariant M) (hMarkov : IsRealMarkovLaplacian M) :
    ∃! rates : ℝ × ℝ, 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      M = (rates.1 : ℂ) • laplacianOne + (rates.2 : ℂ) • laplacianTwo := by
  have hm := invariant_eq_orbitForm hM
  have hrow : M 0 0 + 2 * M 0 1 + 2 * M 0 2 = 0 := by
    rw [← orbitForm_row_zero]
    rw [← hm]
    exact hMarkov.2.1 0
  have hb : ((M 0 1).re : ℂ) = M 0 1 := by
    apply Complex.ext <;> simp [hMarkov.1 0 1]
  have hc : ((M 0 2).re : ℂ) = M 0 2 := by
    apply Complex.ext <;> simp [hMarkov.1 0 2]
  have hnonneg1 : 0 ≤ -(M 0 1).re :=
    neg_nonneg.mpr (hMarkov.2.2 0 1 (by decide))
  have hnonneg2 : 0 ≤ -(M 0 2).re :=
    neg_nonneg.mpr (hMarkov.2.2 0 2 (by decide))
  have hcanonical : M =
      ((-(M 0 1).re : ℝ) : ℂ) • laplacianOne +
        ((-(M 0 2).re : ℝ) : ℂ) • laplacianTwo := by
    apply hm.trans
    rw [laplacianCombination_eq_orbitForm]
    congr 1
    · rw [Complex.ofReal_neg, Complex.ofReal_neg, hb, hc]
      linear_combination hrow
    · rw [Complex.ofReal_neg, neg_neg, hb]
    · rw [Complex.ofReal_neg, neg_neg, hc]
  refine ⟨(-(M 0 1).re, -(M 0 2).re), ⟨hnonneg1, hnonneg2, hcanonical⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨_, _, hab⟩
  have hcoeff := laplacianCombination_injective (hab.symm.trans hcanonical)
  exact Prod.ext (Complex.ofReal_injective hcoeff.1) (Complex.ofReal_injective hcoeff.2)

/-- The complete equivariant Markov cone, with nonnegative real parameters. -/
theorem equivariant_markov_iff (M : VertexMatrix) :
    (IsDihedralEquivariant M ∧ IsRealMarkovLaplacian M) ↔
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
        M = (a : ℂ) • laplacianOne + (b : ℂ) • laplacianTwo := by
  constructor
  · rintro ⟨hEquiv, hMarkov⟩
    obtain ⟨⟨a, b⟩, ⟨ha, hb, h⟩, _⟩ := invariant_markov_exists_unique M
      ((equivariant_iff_invariant M).mp hEquiv) hMarkov
    exact ⟨a, b, ha, hb, h⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine ⟨?_, laplacianCombination_isRealMarkov a b ha hb⟩
    apply (equivariant_iff_invariant _).mpr
    rw [laplacianCombination_eq_orbitForm]
    exact orbitForm_invariant _ _ _

/-- Uniqueness form of the complete equivariant Markov cone. -/
theorem equivariant_markov_exists_unique (M : VertexMatrix)
    (hM : IsDihedralEquivariant M) (hMarkov : IsRealMarkovLaplacian M) :
    ∃! rates : ℝ × ℝ, 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      M = (rates.1 : ℂ) • laplacianOne + (rates.2 : ℂ) • laplacianTwo :=
  invariant_markov_exists_unique M ((equivariant_iff_invariant M).mp hM) hMarkov



/-- The complete-graph Laplacian is the sum of the two cone generators. -/
theorem laplacian_sum_eq_complete :
    laplacianOne + laplacianTwo =
      (5 : ℂ) • (1 : VertexMatrix) - Matrix.of (fun _ _ => (1 : ℂ)) := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp +decide [laplacianOne, laplacianTwo, adjacencyOne, adjacencyTwo] <;> norm_num

/-! ## Connection to the pre-existing pentagon action -/

open DihedralGroup Brockian.D5Representation Brockian.Automorphism

theorem rotationPull_eq_d5Pull (k : Vertex) (f : Vertex → ℂ) :
    rotationPull k f = d5Pull (r k) f := by
  funext x
  simp [rotationPull, d5Pull_apply, dihedralHom_r, rotIso, rotEquiv, sub_eq_add_neg]

theorem reflectionPull_eq_d5Pull (k : Vertex) (f : Vertex → ℂ) :
    reflectionPull k f = d5Pull (sr k) f := by
  funext x
  simp [reflectionPull, d5Pull_apply, dihedralHom_sr, reflIso, reflEquiv]

/-- The coordinate criterion is exactly equivariance for the existing action,
not an unrelated matrix predicate. -/
theorem equivariant_iff_d5Pull (M : VertexMatrix) :
    IsDihedralEquivariant M ↔
      ∀ (g : DihedralGroup 5) (f : VertexSpace),
        M.mulVec (d5Pull g f) = d5Pull g (M.mulVec f) := by
  constructor
  · rintro ⟨hrot, href⟩ g f
    cases g with
    | r k =>
      simpa only [rotationPull_eq_d5Pull] using hrot k f
    | sr k =>
      simpa only [reflectionPull_eq_d5Pull] using href k f
  · intro h
    constructor
    · intro k f
      simpa only [rotationPull_eq_d5Pull] using h (r k) f
    · intro k f
      simpa only [reflectionPull_eq_d5Pull] using h (sr k) f

/-- Full D₅ equivariance for an arbitrary complex-linear endomorphism. -/
def IsD5EquivariantLinear (T : VertexSpace →ₗ[ℂ] VertexSpace) : Prop :=
  ∀ (g : DihedralGroup 5) (f : VertexSpace), T (d5Pull g f) = d5Pull g (T f)

theorem matrix_equivariant_iff_linear (T : VertexSpace →ₗ[ℂ] VertexSpace) :
    IsDihedralEquivariant (LinearMap.toMatrix' T) ↔ IsD5EquivariantLinear T := by
  rw [equivariant_iff_d5Pull]
  simp only [IsD5EquivariantLinear, LinearMap.toMatrix'_mulVec]

/-- The distance-one adjacency is the sum of the two existing rotation maps. -/
theorem adjacencyOneLinear_eq_rotations :
    adjacencyOneLinear = (d5Pull (r (1 : Fin 5))).toLinearMap +
      (d5Pull (r (-1 : Fin 5))).toLinearMap := by
  apply LinearMap.ext
  intro f
  funext x
  rw [adjacencyOneLinear_apply]
  change f (x - 1) + f (x + 1) =
    d5Pull (r (1 : Fin 5)) f x + d5Pull (r (-1 : Fin 5)) f x
  rw [← rotationPull_eq_d5Pull, ← rotationPull_eq_d5Pull]
  simp [rotationPull]

/-- The distance-two adjacency is the sum of the two existing double rotations. -/
theorem adjacencyTwoLinear_eq_rotations :
    adjacencyTwoLinear = (d5Pull (r (2 : Fin 5))).toLinearMap +
      (d5Pull (r (-2 : Fin 5))).toLinearMap := by
  apply LinearMap.ext
  intro f
  funext x
  rw [adjacencyTwoLinear_apply]
  change f (x - 2) + f (x + 2) =
    d5Pull (r (2 : Fin 5)) f x + d5Pull (r (-2 : Fin 5)) f x
  rw [← rotationPull_eq_d5Pull, ← rotationPull_eq_d5Pull]
  simp [rotationPull]

/-- Every complex D₅-equivariant endomorphism has unique coefficients
in the identity and the two distance adjacency operators. -/
theorem d5Equivariant_linear_exists_unique (T : VertexSpace →ₗ[ℂ] VertexSpace)
    (hT : IsD5EquivariantLinear T) :
    ∃! coeff : ℂ × ℂ × ℂ,
      T = coeff.1 • LinearMap.id +
        coeff.2.1 • adjacencyOneLinear + coeff.2.2 • adjacencyTwoLinear := by
  obtain ⟨coeff, hcoeff, huniq⟩ := equivariant_exists_unique
    (LinearMap.toMatrix' T) ((matrix_equivariant_iff_linear T).mpr hT)
  refine ⟨coeff, ?_, ?_⟩
  · have h := congrArg (fun M : VertexMatrix => Matrix.toLin' M) hcoeff
    simpa [adjacencyOneLinear, adjacencyTwoLinear] using h
  · intro other hother
    apply huniq
    have h := congrArg LinearMap.toMatrix' hother
    simpa [adjacencyOneLinear, adjacencyTwoLinear] using h

/-- The actual D₅ action and the actual Markov conditions imply the complete,
unique two-rate cone. -/
theorem d5Pull_markov_exists_unique (M : VertexMatrix)
    (hM : ∀ (g : DihedralGroup 5) (f : VertexSpace),
      M.mulVec (d5Pull g f) = d5Pull g (M.mulVec f))
    (hMarkov : IsRealMarkovLaplacian M) :
    ∃! rates : ℝ × ℝ, 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      M = (rates.1 : ℂ) • laplacianOne + (rates.2 : ℂ) • laplacianTwo :=
  equivariant_markov_exists_unique M ((equivariant_iff_d5Pull M).mpr hM) hMarkov

#print axioms d5Equivariant_linear_exists_unique
#print axioms d5Pull_markov_exists_unique


end

end Brockian.D5Commutant

