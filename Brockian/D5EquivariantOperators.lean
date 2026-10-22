import Brockian.D5RateBlocks
import Brockian.D5FourierInversion
import Brockian.Fin5InnerProduct

/-!
# Symmetric D₅ rates on the five-vertex representation

There are two independent rotation rates and five reflection rates. In the
paired cyclic Fourier coordinates `(v_j, v_{-j})`, their positive Laplacian
has matrix `d_j I - Q C_j`, where `C_j` is the Fourier transform of the
reflection rates. The resulting commutation criterion is an equality of
operators on the whole vertex space, obtained using Fourier inversion.

Here "symmetric rates" means inversion symmetry of group rates. Arbitrary
reflection rates do not make the resulting operator equivariant under every
element of D₅. Nonnegativity is needed for a Markov interpretation, but is
not needed for the algebraic identities in this file.
-/

open BigOperators DihedralGroup Complex
open Brockian.Automorphism
open Brockian.D5Representation Brockian.D5Isotypic
open Brockian.D5FourierInversion Brockian.Fin5InnerProduct
open Brockian.D5RateBlocks

namespace Brockian.D5RateOperators

noncomputable section

local notation "conjC" => (starRingEnd ℂ)

/-- All inversion-symmetric rates on D₅, omitting the ineffective identity rate. -/
structure SymmetricRates where
  rotationOne : ℝ
  rotationTwo : ℝ
  reflection : Fin 5 → ℝ

/-- The additional hypothesis that gives these data their Markov-rate meaning. -/
def SymmetricRates.Nonnegative (a : SymmetricRates) : Prop :=
  0 ≤ a.rotationOne ∧ 0 ≤ a.rotationTwo ∧ ∀ k, 0 ≤ a.reflection k

/-- Componentwise addition of a base rate vector and a rate increment. -/
def addRates (a b : SymmetricRates) : SymmetricRates where
  rotationOne := a.rotationOne + b.rotationOne
  rotationTwo := a.rotationTwo + b.rotationTwo
  reflection := fun k => a.reflection k + b.reflection k

theorem addRates_nonnegative {a b : SymmetricRates}
    (ha : a.Nonnegative) (hb : b.Nonnegative) : (addRates a b).Nonnegative :=
  ⟨add_nonneg ha.1 hb.1, add_nonneg ha.2.1 hb.2.1,
    fun k => add_nonneg (ha.2.2 k) (hb.2.2 k)⟩

def rotation (k : Fin 5) : VertexSpace →ₗ[ℂ] VertexSpace :=
  (d5Pull (r k)).toLinearMap

def reflection (k : Fin 5) : VertexSpace →ₗ[ℂ] VertexSpace :=
  (d5Pull (sr k)).toLinearMap

@[simp] theorem rotation_apply (k : Fin 5) (f : VertexSpace) :
    rotation k f = d5Pull (r k) f := rfl

@[simp] theorem reflection_apply (k : Fin 5) (f : VertexSpace) :
    reflection k f = d5Pull (sr k) f := rfl

theorem reflection_apply_coord (k : Fin 5) (f : VertexSpace) (x : Fin 5) :
    reflection k f x = f (-k - x) := by
  simp [reflection, d5Pull_apply, dihedralHom_sr, reflIso, reflEquiv]

theorem reflection_eigenmode (j k : Fin 5) :
    reflection k (eigenmode j) = omegaPow (-(j * k)) • eigenmode (-j) := by
  funext x
  simp only [reflection_apply_coord, eigenmode_apply, Pi.smul_apply, smul_eq_mul]
  rw [← omegaPow_add]
  congr 1
  simp only [sub_eq_add_neg, mul_add, mul_neg, neg_mul]

/-- The positive Laplacian for a rotation and its inverse. -/
def rotationPair (k : Fin 5) : VertexSpace →ₗ[ℂ] VertexSpace :=
  (2 : ℂ) • LinearMap.id - rotation k - rotation (-k)

def pairSymbol (k j : Fin 5) : ℂ :=
  2 - omegaPow (-(j * k)) - omegaPow (j * k)

theorem rotationPair_eigenmode (k j : Fin 5) :
    rotationPair k (eigenmode j) = pairSymbol k j • eigenmode j := by
  simp only [rotationPair, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, rotation_apply, d5Pull_r_eigenmode, mul_neg, neg_neg]
  funext x
  simp only [pairSymbol, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem pairSymbol_neg (k j : Fin 5) : pairSymbol k (-j) = pairSymbol k j := by
  simp only [pairSymbol, neg_mul, neg_neg]
  ring

theorem pairSymbol_conj (k j : Fin 5) : conjC (pairSymbol k j) = pairSymbol k j := by
  simp only [pairSymbol, map_sub, map_ofNat, conj_omegaPow, neg_neg]
  ring

def reflectionMass (b : Fin 5 → ℝ) : ℂ := ∑ k, (b k : ℂ)

theorem reflectionMass_conj (b : Fin 5 → ℝ) :
    conjC (reflectionMass b) = reflectionMass b := by
  simp [reflectionMass]

/-- The Fourier symbol of the real reflection-rate vector. -/
def reflectionSymbol (b : Fin 5 → ℝ) (j : Fin 5) : ℂ :=
  ∑ k, (b k : ℂ) * omegaPow (j * k)

theorem reflectionSymbol_neg (b : Fin 5 → ℝ) (j : Fin 5) :
    reflectionSymbol b (-j) = conjC (reflectionSymbol b j) := by
  simp only [reflectionSymbol, map_sum, map_mul, Complex.conj_ofReal,
    conj_omegaPow, neg_mul]

theorem reflectionSymbol_zero (b : Fin 5 → ℝ) :
    reflectionSymbol b 0 = reflectionMass b := by
  simp [reflectionSymbol, reflectionMass]

theorem reflectionCross_zero (b c : Fin 5 → ℝ) :
    (reflectionSymbol b 0 * conjC (reflectionSymbol c 0)).im = 0 := by
  apply (cross_eq_iff_im_zero _ _).mp
  rw [reflectionSymbol_zero, reflectionSymbol_zero,
    reflectionMass_conj, reflectionMass_conj]
  exact mul_comm _ _

theorem reflectionCross_neg_iff (b c : Fin 5 → ℝ) (j : Fin 5) :
    (reflectionSymbol b (-j) * conjC (reflectionSymbol c (-j))).im = 0 ↔
      (reflectionSymbol b j * conjC (reflectionSymbol c j)).im = 0 := by
  constructor
  · intro h
    have hc := (cross_eq_iff_im_zero
      (reflectionSymbol b (-j)) (reflectionSymbol c (-j))).mpr h
    simp only [reflectionSymbol_neg, starRingEnd_self_apply] at hc
    apply (cross_eq_iff_im_zero _ _).mp
    simpa only [mul_comm] using hc.symm
  · intro h
    have hc := (cross_eq_iff_im_zero (reflectionSymbol b j) (reflectionSymbol c j)).mpr h
    apply (cross_eq_iff_im_zero _ _).mp
    simp only [reflectionSymbol_neg, starRingEnd_self_apply]
    simpa only [mul_comm] using hc.symm

def reflectionPart (b : Fin 5 → ℝ) : VertexSpace →ₗ[ℂ] VertexSpace :=
  ∑ k, (b k : ℂ) • (LinearMap.id - reflection k)

theorem reflectionPart_add (b c : Fin 5 → ℝ) :
    reflectionPart (b + c) = reflectionPart b + reflectionPart c := by
  simp only [reflectionPart, Pi.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem reflectionPart_eigenmode (b : Fin 5 → ℝ) (j : Fin 5) :
    reflectionPart b (eigenmode j) =
      reflectionMass b • eigenmode j -
        conjC (reflectionSymbol b j) • eigenmode (-j) := by
  rw [← reflectionSymbol_neg]
  funext x
  simp only [reflectionPart, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, reflection_eigenmode,
    Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    reflectionMass, reflectionSymbol, neg_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]

/-- The positive Laplacian obtained from the seven independent symmetric rates. -/
def rateOperator (a : SymmetricRates) : VertexSpace →ₗ[ℂ] VertexSpace :=
  (a.rotationOne : ℂ) • rotationPair 1 +
    (a.rotationTwo : ℂ) • rotationPair 2 + reflectionPart a.reflection

theorem rateOperator_add (a b : SymmetricRates) :
    rateOperator (addRates a b) = rateOperator a + rateOperator b := by
  simp only [rateOperator, addRates, Complex.ofReal_add, add_smul,
    show (fun k => a.reflection k + b.reflection k) = a.reflection + b.reflection from rfl,
    reflectionPart_add]
  abel

/-- The actual coordinate action, expressed entirely using the seven real rates. -/
theorem rateOperator_apply_coord (a : SymmetricRates) (f : VertexSpace) (x : Fin 5) :
    rateOperator a f x =
      (a.rotationOne : ℂ) * (2 * f x - f (x - 1) - f (x + 1)) +
      (a.rotationTwo : ℂ) * (2 * f x - f (x - 2) - f (x + 2)) +
      ∑ k : Fin 5, (a.reflection k : ℂ) * (f x - f (-k - x)) := by
  simp only [rateOperator, rotationPair, reflectionPart,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.sum_apply, rotation_apply, d5Pull_r_apply,
    reflection_apply_coord, Finset.sum_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, sub_neg_eq_add]

/-- The same permutation-rate Laplacian acting on real-valued functions. -/
def realRateAction (a : SymmetricRates) (f : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun x =>
    a.rotationOne * (2 * f x - f (x - 1) - f (x + 1)) +
    a.rotationTwo * (2 * f x - f (x - 2) - f (x + 2)) +
    ∑ k : Fin 5, a.reflection k * (f x - f (-k - x))

/-- Complexification of the explicit real action is the actual D₅ rate operator. -/
theorem rateOperator_ofReal (a : SymmetricRates) (f : Fin 5 → ℝ) :
    rateOperator a (fun x => (f x : ℂ)) =
      fun x => (realRateAction a f x : ℂ) := by
  funext x
  rw [rateOperator_apply_coord]
  simp [realRateAction]

/-- The common diagonal entry of the paired Fourier block. -/
def scalarPart (a : SymmetricRates) (j : Fin 5) : ℂ :=
  (a.rotationOne : ℂ) * pairSymbol 1 j +
    (a.rotationTwo : ℂ) * pairSymbol 2 j + reflectionMass a.reflection

theorem scalarPart_neg (a : SymmetricRates) (j : Fin 5) :
    scalarPart a (-j) = scalarPart a j := by
  simp only [scalarPart, pairSymbol_neg]

theorem scalarPart_conj (a : SymmetricRates) (j : Fin 5) :
    conjC (scalarPart a j) = scalarPart a j := by
  simp only [scalarPart, map_add, map_mul, Complex.conj_ofReal,
    pairSymbol_conj, reflectionMass_conj]

theorem scalarPart_im (a : SymmetricRates) (j : Fin 5) :
    (scalarPart a j).im = 0 := by
  have h := congrArg Complex.im (scalarPart_conj a j)
  simp only [Complex.conj_im] at h
  linarith

/-- Exact action on the pre-existing cyclic Fourier eigenmodes. -/
theorem rateOperator_eigenmode (a : SymmetricRates) (j : Fin 5) :
    rateOperator a (eigenmode j) =
      scalarPart a j • eigenmode j -
        conjC (reflectionSymbol a.reflection j) • eigenmode (-j) := by
  simp only [rateOperator, LinearMap.add_apply, LinearMap.smul_apply,
    rotationPair_eigenmode, reflectionPart_eigenmode]
  funext x
  simp only [scalarPart, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Paired Fourier-coordinate map; injective for every nonzero frequency. -/
def pairedEmbedding (j : Fin 5) (z : Fin 2 → ℂ) : VertexSpace :=
  z 0 • eigenmode j + z 1 • eigenmode (-j)

theorem pairedEmbedding_injective {j : Fin 5} (hj : j ≠ 0) :
    Function.Injective (pairedEmbedding j) := by
  have hneg : j ≠ -j := by
    fin_cases j
    · exact (hj rfl).elim
    all_goals decide
  intro z w h
  have h0 := congrArg (fourierCoeff j) h
  have h1 := congrArg (fourierCoeff (-j)) h
  simp [pairedEmbedding, fourierCoeff_add, fourierCoeff_smul,
    fourierCoeff_eigenmode, hneg, hneg.symm] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The actual operator is intertwined with the explicit two-by-two rate block. -/
theorem rateOperator_pairedEmbedding (a : SymmetricRates) (j : Fin 5)
    (z : Fin 2 → ℂ) :
    rateOperator a (pairedEmbedding j z) =
      pairedEmbedding j
        ((rateBlock (scalarPart a j) (reflectionSymbol a.reflection j)).mulVec z) := by
  simp only [pairedEmbedding, map_add, map_smul, rateOperator_eigenmode,
    scalarPart_neg, reflectionSymbol_neg, neg_neg]
  funext x
  simp [rateBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The commutator is diagonal on each original cyclic Fourier mode. -/
theorem rateOperator_commutator_eigenmode (a b : SymmetricRates) (j : Fin 5) :
    ((rateOperator a).comp (rateOperator b) -
        (rateOperator b).comp (rateOperator a)) (eigenmode j) =
      (reflectionSymbol a.reflection j * conjC (reflectionSymbol b.reflection j) -
        reflectionSymbol b.reflection j * conjC (reflectionSymbol a.reflection j)) •
        eigenmode j := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, rateOperator_eigenmode,
    map_sub, map_smul, scalarPart_neg, reflectionSymbol_neg, neg_neg]
  funext x
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Fourier inversion upgrades equality on these modes to whole-space equality. -/
theorem linearMap_eq_of_eigenmodes (S T : VertexSpace →ₗ[ℂ] VertexSpace)
    (h : ∀ j : Fin 5, S (eigenmode j) = T (eigenmode j)) : S = T := by
  apply LinearMap.ext
  intro f
  calc
    S f = S (∑ j : Fin 5, fourierCoeff j f • eigenmode j) := by
      rw [fourier_inversion]
    _ = ∑ j : Fin 5, fourierCoeff j f • S (eigenmode j) := by
      simp only [map_sum, map_smul]
    _ = ∑ j : Fin 5, fourierCoeff j f • T (eigenmode j) := by
      simp_rw [h]
    _ = T (∑ j : Fin 5, fourierCoeff j f • eigenmode j) := by
      simp only [map_sum, map_smul]
    _ = T f := by rw [fourier_inversion]

/-- Necessary and sufficient commutation criterion on the entire vertex space. -/
theorem rateOperator_comp_comm_iff (a b : SymmetricRates) :
    (rateOperator a).comp (rateOperator b) = (rateOperator b).comp (rateOperator a) ↔
      ∀ j : Fin 5,
        (reflectionSymbol a.reflection j *
          conjC (reflectionSymbol b.reflection j)).im = 0 := by
  constructor
  · intro h j
    have hz : ((rateOperator a).comp (rateOperator b) -
        (rateOperator b).comp (rateOperator a)) (eigenmode j) = 0 := by
      rw [h, sub_self]
      rfl
    rw [rateOperator_commutator_eigenmode] at hz
    have hcoord := congrFun hz (0 : Fin 5)
    simp only [Pi.smul_apply, smul_eq_mul, eigenmode_apply, mul_zero,
      omegaPow_zero, mul_one, Pi.zero_apply] at hcoord
    exact (cross_eq_iff_im_zero _ _).mp (sub_eq_zero.mp hcoord)
  · intro h
    apply linearMap_eq_of_eigenmodes
    intro j
    have hc : reflectionSymbol a.reflection j * conjC (reflectionSymbol b.reflection j) -
        reflectionSymbol b.reflection j * conjC (reflectionSymbol a.reflection j) = 0 :=
      sub_eq_zero.mpr ((cross_eq_iff_im_zero _ _).mpr (h j))
    have hz := rateOperator_commutator_eigenmode a b j
    rw [hc, zero_smul] at hz
    exact sub_eq_zero.mp hz

theorem rateOperator_commute_iff (a b : SymmetricRates) :
    Commute (rateOperator a) (rateOperator b) ↔
      ∀ j : Fin 5,
        (reflectionSymbol a.reflection j *
          conjC (reflectionSymbol b.reflection j)).im = 0 :=
  rateOperator_comp_comm_iff a b

/-- Only the two nontrivial paired blocks need to be tested. -/
theorem rateOperator_commute_iff_two (a b : SymmetricRates) :
    Commute (rateOperator a) (rateOperator b) ↔
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0 := by
  rw [rateOperator_commute_iff]
  constructor
  · intro h
    exact ⟨h 1, h 2⟩
  · rintro ⟨h1, h2⟩ j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = -(1 : Fin 5) ∨ j = -(2 : Fin 5) := by
      fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact reflectionCross_zero _ _
    · exact h1
    · exact h2
    · exact (reflectionCross_neg_iff a.reflection b.reflection 1).mpr h1
    · exact (reflectionCross_neg_iff a.reflection b.reflection 2).mpr h2

/-- Restricting the complex commutation result gives commutation of the real actions. -/
theorem realRateAction_commute_of_rateOperator_commute (a b : SymmetricRates)
    (h : Commute (rateOperator a) (rateOperator b)) :
    Function.Commute (realRateAction a) (realRateAction b) := by
  intro f
  have hc :
      rateOperator a (rateOperator b (fun x => (f x : ℂ))) =
        rateOperator b (rateOperator a (fun x => (f x : ℂ))) :=
    congrArg (fun L : VertexSpace →ₗ[ℂ] VertexSpace => L (fun x => (f x : ℂ))) h.eq
  simp only [rateOperator_ofReal] at hc
  funext x
  exact Complex.ofReal_injective (congrFun hc x)

end

end Brockian.D5RateOperators
