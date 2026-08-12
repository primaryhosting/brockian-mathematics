/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/
def mform (x y : Spacetime) : ℝ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- The (bilinear, not sesquilinear) Minkowski form on complexified Minkowski space. -/
def cform (z w : CSpace) : ℂ := z 0 * w 0 - z 1 * w 1 - z 2 * w 2 - z 3 * w 3

/-- The embedding of real Minkowski space into its complexification. -/
def emb (x : Spacetime) : CSpace := fun mu => (x mu : ℂ)

lemma emb_neg (x : Spacetime) : emb (-x) = -emb x := by
  funext mu; simp [emb]

/-- A complex `4×4` matrix belongs to the complex Lorentz group when it preserves the
complex bilinear Minkowski form. -/
def IsComplexLorentz (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ z w : CSpace, cform (M *ᵥ z) (M *ᵥ w) = cform z w

/-! ### Total spacetime inversion lies in the identity component of `L(ℂ)`

The mathematical heart of the CPT theorem: although `-1` is *not* connected to the
identity inside the real proper orthochronous Lorentz group, it *is* connected to the
identity inside the complex Lorentz group.  Concretely, `-1` is the endpoint of the path
obtained by combining a boost with imaginary rapidity `iπ` in the `(0,1)` plane with an
ordinary rotation by `π` in the `(2,3)` plane. -/

/-- A continuous path of complex Lorentz transformations from the identity to `-1`. -/
noncomputable def inversionPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ (Real.cos (π * t) : ℂ), Complex.I * (Real.sin (π * t) : ℂ), 0, 0;
      Complex.I * (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ), 0, 0;
      0, 0, (Real.cos (π * t) : ℂ), -(Real.sin (π * t) : ℂ);
      0, 0, (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ) ]

lemma inversionPath_lorentz (t : ℝ) : IsComplexLorentz (inversionPath t) := by
  intro z w
  have hcs : Complex.cos ((π : ℂ) * (t : ℂ)) ^ 2 + Complex.sin ((π : ℂ) * (t : ℂ)) ^ 2 = 1 := by
    rw [add_comm]; exact Complex.sin_sq_add_cos_sq _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [cform, inversionPath, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (z 0 * w 0 - z 1 * w 1 - z 2 * w 2 - z 3 * w 3) * hcs
    + ((Complex.sin ((π : ℂ) * (t : ℂ))) ^ 2 * (z 1 * w 1 - z 0 * w 0)) * hI

lemma inversionPath_zero : inversionPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inversionPath]

lemma inversionPath_one : inversionPath 1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inversionPath]

lemma inversionPath_continuous : Continuous inversionPath := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [inversionPath] <;> fun_prop

/-- Total spacetime inversion `-1` (the CPT transformation) is joined to the identity by a
continuous path inside the complex Lorentz group. -/
theorem total_inversion_joined_to_id :
    ∃ L : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
      Continuous L ∧ L 0 = 1 ∧ L 1 = -1 ∧ ∀ t, IsComplexLorentz (L t) :=
  ⟨inversionPath, inversionPath_continuous, inversionPath_zero, inversionPath_one,
    inversionPath_lorentz⟩

/-! ## Jost points -/

/-- `x` is a *Jost point*: every nontrivial nonnegative combination of the consecutive
difference vectors `x k - x (k+1)` is spacelike.  At such configurations locality of the
field implies weak local commutativity. -/
def IsJostPoint {m : ℕ} (x : Fin (m + 1) → Spacetime) : Prop :=
  ∀ lam : Fin m → ℝ, (∀ k, 0 ≤ lam k) → (∃ k, 0 < lam k) →
    mform (∑ k, lam k • (x k.castSucc - x k.succ)) (∑ k, lam k • (x k.castSucc - x k.succ)) < 0

/-- Jost points exist: two points at spacelike separation form one. -/
theorem exists_jostPoint : ∃ x : Fin 2 → Spacetime, IsJostPoint x := by
  refine ⟨![0, ![0, 1, 0, 0]], ?_⟩
  intro lam _ hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : k = 0 := Subsingleton.elim _ _
  subst hk0
  have hv : (∑ k : Fin 1, lam k •
      ((![0, ![0, 1, 0, 0]] : Fin 2 → Spacetime) k.castSucc
        - (![0, ![0, 1, 0, 0]] : Fin 2 → Spacetime) k.succ))
      = ![0, -lam 0, 0, 0] := by
    funext mu
    fin_cases mu <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hv]
  have : mform ![0, -lam 0, 0, 0] ![0, -lam 0, 0, 0] = -(lam 0 * lam 0) := by
    simp [mform]
  rw [this]
  nlinarith [hk]

/-! ## Wightman theories and the CPT theorem -/

/-- A (scalar, hermitian) Wightman quantum field theory, described through its analytically
continued Wightman functions `W n : (Fin n → ℂ^4) → ℂ` on complexified Minkowski space.

The three axioms are:

* `bhw_covariance`: Lorentz invariance in the form supplied by the Bargmann–Hall–Wightman
  theorem — the analytic Wightman functions are invariant under every complex Lorentz
  transformation that can be reached from the identity by a continuous path inside the
  complex Lorentz group.  (For real proper orthochronous transformations this is ordinary
  Lorentz invariance; the extension to the complex group is the analytic input.)
* `hermiticity`: the hermiticity relation for the Wightman functions of a hermitian field,
  `conj W_n(x₁,…,x_n) = W_n(x_n,…,x₁)`.
* `weak_locality`: locality, in the form of weak local commutativity at Jost points,
  `W_n(x_n,…,x₁) = W_n(x₁,…,x_n)`. -/
structure WightmanTheory where
  /-- The analytic `n`-point Wightman functions. -/
  W : (n : ℕ) → (Fin n → CSpace) → ℂ
  bhw_covariance : ∀ L : ℝ → Matrix (Fin 4) (Fin 4) ℂ, Continuous L → L 0 = 1 →
    (∀ t, IsComplexLorentz (L t)) → ∀ (n : ℕ) (z : Fin n → CSpace),
      W n (fun i => L 1 *ᵥ z i) = W n z
  hermiticity : ∀ (n : ℕ) (x : Fin n → Spacetime),
    (starRingEnd ℂ) (W n fun i => emb (x i)) = W n fun i => emb (x i.rev)
  weak_locality : ∀ (m : ℕ) (x : Fin (m + 1) → Spacetime), IsJostPoint x →
    (W (m + 1) fun i => emb (x i.rev)) = W (m + 1) fun i => emb (x i)

/-- Invariance of the Wightman functions under total spacetime inversion `x ↦ -x`,
obtained from Lorentz invariance by continuing along a path in the complex Lorentz group. -/
theorem inversion_invariance (T : WightmanTheory) (n : ℕ) (z : Fin n → CSpace) :
    (T.W n fun i => -z i) = T.W n z := by
  have key : (fun i => -z i) = fun i => inversionPath 1 *ᵥ z i := by
    funext i
    rw [inversionPath_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [key]
  exact T.bhw_covariance inversionPath inversionPath_continuous inversionPath_zero
    inversionPath_lorentz n z

/-- **CPT theorem.**  For any Lorentz-invariant local quantum field theory (in the Wightman
sense), the Wightman functions are invariant under the CPT transformation, which reverses
the order of the arguments and negates all of them:
`W_n(-x_n, …, -x₁) = W_n(x₁, …, x_n)` at Jost points. -/
theorem cpt_theorem (T : WightmanTheory) {m : ℕ} (x : Fin (m + 1) → Spacetime)
    (hx : IsJostPoint x) :
    (T.W (m + 1) fun i => emb (-x i.rev)) = T.W (m + 1) fun i => emb (x i) := by
  have h1 : (fun i : Fin (m + 1) => emb (-x i.rev)) = fun i => -emb (x i.rev) := by
    funext i; rw [emb_neg]
  rw [h1, inversion_invariance T (m + 1) fun i => emb (x i.rev)]
  exact T.weak_locality m x hx

/-- The CPT relation in conjugated form: at Jost points the Wightman function of the
totally inverted configuration is the complex conjugate of the original one,
`W_n(-x₁, …, -x_n) = conj W_n(x₁, …, x_n)`. -/
theorem cpt_conjugation (T : WightmanTheory) {m : ℕ} (x : Fin (m + 1) → Spacetime)
    (hx : IsJostPoint x) :
    (T.W (m + 1) fun i => emb (-x i)) = (starRingEnd ℂ) (T.W (m + 1) fun i => emb (x i)) := by
  have h1 : (fun i : Fin (m + 1) => emb (-x i)) = fun i => -emb (x i) := by
    funext i; rw [emb_neg]
  rw [h1, inversion_invariance T (m + 1) fun i => emb (x i), T.hermiticity (m + 1) x]
  exact (T.weak_locality m x hx).symm

/-! ## Consistency: a nontrivial theory satisfying all the axioms -/

private lemma sum_rev_rev {n : ℕ} (f : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) (Fin.rev j)) = ∑ i, ∑ j, f i j :=
  calc (∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) (Fin.rev j))
      = ∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) j :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp Fin.revPerm fun j => f (Fin.rev i) j
    _ = ∑ i, ∑ j, f i j := Equiv.sum_comp Fin.revPerm fun i => ∑ j, f i j

/-- A concrete, nonzero example of a structure satisfying all the Wightman axioms used
above, showing that the hypotheses of `cpt_theorem` are not vacuous. -/
noncomputable def exampleTheory : WightmanTheory where
  W := fun _ z => ∑ i, ∑ j, cform (z i) (z j)
  bhw_covariance := by
    intro L _ _ hL n z
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hL 1 (z i) (z j)
  hermiticity := by
    intro n x
    have hreal : ∀ a b : Spacetime,
        (starRingEnd ℂ) (cform (emb a) (emb b)) = cform (emb a) (emb b) := by
      intro a b
      simp [cform, emb]
    rw [map_sum]
    simp only [map_sum, hreal]
    exact (sum_rev_rev (fun i j => cform (emb (x i)) (emb (x j)))).symm
  weak_locality := by
    intro m x _
    exact sum_rev_rev (fun i j => cform (emb (x i)) (emb (x j)))

lemma exampleTheory_nontrivial :
    exampleTheory.W 1 (fun _ => emb ![1, 0, 0, 0]) = 1 := by
  simp [exampleTheory, cform, emb]

end Phys

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

