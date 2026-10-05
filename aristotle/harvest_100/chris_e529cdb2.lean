/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical information quantities -/

section ClassicalDefs

variable {X I Y : Type*}

/-- Shannon entropy `H(P) = -∑ P x * log (P x)` of a finite probability vector. -/
noncomputable def shannonEntropy [Fintype X] (P : X → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (P x)

/-- Kullback–Leibler divergence `D(a‖b) = ∑ a x * log (a x / b x)`. -/
noncomputable def klDiv [Fintype X] (a b : X → ℝ) : ℝ :=
  ∑ x, a x * Real.log (a x / b x)

/-- Mutual information of a joint probability distribution `J` on `I × Y`. -/
noncomputable def mutualInfo [Fintype I] [Fintype Y] (J : I → Y → ℝ) : ℝ :=
  ∑ i, ∑ y, J i y * Real.log (J i y / ((∑ y', J i y') * (∑ i', J i' y)))

end ClassicalDefs

/-! ## The log-sum inequality and the classical data-processing inequality -/

section ClassicalCore

variable {X I Y : Type*} [Fintype X] [Fintype I] [Fintype Y]

/-- The log-sum inequality. -/
theorem log_sum_inequality (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hab : ∀ x, b x = 0 → a x = 0) :
    (∑ x, a x) * Real.log ((∑ x, a x) / (∑ x, b x)) ≤ ∑ x, a x * Real.log (a x / b x) := by
  set A := ∑ x, a x with hA
  set B := ∑ x, b x with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => ha x
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hz : ∀ x, a x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => ha x)).mp hA0'.symm x (Finset.mem_univ x)
    simp [← hA0', hz]
  · have hBpos : 0 < B := by
      obtain ⟨x0, -, hx0⟩ : ∃ x0 ∈ Finset.univ, 0 < a x0 := by
        by_contra h
        push_neg at h
        have : A ≤ 0 := by rw [hA]; exact Finset.sum_nonpos fun x hx => h x hx
        linarith
      have hb0 : 0 < b x0 := by
        rcases eq_or_lt_of_le (hb x0) with h | h
        · exact absurd (hab x0 h.symm) (by linarith)
        · exact h
      exact lt_of_lt_of_le hb0 (Finset.single_le_sum (fun x _ => hb x) (Finset.mem_univ x0))
    have key : ∀ x, a x * Real.log (A / B) + (a x - b x * (A / B)) ≤ a x * Real.log (a x / b x) := by
      intro x
      rcases eq_or_lt_of_le (ha x) with hax | hax
      · have hb' : 0 ≤ b x * (A / B) := mul_nonneg (hb x) (by positivity)
        simp [← hax]
        linarith
      · have hbx : 0 < b x := by
          rcases eq_or_lt_of_le (hb x) with h | h
          · exact absurd (hab x h.symm) (by linarith)
          · exact h
        have h1 := Real.log_le_sub_one_of_pos (x := (b x * A) / (a x * B)) (by positivity)
        have hinv : Real.log ((b x * A) / (a x * B)) = -Real.log ((a x * B) / (b x * A)) := by
          rw [← Real.log_inv]
          congr 1
          field_simp
        rw [hinv] at h1
        have hsplit : Real.log ((a x * B) / (b x * A)) = Real.log (a x / b x) - Real.log (A / B) := by
          rw [Real.log_div (by positivity) (by positivity),
            Real.log_div (by positivity) (by positivity),
            Real.log_div (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
          ring
        rw [hsplit] at h1
        have h2 : a x * (1 - (b x * A) / (a x * B))
            ≤ a x * (Real.log (a x / b x) - Real.log (A / B)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hax)
          linarith
        have h3 : a x * (1 - (b x * A) / (a x * B)) = a x - b x * (A / B) := by field_simp
        linarith
    calc A * Real.log (A / B) = ∑ x, (a x * Real.log (A / B) + (a x - b x * (A / B))) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
            ← hA, ← hB]
          have hBB : B * (A / B) = A := by field_simp
          rw [hBB]; ring
      _ ≤ ∑ x, a x * Real.log (a x / b x) := Finset.sum_le_sum fun x _ => key x

/-- Data-processing inequality for the KL divergence under a stochastic channel `M`. -/
theorem klDiv_channel_le (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hab : ∀ x, b x = 0 → a x = 0) (M : X → Y → ℝ) (hM : ∀ x y, 0 ≤ M x y)
    (hM1 : ∀ x, ∑ y, M x y = 1) :
    klDiv (fun y => ∑ x, a x * M x y) (fun y => ∑ x, b x * M x y) ≤ klDiv a b := by
  have step1 : klDiv (fun y => ∑ x, a x * M x y) (fun y => ∑ x, b x * M x y)
      ≤ ∑ y, ∑ x, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y)) := by
    apply Finset.sum_le_sum
    intro y _
    exact log_sum_inequality (fun x => a x * M x y) (fun x => b x * M x y)
      (fun x => mul_nonneg (ha x) (hM x y)) (fun x => mul_nonneg (hb x) (hM x y))
      (fun x hx => by
        simp only at hx ⊢
        rcases mul_eq_zero.mp hx with h | h
        · rw [hab x h]; ring
        · rw [h]; ring)
  have step2 : ∀ x, ∑ y, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y))
      = a x * Real.log (a x / b x) := by
    intro x
    have hterm : ∀ y ∈ Finset.univ, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y))
        = (M x y) * (a x * Real.log (a x / b x)) := by
      intro y _
      rcases eq_or_lt_of_le (hM x y) with h | h
      · simp [← h]
      · rw [mul_div_mul_right _ _ (ne_of_gt h)]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hM1 x, one_mul]
  rw [Finset.sum_comm] at step1
  simp only [step2] at step1
  exact step1

theorem shannonEntropy_eq_neg (P : X → ℝ) :
    shannonEntropy P = -∑ x, P x * Real.log (P x) := by
  simp [shannonEntropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- The Holevo χ quantity of a classical ensemble, written as an average KL divergence. -/
theorem sum_klDiv_eq_entropy_sub (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (P : I → X → ℝ) (hP : ∀ i x, 0 ≤ P i x) :
    ∑ i, p i * klDiv (P i) (fun x => ∑ j, p j * P j x)
      = shannonEntropy (fun x => ∑ j, p j * P j x) - ∑ i, p i * shannonEntropy (P i) := by
  set Pb : X → ℝ := fun x => ∑ j, p j * P j x with hPb
  have key : ∀ i, p i * klDiv (P i) Pb
      = p i * (∑ x, P i x * Real.log (P i x)) - ∑ x, p i * P i x * Real.log (Pb x) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · simp [← h0]
    · have hk : klDiv (P i) Pb = ∑ x, (P i x * Real.log (P i x) - P i x * Real.log (Pb x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases eq_or_lt_of_le (hP i x) with hx | hx
        · simp [← hx]
        · have hbx : 0 < Pb x := by
            have : p i * P i x ≤ Pb x :=
              Finset.single_le_sum (f := fun j => p j * P j x)
                (fun j _ => mul_nonneg (hp j) (hP j x)) (Finset.mem_univ i)
            nlinarith
          rw [Real.log_div (ne_of_gt hx) (ne_of_gt hbx)]
          ring
      rw [hk, Finset.sum_sub_distrib, mul_sub]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib]
  have h1 : ∑ i, ∑ x, p i * P i x * Real.log (Pb x) = ∑ x, Pb x * Real.log (Pb x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_mul]
  have h2 : ∀ i, p i * (∑ x, P i x * Real.log (P i x)) = -(p i * shannonEntropy (P i)) := by
    intro i
    rw [shannonEntropy_eq_neg]
    ring
  rw [h1, shannonEntropy_eq_neg Pb, Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_neg_distrib]
  ring

/-- Mutual information of a joint distribution `J i y = p i * Q i y` as an average KL divergence. -/
theorem mutualInfo_eq_sum_klDiv (p : I → ℝ) (Q : I → Y → ℝ) (hQ1 : ∀ i, ∑ y, Q i y = 1) :
    mutualInfo (fun i y => p i * Q i y)
      = ∑ i, p i * klDiv (Q i) (fun y => ∑ j, p j * Q j y) := by
  unfold mutualInfo klDiv
  apply Finset.sum_congr rfl
  intro i _
  have hrow : ∑ y', p i * Q i y' = p i := by rw [← Finset.mul_sum, hQ1 i, mul_one]
  simp only [hrow]
  rcases eq_or_ne (p i) 0 with h0 | h0
  · simp [h0]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [mul_div_mul_left _ _ h0]
    ring

/-- The Holevo bound for a classical ensemble measured through a stochastic channel:
the mutual information between the label and the outcome is at most the χ quantity. -/
theorem classical_holevo_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (P : I → X → ℝ) (hP : ∀ i x, 0 ≤ P i x) (hP1 : ∀ i, ∑ x, P i x = 1)
    (M : X → Y → ℝ) (hM : ∀ x y, 0 ≤ M x y) (hM1 : ∀ x, ∑ y, M x y = 1) :
    mutualInfo (fun i y => p i * ∑ x, P i x * M x y)
      ≤ shannonEntropy (fun x => ∑ j, p j * P j x) - ∑ i, p i * shannonEntropy (P i) := by
  set Pb : X → ℝ := fun x => ∑ j, p j * P j x with hPbdef
  have hPb0 : ∀ x, 0 ≤ Pb x := fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hP j x)
  set Q : I → Y → ℝ := fun i y => ∑ x, P i x * M x y with hQdef
  have hQ1 : ∀ i, ∑ y, Q i y = 1 := by
    intro i
    rw [hQdef, Finset.sum_comm]
    simp only [← Finset.mul_sum, hM1]
    simpa using hP1 i
  have hQb : (fun y => ∑ j, p j * Q j y) = (fun y => ∑ x, Pb x * M x y) := by
    funext y
    rw [hPbdef]
    simp only [hQdef, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring
  rw [mutualInfo_eq_sum_klDiv p Q hQ1, ← sum_klDiv_eq_entropy_sub p hp P hP]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (hp i) with h0 | hpos
  · simp [← h0]
  · apply mul_le_mul_of_nonneg_left _ (hp i)
    rw [hQb]
    exact klDiv_channel_le (P i) Pb (hP i) hPb0
      (fun x hx => by
        by_contra hne
        have hlt : 0 < P i x := lt_of_le_of_ne (hP i x) (Ne.symm hne)
        have : p i * P i x ≤ Pb x :=
          Finset.single_le_sum (f := fun j => p j * P j x)
            (fun j _ => mul_nonneg (hp j) (hP j x)) (Finset.mem_univ i)
        nlinarith)
      M hM hM1

end ClassicalCore

/-! ## Quantum definitions -/

section QuantumDefs

variable {X I Y : Type*}

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity [Fintype X] (ρ : Matrix X X ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- A POVM: a family of positive semidefinite matrices summing to the identity. -/
def IsPOVM [Fintype X] [DecidableEq X] [Fintype Y] (E : Y → Matrix X X ℂ) : Prop :=
  (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1

/-- The von Neumann entropy `S(ρ) = -∑ λ log λ` of a Hermitian matrix, in terms of its
eigenvalues (defined to be `0` on non-Hermitian matrices). -/
noncomputable def vonNeumannEntropy [Fintype X] [DecidableEq X] (ρ : Matrix X X ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ x, Real.negMulLog (h.eigenvalues x) else 0

/-- The Holevo χ quantity `χ = S(∑ pᵢ ρᵢ) - ∑ pᵢ S(ρᵢ)` of an ensemble. -/
noncomputable def holevoChi [Fintype X] [DecidableEq X] [Fintype I]
    (p : I → ℝ) (ρ : I → Matrix X X ℂ) : ℝ :=
  vonNeumannEntropy (∑ i, (p i : ℂ) • ρ i) - ∑ i, p i * vonNeumannEntropy (ρ i)

/-- The joint distribution of the ensemble label and the outcome of the POVM `E`,
`J i y = pᵢ Tr(ρᵢ Eᵧ)`. -/
noncomputable def measuredJoint [Fintype X] (p : I → ℝ) (ρ : I → Matrix X X ℂ)
    (E : Y → Matrix X X ℂ) : I → Y → ℝ :=
  fun i y => p i * (Matrix.trace (ρ i * E y)).re

/-- The accessible information of an ensemble: the supremum, over all POVMs with finitely
many outcomes, of the mutual information between the label and the measurement outcome. -/
noncomputable def accessibleInfo [Fintype X] [DecidableEq X] [Fintype I]
    (p : I → ℝ) (ρ : I → Matrix X X ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (n : ℕ) (E : Fin n → Matrix X X ℂ), IsPOVM E ∧
    r = mutualInfo (measuredJoint p ρ E)}

end QuantumDefs

/-! ## From matrices to classical data -/

section Bridge

variable {X I Y : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype Y]

/-- Any symmetric function of the eigenvalues of a real diagonal matrix can be computed from
the diagonal entries. -/
theorem sum_eigenvalues_diagonal (f : ℝ → ℝ) (d : X → ℝ)
    (h : (Matrix.diagonal (fun x => (d x : ℂ))).IsHermitian) :
    ∑ x, f (h.eigenvalues x) = ∑ x, f (d x) := by
  have hcomp : (fun i : X => Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ))
      = (fun a : ℂ => Polynomial.X - Polynomial.C a) ∘ (fun x : X => ((d x : ℝ) : ℂ)) := rfl
  have hroots : (Matrix.diagonal (fun x => (d x : ℂ))).charpoly.roots
      = Multiset.map (fun x => ((d x : ℝ) : ℂ)) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, hcomp, ← Multiset.map_map]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [h.roots_charpoly_eq_eigenvalues] at hroots
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map] at hre
  have hre2 : Multiset.map h.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    simpa [Function.comp_def] using hre
  have e1 : ∑ x, f (h.eigenvalues x)
      = (Multiset.map f (Multiset.map h.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have e2 : ∑ x, f (d x) = (Multiset.map f (Multiset.map d Finset.univ.val)).sum := by
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e1, e2, hre2]

omit [Fintype X] in
theorem isHermitian_diagonal_real (d : X → ℝ) :
    (Matrix.diagonal (fun x => (d x : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  simp

theorem vonNeumannEntropy_diagonal (d : X → ℝ) :
    vonNeumannEntropy (Matrix.diagonal (fun x => (d x : ℂ))) = shannonEntropy d := by
  rw [vonNeumannEntropy, dif_pos (isHermitian_diagonal_real d)]
  exact sum_eigenvalues_diagonal Real.negMulLog d _

/-- Diagonal entries of a positive semidefinite matrix are nonnegative reals. -/
theorem posSemidef_diag_re_nonneg {A : Matrix X X ℂ} (hA : A.PosSemidef) (x : X) :
    0 ≤ (A x x).re := by
  simpa using hA.re_dotProduct_nonneg (Pi.single x 1)

end Bridge

/-! ## The Holevo bound -/

section Main

variable {X I Y : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype Y]

/-- **Holevo bound**, fixed POVM version, for an ensemble of commuting (simultaneously
diagonal) states: the mutual information between the ensemble label and the outcome of any
POVM measurement is at most the Holevo χ quantity of the ensemble. -/
theorem holevo_bound_povm (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (d : I → X → ℝ) (hd : ∀ i, IsDensity (Matrix.diagonal (fun x => (d i x : ℂ))))
    (E : Y → Matrix X X ℂ) (hE : IsPOVM E) :
    mutualInfo (measuredJoint p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) E)
      ≤ holevoChi p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) := by
  set M : X → Y → ℝ := fun x y => ((E y) x x).re with hMdef
  have hd0 : ∀ i x, 0 ≤ d i x := by
    intro i x
    have := posSemidef_diag_re_nonneg (hd i).1 x
    simpa [Matrix.diagonal_apply_eq] using this
  have hd1 : ∀ i, ∑ x, d i x = 1 := by
    intro i
    have h := (hd i).2
    rw [Matrix.trace_diagonal] at h
    have := congrArg Complex.re h
    simpa [Complex.re_sum] using this
  have hM0 : ∀ x y, 0 ≤ M x y := fun x y => posSemidef_diag_re_nonneg (hE.1 y) x
  have hM1 : ∀ x, ∑ y, M x y = 1 := by
    intro x
    have h := congrArg (fun A : Matrix X X ℂ => A x x) hE.2
    simp only [Matrix.sum_apply, Matrix.one_apply_eq] at h
    have := congrArg Complex.re h
    simpa [Complex.re_sum, hMdef] using this
  have hjoint : measuredJoint p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) E
      = fun i y => p i * ∑ x, d i x * M x y := by
    funext i y
    rw [measuredJoint]
    congr 1
    rw [Matrix.trace]
    simp [Matrix.diagonal_mul, Complex.re_sum, hMdef]
  have hchi : holevoChi p (fun i => Matrix.diagonal (fun x => (d i x : ℂ)))
      = shannonEntropy (fun x => ∑ j, p j * d j x) - ∑ i, p i * shannonEntropy (d i) := by
    rw [holevoChi]
    congr 1
    · have hsum : ∑ i, (p i : ℂ) • Matrix.diagonal (fun x => (d i x : ℂ))
          = Matrix.diagonal (fun x => ((∑ i, p i * d i x : ℝ) : ℂ)) := by
        ext x y
        rw [Matrix.sum_apply]
        by_cases h : x = y
        · subst h
          simp [Matrix.diagonal_apply_eq, Complex.ofReal_sum]
        · simp [Matrix.diagonal_apply_ne _ h]
      rw [hsum, vonNeumannEntropy_diagonal]
    · exact Finset.sum_congr rfl fun i _ => by rw [vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  exact classical_holevo_bound p hp d hd0 hd1 M hM0 hM1

/-- **Holevo bound**: the accessible information of an ensemble of commuting states is at most
its Holevo χ quantity. -/
theorem holevo_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (d : I → X → ℝ) (hd : ∀ i, IsDensity (Matrix.diagonal (fun x => (d i x : ℂ)))) :
    accessibleInfo p (fun i => Matrix.diagonal (fun x => (d i x : ℂ)))
      ≤ holevoChi p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) := by
  apply csSup_le
  · refine ⟨_, 1, (fun _ => (1 : Matrix X X ℂ)), ⟨fun _ => Matrix.PosSemidef.one, by simp⟩, rfl⟩
  · rintro r ⟨n, E, hE, rfl⟩
    exact holevo_bound_povm p hp d hd E hE

end Main

end QI

