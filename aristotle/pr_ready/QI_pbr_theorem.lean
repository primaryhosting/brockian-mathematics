/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Statement: The quantum state is ontic under preparation independence (Pusey–Barrett–Rudolph).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-! ## The quantum ingredients

We work with two qubits, i.e. with `ℂ⁴` indexed by `Fin 4`, where the index `2*a + b`
stands for the product basis vector `|a⟩ ⊗ |b⟩`.
-/

/-- The inner product on `ℂ⁴` (conjugate-linear in the first argument). -/
noncomputable def ip (u v : Fin 4 → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * v i

/-- `1/√2`, as a complex number. -/
noncomputable def rt : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

@[simp] lemma rt_mul_rt : rt * rt = 1 / 2 := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  rw [rt, ← Complex.ofReal_mul,
    show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = ((Real.sqrt 2) * (Real.sqrt 2))⁻¹ by field_simp, h]
  norm_num

@[simp] lemma conj_rt : (starRingEnd ℂ) rt = rt := Complex.conj_ofReal _

@[simp] lemma conj_two : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl

lemma rt_re : rt.re = (Real.sqrt 2)⁻¹ := rfl

@[simp] lemma rt_re_sq : rt.re ^ 2 = 1 / 2 := by
  rw [rt_re, inv_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_num

@[simp] lemma rt_im : rt.im = 0 := rfl

/-- The four preparations: `phi a b` is `|ψ_a⟩ ⊗ |ψ_b⟩` where `|ψ_0⟩ = |0⟩` and
`|ψ_1⟩ = |+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def phi : Fin 2 → Fin 2 → (Fin 4 → ℂ)
  | 0, 0 => ![1, 0, 0, 0]
  | 0, 1 => ![rt, rt, 0, 0]
  | 1, 0 => ![rt, 0, rt, 0]
  | 1, 1 => ![1/2, 1/2, 1/2, 1/2]

/-- The four vectors of the entangled PBR measurement:
`ξ₀ = (|0⟩|1⟩+|1⟩|0⟩)/√2`, `ξ₁ = (|0⟩|−⟩+|1⟩|+⟩)/√2`,
`ξ₂ = (|+⟩|1⟩+|−⟩|0⟩)/√2`, `ξ₃ = (|+⟩|−⟩+|−⟩|+⟩)/√2`. -/
noncomputable def xi : Fin 4 → (Fin 4 → ℂ)
  | 0 => ![0, rt, rt, 0]
  | 1 => ![1/2, -(1/2), 1/2, 1/2]
  | 2 => ![1/2, 1/2, -(1/2), 1/2]
  | 3 => ![rt, 0, 0, -rt]

/-- The preparation pair excluded by outcome `i`: outcome `i = 2a+b` has probability zero
on the preparation `|ψ_a⟩ ⊗ |ψ_b⟩`. -/
def pa : Fin 4 → Fin 2
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1

def pb : Fin 4 → Fin 2
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1

/-- The PBR measurement is an orthonormal basis of `ℂ⁴`: the vectors are pairwise
orthogonal and of unit norm. -/
theorem xi_orthonormal (i j : Fin 4) :
    ip (xi i) (xi j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [ip, xi, Fin.sum_univ_four] <;> ring

/-- The key quantum fact: outcome `i` of the PBR measurement is orthogonal to the
product preparation `|ψ_{pa i}⟩ ⊗ |ψ_{pb i}⟩`, hence has Born probability zero on it. -/
theorem born_zero (i : Fin 4) : ip (xi i) (phi (pa i) (pb i)) = 0 := by
  fin_cases i <;> simp [ip, xi, phi, pa, pb, Fin.sum_univ_four]

/-! ## Ontological models with preparation independence -/

/-- An ontological model for the two preparations `|0⟩` and `|+⟩` of a qubit, together
with a response function for the PBR measurement on two independently prepared systems.

* `mu a` is the probability distribution over ontic states `Λ` prepared by `|ψ_a⟩`;
* `P l₁ l₂` is the probability distribution over the four measurement outcomes when the
  joint ontic state of the two systems is `(l₁, l₂)`;
* `born` says the model reproduces the quantum predictions, where **preparation
  independence** is encoded in the product measure `mu a l₁ * mu b l₂`. -/
structure OntologicalModel (Λ : Type) [Fintype Λ] where
  mu : Fin 2 → Λ → ℝ
  mu_nonneg : ∀ a l, 0 ≤ mu a l
  mu_sum : ∀ a, ∑ l, mu a l = 1
  P : Λ → Λ → Fin 4 → ℝ
  P_nonneg : ∀ l₁ l₂ i, 0 ≤ P l₁ l₂ i
  P_sum : ∀ l₁ l₂, ∑ i, P l₁ l₂ i = 1
  born : ∀ a b i, ∑ l₁, ∑ l₂, mu a l₁ * mu b l₂ * P l₁ l₂ i =
    Complex.normSq (ip (xi i) (phi a b))

variable {Λ : Type} [Fintype Λ]

/-- If an outcome has average probability zero for a product preparation, then it has
probability zero at every pair of ontic states in the product of the supports. -/
lemma zero_on_support (M : OntologicalModel Λ) (a b : Fin 2) (i : Fin 4)
    (h : Complex.normSq (ip (xi i) (phi a b)) = 0) (l₁ l₂ : Λ)
    (h₁ : 0 < M.mu a l₁) (h₂ : 0 < M.mu b l₂) : M.P l₁ l₂ i = 0 := by
  have hsum := M.born a b i
  rw [h] at hsum
  have hnn : ∀ x ∈ (univ : Finset Λ), 0 ≤ ∑ y, M.mu a x * M.mu b y * M.P x y i := by
    intro x _
    exact sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg a x) (M.mu_nonneg b y)) (M.P_nonneg x y i)
  have h1 : ∑ y, M.mu a l₁ * M.mu b y * M.P l₁ y i = 0 :=
    (sum_eq_zero_iff_of_nonneg hnn).mp hsum l₁ (mem_univ l₁)
  have hnn2 : ∀ y ∈ (univ : Finset Λ), 0 ≤ M.mu a l₁ * M.mu b y * M.P l₁ y i := fun y _ =>
    mul_nonneg (mul_nonneg (M.mu_nonneg a l₁) (M.mu_nonneg b y)) (M.P_nonneg l₁ y i)
  have h2 : M.mu a l₁ * M.mu b l₂ * M.P l₁ l₂ i = 0 :=
    (sum_eq_zero_iff_of_nonneg hnn2).mp h1 l₂ (mem_univ l₂)
  have := mul_pos h₁ h₂
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' (ne_of_gt this)
  · exact h'

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model that reproduces the
quantum predictions for the PBR measurement on two independently prepared systems
(preparation independence), the distributions over ontic states associated with the two
distinct pure states `|0⟩` and `|+⟩` have disjoint supports: no ontic state is compatible
with both preparations.  In other words, the quantum state is *ontic*, not merely
epistemic. -/
theorem pbr_theorem (M : OntologicalModel Λ) (l : Λ) :
    ¬ (0 < M.mu 0 l ∧ 0 < M.mu 1 l) := by
  rintro ⟨h0, h1⟩
  have hall : ∀ a : Fin 2, 0 < M.mu a l := by
    intro a; fin_cases a
    · exact h0
    · exact h1
  have key : ∀ i : Fin 4, M.P l l i = 0 := by
    intro i
    have hz : Complex.normSq (ip (xi i) (phi (pa i) (pb i))) = 0 := by
      rw [born_zero i]; simp
    exact zero_on_support M (pa i) (pb i) i hz l l (hall _) (hall _)
  have := M.P_sum l l
  rw [show ∑ i, M.P l l i = 0 from sum_eq_zero fun i _ => key i] at this
  norm_num at this

/-- The Born probabilities of the PBR measurement sum to one on every product
preparation (the measurement is a complete measurement). -/
theorem born_sum (a b : Fin 2) : ∑ i, Complex.normSq (ip (xi i) (phi a b)) = 1 := by
  fin_cases a <;> fin_cases b <;>
    simp [ip, xi, phi, Fin.sum_univ_four, Complex.normSq_apply] <;> nlinarith [rt_re_sq]

/-- The hypotheses of `OntologicalModel` are consistent: the ψ-ontic model in which the
ontic state simply records which of the two quantum states was prepared, and whose
response function is given by the Born rule, is such a model.  Hence `pbr_theorem` is
not vacuous. -/
noncomputable def psiOnticModel : OntologicalModel (Fin 2) where
  mu := fun a l => if l = a then 1 else 0
  mu_nonneg := by intro a l; split <;> norm_num
  mu_sum := by intro a; fin_cases a <;> simp
  P := fun l₁ l₂ i => Complex.normSq (ip (xi i) (phi l₁ l₂))
  P_nonneg := fun _ _ _ => Complex.normSq_nonneg _
  P_sum := fun l₁ l₂ => born_sum l₁ l₂
  born := by intro a b i; fin_cases a <;> fin_cases b <;> simp

/-- Reformulation: the supports of the two ontic distributions are disjoint sets. -/
theorem pbr_supports_disjoint (M : OntologicalModel Λ) :
    Disjoint {l : Λ | 0 < M.mu 0 l} {l : Λ | 0 < M.mu 1 l} := by
  rw [Set.disjoint_left]
  intro l hl hl'
  exact pbr_theorem M l ⟨hl, hl'⟩

end QI

