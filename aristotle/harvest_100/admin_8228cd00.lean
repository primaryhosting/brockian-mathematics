import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/--
**Pusey–Barrett–Rudolph theorem** (the quantum state is ontic).

Setting: an ontological (hidden-variable) model with a finite space `Λ` of ontic states.
Two distinct quantum preparations, indexed by `Bool`, are represented by probability
distributions `mu false, mu true : Λ → ℝ` over `Λ` (`hmu_nonneg`, `hmu_sum`).

*Preparation independence*: when two systems are prepared independently, with
preparations `o.1` and `o.2`, the joint distribution of their ontic states is the
product `mu o.1 l₁ * mu o.2 l₂`.

The two systems are subjected to a joint measurement whose outcomes are indexed by
`Bool × Bool`; `p l₁ l₂ o` is the probability of outcome `o` given the ontic state
`(l₁, l₂)` (`hp_nonneg`, `hp_sum`).

*Antidistinguishability* (the quantum prediction realized by the PBR entangled
measurement): outcome `o` never occurs on the product preparation `o` (`hanti`).

Conclusion: the two preparations have disjoint (and nonempty) supports, i.e. no
ontic state is compatible with both quantum states — the quantum state is ontic,
not merely epistemic.
-/
theorem pbr_theorem {Λ : Type*} [Fintype Λ]
    (mu : Bool → Λ → ℝ)
    (hmu_nonneg : ∀ i l, 0 ≤ mu i l)
    (hmu_sum : ∀ i, ∑ l, mu i l = 1)
    (p : Λ → Λ → Bool × Bool → ℝ)
    (hp_nonneg : ∀ l₁ l₂ o, 0 ≤ p l₁ l₂ o)
    (hp_sum : ∀ l₁ l₂, ∑ o : Bool × Bool, p l₁ l₂ o = 1)
    (hanti : ∀ o : Bool × Bool,
      ∑ l₁, ∑ l₂, mu o.1 l₁ * mu o.2 l₂ * p l₁ l₂ o = 0) :
    (∀ l, mu false l = 0 ∨ mu true l = 0) ∧
      (∃ l, 0 < mu false l) ∧ (∃ l, 0 < mu true l) := by
  have nonempty_support : ∀ i, ∃ l, 0 < mu i l := by
    intro i
    by_contra hcon
    push_neg at hcon
    have : ∑ l, mu i l = 0 :=
      Finset.sum_eq_zero fun l _ => le_antisymm (hcon l) (hmu_nonneg i l)
    rw [hmu_sum i] at this
    norm_num at this
  refine ⟨?_, nonempty_support false, nonempty_support true⟩
  intro l
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  have h0' : 0 < mu false l := lt_of_le_of_ne (hmu_nonneg false l) (Ne.symm h0)
  have h1' : 0 < mu true l := lt_of_le_of_ne (hmu_nonneg true l) (Ne.symm h1)
  -- Each outcome `o` has zero response at the common ontic state `(l, l)`.
  have key : ∀ o : Bool × Bool, p l l o = 0 := by
    intro o
    have hpos : 0 < mu o.1 l * mu o.2 l := by
      cases o.1 <;> cases o.2 <;> positivity
    have hterm : mu o.1 l * mu o.2 l * p l l o = 0 := by
      have hnn : ∀ l₁ ∈ (Finset.univ : Finset Λ), 0 ≤ ∑ l₂, mu o.1 l₁ * mu o.2 l₂ * p l₁ l₂ o := by
        intro l₁ _
        exact Finset.sum_nonneg fun l₂ _ =>
          mul_nonneg (mul_nonneg (hmu_nonneg _ _) (hmu_nonneg _ _)) (hp_nonneg _ _ _)
      have hinner : ∑ l₂, mu o.1 l * mu o.2 l₂ * p l l₂ o = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (hanti o) l (Finset.mem_univ l)
      have hnn2 : ∀ l₂ ∈ (Finset.univ : Finset Λ), 0 ≤ mu o.1 l * mu o.2 l₂ * p l l₂ o :=
        fun l₂ _ => mul_nonneg (mul_nonneg (hmu_nonneg _ _) (hmu_nonneg _ _)) (hp_nonneg _ _ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp hinner l (Finset.mem_univ l)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have : (1 : ℝ) = 0 := by
    rw [← hp_sum l l]
    exact Finset.sum_eq_zero fun o _ => key o
  norm_num at this

/--
The hypotheses of `QI.pbr_theorem` are consistent: an ontological model with
disjoint supports, preparation independence and an antidistinguishing measurement
does exist (here `Λ = Bool`, with the two preparations being the two point masses).
-/
theorem pbr_hypotheses_satisfiable :
    ∃ (mu : Bool → Bool → ℝ) (p : Bool → Bool → Bool × Bool → ℝ),
      (∀ i l, 0 ≤ mu i l) ∧ (∀ i, ∑ l, mu i l = 1) ∧
      (∀ l₁ l₂ o, 0 ≤ p l₁ l₂ o) ∧ (∀ l₁ l₂, ∑ o : Bool × Bool, p l₁ l₂ o = 1) ∧
      (∀ o : Bool × Bool, ∑ l₁, ∑ l₂, mu o.1 l₁ * mu o.2 l₂ * p l₁ l₂ o = 0) := by
  refine ⟨fun i l => if i = l then 1 else 0,
          fun l₁ l₂ o => if o = (l₁, l₂) then 0 else 1 / 3, ?_, ?_, ?_, ?_, ?_⟩
  · intro i l; dsimp only; split <;> norm_num
  · intro i; cases i <;> simp
  · intro l₁ l₂ o; dsimp only; split <;> norm_num
  · intro l₁ l₂
    cases l₁ <;> cases l₂ <;>
      simp [Fintype.sum_prod_type, Prod.ext_iff] <;> norm_num
  · rintro ⟨a, b⟩
    cases a <;> cases b <;>
      simp [Prod.ext_iff]

/-! ### The quantum ingredient: the PBR antidistinguishing measurement

We work with two qubits, the four-dimensional state space being modelled as
`Bool × Bool → ℂ` (the coordinate indexed by `(a, b)` is the amplitude of the
computational basis vector `|a⟩|b⟩`, with `false ↦ |0⟩`, `true ↦ |1⟩`).
-/

/-- The complex number `√2`. -/
noncomputable def sq2 : ℂ := (Real.sqrt 2 : ℝ)

/-- The qubit state `|0⟩`. -/
noncomputable def ket0 : Bool → ℂ := fun b => if b then 0 else 1

/-- The qubit state `|1⟩`. -/
noncomputable def ket1 : Bool → ℂ := fun b => if b then 1 else 0

/-- The qubit state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def ketp : Bool → ℂ := fun _ => 1 / sq2

/-- The qubit state `|-⟩ = (|0⟩ - |1⟩)/√2`. -/
noncomputable def ketm : Bool → ℂ := fun b => if b then -(1 / sq2) else 1 / sq2

/-- The tensor product of two qubit states. -/
noncomputable def tens (u v : Bool → ℂ) : Bool × Bool → ℂ := fun q => u q.1 * v q.2

/-- The inner product on the two-qubit space (conjugate-linear in the first slot). -/
noncomputable def inn (u v : Bool × Bool → ℂ) : ℂ :=
  ∑ q : Bool × Bool, (starRingEnd ℂ) (u q) * v q

/-- The four PBR product preparations: `psiPBR (i, j) = |ψ_i⟩ ⊗ |ψ_j⟩`, where
`ψ_false = |0⟩` and `ψ_true = |+⟩`. -/
noncomputable def psiPBR (o : Bool × Bool) : Bool × Bool → ℂ :=
  tens (if o.1 then ketp else ket0) (if o.2 then ketp else ket0)

/-- The four vectors of the entangled PBR measurement basis. -/
noncomputable def xiPBR : Bool × Bool → (Bool × Bool → ℂ)
  | (false, false) => fun q => (tens ket0 ket1 q + tens ket1 ket0 q) / sq2
  | (false, true)  => fun q => (tens ket0 ketm q + tens ket1 ketp q) / sq2
  | (true, false)  => fun q => (tens ketp ket1 q + tens ketm ket0 q) / sq2
  | (true, true)   => fun q => (tens ketp ketm q + tens ketm ketp q) / sq2

/-- The PBR measurement vectors form an orthonormal basis of the two-qubit space,
so `{|ξ_o⟩⟨ξ_o|}` is a legitimate projective measurement. -/
theorem xiPBR_orthonormal (o o' : Bool × Bool) :
    inn (xiPBR o) (xiPBR o') = if o = o' then 1 else 0 := by
  obtain ⟨a, b⟩ := o
  obtain ⟨c, d⟩ := o'
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [inn, xiPBR, tens, ket0, ket1, ketp, ketm, Fintype.sum_prod_type,
      map_div₀, Complex.conj_ofReal, sq2] <;>
    field_simp <;> ring_nf <;> norm_cast <;>
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      pow_mul (Real.sqrt 2) 2 3, pow_mul (Real.sqrt 2) 2 2]

/-- **Antidistinguishability**: the `o`-th outcome of the PBR measurement has zero
Born probability on the `o`-th product preparation. -/
theorem xiPBR_orth_psiPBR (o : Bool × Bool) : inn (xiPBR o) (psiPBR o) = 0 := by
  obtain ⟨a, b⟩ := o
  cases a <;> cases b <;>
    simp [inn, xiPBR, psiPBR, tens, ket0, ket1, ketp, ketm, Fintype.sum_prod_type,
      map_div₀] <;>
    field_simp <;> ring

/--
**PBR theorem, quantum form.** Suppose an ontological model with a finite ontic
state space `Λ` underlies the two qubit preparations `|0⟩` (index `false`) and
`|+⟩` (index `true`), satisfies preparation independence, and reproduces the Born
rule probabilities of the entangled PBR measurement `{|ξ_o⟩⟨ξ_o|}` on the four
product preparations (`hborn`). Then the two preparations have disjoint nonempty
supports: the quantum state is ontic.
-/
theorem pbr_theorem_quantum {Λ : Type*} [Fintype Λ]
    (mu : Bool → Λ → ℝ)
    (hmu_nonneg : ∀ i l, 0 ≤ mu i l)
    (hmu_sum : ∀ i, ∑ l, mu i l = 1)
    (p : Λ → Λ → Bool × Bool → ℝ)
    (hp_nonneg : ∀ l₁ l₂ o, 0 ≤ p l₁ l₂ o)
    (hp_sum : ∀ l₁ l₂, ∑ o : Bool × Bool, p l₁ l₂ o = 1)
    (hborn : ∀ o : Bool × Bool,
      ∑ l₁, ∑ l₂, mu o.1 l₁ * mu o.2 l₂ * p l₁ l₂ o
        = Complex.normSq (inn (xiPBR o) (psiPBR o))) :
    (∀ l, mu false l = 0 ∨ mu true l = 0) ∧
      (∃ l, 0 < mu false l) ∧ (∃ l, 0 < mu true l) := by
  refine pbr_theorem mu hmu_nonneg hmu_sum p hp_nonneg hp_sum ?_
  intro o
  rw [hborn o, xiPBR_orth_psiPBR o, map_zero]

end QI

