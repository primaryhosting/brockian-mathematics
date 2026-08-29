import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The header comment above must be the first thing in the file; Lean requires
`import` lines to precede all commands, so the single `import Mathlib` line comes first.)

We compute the spectrum of the adjacency matrix of the cycle graph `C₁₇`
(the Hückel matrix of a 17-membered annulene, in units where α = 0 and β = 1):
the eigenvalues are exactly `2 cos (2πk/17)` for `k = 0, …, 16`.

The vertex set `Fin 17` is identified with the ring `ZMod 17`, and the proof uses the
standard additive character `ψ a = exp (2πi a / 17)` and discrete Fourier analysis.
-/

open Complex Matrix Finset

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₇`, i.e. the Hückel matrix of a
17-membered annulene with `α = 0`, `β = 1`. The index type `ZMod 17` is definitionally
the vertex type `Fin 17` of `SimpleGraph.cycleGraph 17`. -/
noncomputable def C17adj : Matrix (ZMod 17) (ZMod 17) ℂ :=
  SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 17)

/-- The standard additive character `a ↦ exp (2πi a / 17)` on `ZMod 17`. -/
noncomputable abbrev psi : AddChar (ZMod 17) ℂ := ZMod.stdAddChar

/-! ### Basic properties of the character `psi` -/

lemma psi_apply (a : ZMod 17) :
    psi a = Complex.exp (2 * Real.pi * Complex.I * a.val / 17) := by
  rw [psi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]; norm_num

lemma psi_ne_zero (a : ZMod 17) : psi a ≠ 0 := by
  rw [psi_apply]; exact Complex.exp_ne_zero _

lemma psi_mul_neg (a : ZMod 17) : psi a * psi (-a) = 1 := by
  rw [← AddChar.map_add_eq_mul]; simp

lemma psi_neg (a : ZMod 17) : psi (-a) = (psi a)⁻¹ := by
  have h := psi_mul_neg a
  have h0 := psi_ne_zero a
  field_simp
  linear_combination h

/-- The eigenvalue attached to the character index `a` is `2 cos (2π a / 17)`. -/
lemma psi_add_psi_neg (a : ZMod 17) :
    psi a + psi (-a) = 2 * Real.cos (2 * Real.pi * a.val / 17) := by
  rw [psi_neg, psi_apply, ← Complex.exp_neg]
  have hrw : ((2 : ℂ) * Real.pi * Complex.I * a.val / 17)
      = ((2 * Real.pi * a.val / 17 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Orthogonality of characters: the character sum vanishes unless `d = 0`. -/
lemma psi_orthogonality (d : ZMod 17) :
    ∑ k : ZMod 17, psi (k * d) = if d = 0 then 17 else 0 := by
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd]
    have h1 : psi.mulShift d ≠ 1 := ZMod.isPrimitive_stdAddChar 17 hd
    simpa [AddChar.mulShift_apply, mul_comm] using AddChar.sum_eq_zero_of_ne_one h1

/-! ### The adjacency matrix acts as the sum of the two neighbour shifts -/

lemma cycle17_adj (i j : ZMod 17) :
    (SimpleGraph.cycleGraph 17).Adj i j ↔ (i - j = 1 ∨ j - i = 1) :=
  SimpleGraph.cycleGraph_adj (n := 15)

lemma C17adj_apply (i j : ZMod 17) :
    C17adj i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  rw [C17adj, SimpleGraph.adjMatrix_apply]
  congr 1
  simp only [eq_iff_iff, cycle17_adj]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination h)
  · rintro (h | h)
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination h)

lemma adj_mulVec (v : ZMod 17 → ℂ) (i : ZMod 17) :
    (C17adj *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    revert h2; decide
  rw [Matrix.mulVec, dotProduct]
  have hterm : ∀ j : ZMod 17, C17adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    rw [C17adj_apply]
    by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  simp

/-! ### Discrete Fourier analysis on `ZMod 17` -/

/-- The `k`-th Fourier coefficient of `v`. -/
noncomputable def fourierCoeff (v : ZMod 17 → ℂ) (k : ZMod 17) : ℂ :=
  ∑ j : ZMod 17, v j * psi (-(k * j))

lemma sum_shift (v : ZMod 17 → ℂ) (k d : ZMod 17) :
    ∑ j : ZMod 17, v (j + d) * psi (-(k * j)) = psi (k * d) * fourierCoeff v k := by
  rw [fourierCoeff, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight d) _ _ (fun x => ?_)
  have h1 : (-(k * (x + d))) = (-(k * x)) + (-(k * d)) := by ring
  simp only [Equiv.coe_addRight, h1, AddChar.map_add_eq_mul]
  linear_combination (-(v (x + d) * psi (-(k * x)))) * (psi_mul_neg (k * d))

/-- Fourier inversion on `ZMod 17`. -/
lemma fourier_inversion (v : ZMod 17 → ℂ) (j : ZMod 17) :
    ∑ k : ZMod 17, fourierCoeff v k * psi (k * j) = 17 * v j := by
  have step : ∀ k : ZMod 17, fourierCoeff v k * psi (k * j)
      = ∑ j' : ZMod 17, v j' * psi (k * (j - j')) := by
    intro k
    rw [fourierCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    have hk : k * (j - j') = (-(k * j')) + k * j := by ring
    rw [hk, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
  have step2 : ∀ j' : ZMod 17, ∑ k : ZMod 17, v j' * psi (k * (j - j'))
      = if j' = j then 17 * v j else 0 := by
    intro j'
    rw [← Finset.mul_sum, psi_orthogonality]
    by_cases h : j' = j
    · subst h; simp; ring
    · rw [if_neg (fun hz => h (by linear_combination -hz)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun j' _ => step2 j')]
  simp

/-! ### The main theorem -/

/-- **Hückel theory for the 17-annulene.** A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₇` if and only if `μ = 2 cos (2πk/17)`
for some `k ∈ {0, …, 16}`. -/
theorem huckel_C17 (μ : ℂ) :
    (∃ v : ZMod 17 → ℂ, v ≠ 0 ∧ C17adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 17, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    by_contra hc
    push_neg at hc
    have hne : ∀ a : ZMod 17, μ ≠ psi a + psi (-a) := by
      intro a h
      exact hc ⟨a.val, a.val_lt⟩ (by rw [h, psi_add_psi_neg])
    have hcoeff : ∀ k : ZMod 17, fourierCoeff v k = 0 := by
      intro k
      have h1 : ∑ j : ZMod 17, (C17adj *ᵥ v) j * psi (-(k * j))
          = (psi (-k) + psi k) * fourierCoeff v k := by
        have hsplit : ∀ j : ZMod 17, (C17adj *ᵥ v) j * psi (-(k * j))
            = v (j + (-1)) * psi (-(k * j)) + v (j + 1) * psi (-(k * j)) := by
          intro j
          rw [adj_mulVec]
          rw [show j + (-1 : ZMod 17) = j - 1 by ring]
          ring
        rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
          sum_shift v k (-1), sum_shift v k 1]
        rw [show k * (-1 : ZMod 17) = -k by ring, mul_one]
        ring
      have h2 : ∑ j : ZMod 17, (C17adj *ᵥ v) j * psi (-(k * j)) = μ * fourierCoeff v k := by
        rw [fourierCoeff, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hA]
        simp [Pi.smul_apply, smul_eq_mul]
        ring
      have h3 : (psi (-k) + psi k - μ) * fourierCoeff v k = 0 := by
        have := h1.symm.trans h2
        linear_combination this
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (by linear_combination -h : μ = psi k + psi (-k)) (hne k)
      · exact h
    exact hv (funext (fun j => by
      have := fourier_inversion v j
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcoeff k, zero_mul])] at this
      simp only [Finset.sum_const_zero] at this
      have h17 : (17 : ℂ) ≠ 0 := by norm_num
      simpa [h17] using (mul_eq_zero.1 this.symm).resolve_left h17))
  · rintro ⟨k, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ZMod 17, a.val = (k : ℕ) :=
      ⟨((k : ℕ) : ZMod 17), ZMod.val_natCast_of_lt k.isLt⟩
    refine ⟨fun j => psi (a * j), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [mul_zero, Pi.zero_apply] at h0
      exact psi_ne_zero 0 h0
    · funext i
      have hval : (2 : ℂ) * Real.cos (2 * Real.pi * (k : ℕ) / 17) = psi a + psi (-a) := by
        rw [psi_add_psi_neg, ha]
      have e1 : a * (i - 1) = a * i + (-a) := by ring
      have e2 : a * (i + 1) = a * i + a := by ring
      rw [adj_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul, e1, e2, AddChar.map_add_eq_mul, hval]
      ring

/-- Reformulation of `Chem.huckel_C17` in terms of the spectrum: the spectrum of the Hückel
matrix of `C₁₇` is exactly `{2 cos (2πk/17) : k = 0, …, 16}`. -/
theorem huckel_C17_spectrum :
    spectrum ℂ C17adj = {μ : ℂ | ∃ k : Fin 17, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 17)} := by
  ext μ
  rw [Set.mem_setOf_eq, ← huckel_C17, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_ne_iff, ← Matrix.exists_mulVec_eq_zero_iff]
  have key : ∀ v : ZMod 17 → ℂ,
      (algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - C17adj) *ᵥ v = μ • v - C17adj *ᵥ v := by
    intro v
    rw [sub_mulVec, Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_mulVec]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (sub_eq_zero.1 ((key v) ▸ h)).symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, h, sub_self]⟩

end Chem

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

