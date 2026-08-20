/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

theorem scalar_on_range (P M : Matrix (Fin n) (Fin n) ℂ) (hidem : P * P = P) (hP0 : P ≠ 0)
    (h : ∀ ψ : Fin n → ℂ, P *ᵥ ψ = ψ → ∃ t : ℂ, M *ᵥ ψ = t • ψ) :
    ∃ lam : ℂ, M * P = lam • P := by
  have hex : ∃ v : Fin n → ℂ, P *ᵥ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hP0 ?_
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨v₀, hv₀⟩ := hex
  have hrange : ∀ w : Fin n → ℂ, P *ᵥ (P *ᵥ w) = P *ᵥ w := by
    intro w; rw [Matrix.mulVec_mulVec, hidem]
  obtain ⟨ψ₀, hψ₀r, hψ₀0⟩ : ∃ ψ₀ : Fin n → ℂ, P *ᵥ ψ₀ = ψ₀ ∧ ψ₀ ≠ 0 :=
    ⟨P *ᵥ v₀, hrange v₀, hv₀⟩
  obtain ⟨t₀, ht₀⟩ := h ψ₀ hψ₀r
  refine ⟨t₀, Matrix.ext_iff_mulVec.mpr ?_⟩
  intro w
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  obtain ⟨ψ, hψr, hψe⟩ : ∃ ψ : Fin n → ℂ, P *ᵥ ψ = ψ ∧ ψ = P *ᵥ w := ⟨P *ᵥ w, hrange w, rfl⟩
  rw [← hψe]
  rcases eq_or_ne ψ 0 with hz | hz
  · simp [hz]
  obtain ⟨t, ht⟩ := h ψ hψr
  obtain ⟨t', ht'⟩ := h (ψ + ψ₀) (by rw [Matrix.mulVec_add, hψr, hψ₀r])
  rw [Matrix.mulVec_add, ht, ht₀, smul_add] at ht'
  have key : (t' - t) • ψ = (t₀ - t') • ψ₀ := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ← ht']
    abel
  have keyM : (t' - t) • (M *ᵥ ψ) = (t₀ - t') • (M *ᵥ ψ₀) := by
    have := congrArg (fun v : Fin n → ℂ => M *ᵥ v) key
    simpa only [Matrix.mulVec_smul] using this
  rw [ht, ht₀, smul_smul, smul_smul] at keyM
  have keyM2 : ((t' - t) * (t - t₀)) • ψ = 0 := by
    have e1 : ((t' - t) * (t - t₀)) • ψ = ((t' - t) * t) • ψ - (t₀ * (t' - t)) • ψ := by
      rw [← sub_smul]; ring_nf
    have e2 : (t₀ * (t' - t)) • ψ = ((t₀ - t') * t₀) • ψ₀ := by
      calc (t₀ * (t' - t)) • ψ = t₀ • ((t' - t) • ψ) := by rw [smul_smul]
        _ = t₀ • ((t₀ - t') • ψ₀) := by rw [key]
        _ = ((t₀ - t') * t₀) • ψ₀ := by rw [smul_smul]; ring_nf
    rw [e1, e2, keyM, sub_self]
  have htt : t = t₀ := by
    have h4 := (smul_eq_zero.1 keyM2).resolve_right hz
    rcases mul_eq_zero.1 h4 with h1 | h1
    · have ht'eq : t' = t := by linear_combination h1
      rw [ht'eq, sub_self, zero_smul] at key
      have h5 := (smul_eq_zero.1 key.symm).resolve_right hψ₀0
      linear_combination -h5
    · linear_combination h1
  rw [ht, htt]

/-! ## Correctability implies the Knill–Laflamme conditions -/

