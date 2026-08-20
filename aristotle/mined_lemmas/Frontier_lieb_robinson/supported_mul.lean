/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean 4 requires `import` commands to
-- precede every other command, including module doc-strings.)

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

/-- Spin configurations of a chain of `N` sites (each site carries a qubit). -/
abbrev Config (N : ℕ) := Fin N → Fin 2

/-- Observables of the spin chain: linear operators on the `2^N`-dimensional Hilbert space,
represented as matrices indexed by spin configurations. -/
abbrev SpinOp (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- `Supported S M` says that the observable `M` acts only on the sites in `S`, i.e.
`M = M₀ ⊗ 1` with `M₀` acting on the sites of `S`.  Concretely, matrix elements vanish
unless the configurations agree off `S`, and they depend only on the restrictions to `S`. -/

theorem supported_mul {S T : Set (Fin N)} {M P : SpinOp N} (hM : Supported S M)
    (hP : Supported T P) : Supported (S ∪ T) (M * P) := by
  classical
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  constructor
  · rintro c d ⟨i, hi, hne⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun e _ => ?_)
    by_cases hce : c i = e i
    · have hz : P e d = 0 := hP0 e d ⟨i, fun hiT => hi (Or.inr hiT), by rw [← hce]; exact hne⟩
      rw [hz, mul_zero]
    · have hz : M c e = 0 := hM0 c e ⟨i, fun hiS => hi (Or.inl hiS), hce⟩
      rw [hz, zero_mul]
  · intro c d c' d' hcc' hdd' hcd hc'd'
    rw [Matrix.mul_apply, Matrix.mul_apply]
    set perm : Config N ≃ Config N :=
      Equiv.piCongrRight
        (fun i => if i ∈ S ∪ T then Equiv.refl (Fin 2) else Equiv.swap (c i) (c' i))
    have hperm : ∀ (e : Config N) (i : Fin N),
        perm e i = (if i ∈ S ∪ T then Equiv.refl (Fin 2) else Equiv.swap (c i) (c' i)) (e i) :=
      fun e i => rfl
    have hperm_in : ∀ (e : Config N) (i : Fin N), i ∈ S ∪ T → perm e i = e i := by
      intro e i hi
      rw [hperm e i, if_pos hi]
      rfl
    have hperm_out : ∀ (e : Config N) (i : Fin N), i ∉ S ∪ T →
        perm e i = Equiv.swap (c i) (c' i) (e i) := by
      intro e i hi
      rw [hperm e i, if_neg hi]
    refine Fintype.sum_equiv perm _ _ (fun e => ?_)
    -- pointwise transfer of the two "diagonal" conditions
    have hA_iff : ∀ i, i ∉ S → (c i = e i ↔ c' i = perm e i) := by
      intro i hi
      by_cases hiT : i ∈ T
      · rw [hperm_in e i (Or.inr hiT), hcc' i (Or.inr hiT)]
      · have hiST : i ∉ S ∪ T := fun hmem => hmem.elim hi hiT
        rw [hperm_out e i hiST]
        constructor
        · intro hce; rw [← hce, Equiv.swap_apply_left]
        · intro hce; exact ((swap_eq_right_iff (c i) (c' i) (e i)).mp hce.symm).symm
    have hB_iff : ∀ i, i ∉ T → (e i = d i ↔ perm e i = d' i) := by
      intro i hi
      by_cases hiS : i ∈ S
      · rw [hperm_in e i (Or.inl hiS), hdd' i (Or.inl hiS)]
      · have hiST : i ∉ S ∪ T := fun hmem => hmem.elim hiS hi
        rw [hperm_out e i hiST, ← hc'd' i hiST, ← hcd i hiST]
        exact (swap_eq_right_iff (c i) (c' i) (e i)).symm
    by_cases hda : ∀ i, i ∉ S → c i = e i
    · by_cases hdb : ∀ i, i ∉ T → e i = d i
      · have h1 : M c e = M c' (perm e) :=
          hM1 c e c' (perm e) (fun i hi => hcc' i (Or.inl hi))
            (fun i hi => (hperm_in e i (Or.inl hi)).symm) hda
            (fun i hi => (hA_iff i hi).mp (hda i hi))
        have h2 : P e d = P (perm e) d' :=
          hP1 e d (perm e) d' (fun i hi => (hperm_in e i (Or.inr hi)).symm)
            (fun i hi => hdd' i (Or.inr hi)) hdb
            (fun i hi => (hB_iff i hi).mp (hdb i hi))
        rw [h1, h2]
      · push_neg at hdb
        obtain ⟨i, hi, hne⟩ := hdb
        have hz1 : P e d = 0 := hP0 e d ⟨i, hi, hne⟩
        have hz2 : P (perm e) d' = 0 :=
          hP0 (perm e) d' ⟨i, hi, fun hcon => hne ((hB_iff i hi).mpr hcon)⟩
        rw [hz1, hz2, mul_zero, mul_zero]
    · push_neg at hda
      obtain ⟨i, hi, hne⟩ := hda
      have hz1 : M c e = 0 := hM0 c e ⟨i, hi, hne⟩
      have hz2 : M c' (perm e) = 0 :=
        hM0 c' (perm e) ⟨i, hi, fun hcon => hne ((hA_iff i hi).mpr hcon)⟩
      rw [hz1, hz2, zero_mul, zero_mul]

/-- Observables supported on disjoint sets of sites commute. -/
