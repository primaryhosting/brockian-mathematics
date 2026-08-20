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

theorem commute_of_disjoint {S T : Set (Fin N)} {M P : SpinOp N} (hST : Disjoint S T)
    (hM : Supported S M) (hP : Supported T P) : M * P = P * M := by
  classical
  have hMP := supported_mul hM hP
  have hPM := supported_mul hP hM
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  ext c d
  by_cases hcd : ∀ i, i ∉ S ∪ T → c i = d i
  · -- both matrix elements reduce to a single term of the sum
    set e1 : Config N := fun i => if i ∈ S then d i else c i with he1
    set e2 : Config N := fun i => if i ∈ T then d i else c i with he2
    have hSnotT : ∀ i, i ∈ S → i ∉ T := fun i hi => Set.disjoint_left.mp hST hi
    have hTnotS : ∀ i, i ∈ T → i ∉ S := fun i hi => Set.disjoint_right.mp hST hi
    have hleft : (M * P) c d = M c e1 * P e1 d := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single e1 (fun e _ hne => ?_) (fun hcon => absurd (Finset.mem_univ e1) hcon)
      by_contra hprod
      have h1 : ∀ i, i ∉ S → c i = e i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hM0 c e ⟨i, hi, hci⟩, zero_mul])
      have h2 : ∀ i, i ∉ T → e i = d i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hP0 e d ⟨i, hi, hci⟩, mul_zero])
      refine hne (funext fun i => ?_)
      by_cases hiS : i ∈ S
      · rw [he1]; simp only [if_pos hiS]; exact h2 i (hSnotT i hiS)
      · rw [he1]; simp only [if_neg hiS]; exact (h1 i hiS).symm
    have hright : (P * M) c d = P c e2 * M e2 d := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single e2 (fun e _ hne => ?_) (fun hcon => absurd (Finset.mem_univ e2) hcon)
      by_contra hprod
      have h1 : ∀ i, i ∉ T → c i = e i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hP0 c e ⟨i, hi, hci⟩, zero_mul])
      have h2 : ∀ i, i ∉ S → e i = d i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hM0 e d ⟨i, hi, hci⟩, mul_zero])
      refine hne (funext fun i => ?_)
      by_cases hiT : i ∈ T
      · rw [he2]; simp only [if_pos hiT]; exact h2 i (hTnotS i hiT)
      · rw [he2]; simp only [if_neg hiT]; exact (h1 i hiT).symm
    have hMeq : M c e1 = M e2 d := by
      refine hM1 c e1 e2 d (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
      · rw [he2]; simp only [if_neg (hSnotT i hi)]
      · rw [he1]; simp only [if_pos hi]
      · rw [he1]; simp only [if_neg hi]
      · rw [he2]
        by_cases hiT : i ∈ T
        · simp only [if_pos hiT]
        · simp only [if_neg hiT]
          exact hcd i (fun hmem => hmem.elim hi hiT)
    have hPeq : P e1 d = P c e2 := by
      refine hP1 e1 d c e2 (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
      · rw [he1]; simp only [if_neg (hTnotS i hi)]
      · rw [he2]; simp only [if_pos hi]
      · rw [he1]
        by_cases hiS : i ∈ S
        · simp only [if_pos hiS]
        · simp only [if_neg hiS]
          exact hcd i (fun hmem => hmem.elim hiS hi)
      · rw [he2]; simp only [if_neg hi]
    rw [hleft, hright, hMeq, hPeq, mul_comm]
  · push_neg at hcd
    obtain ⟨i, hi, hne⟩ := hcd
    have hi' : i ∉ T ∪ S := fun hmem => hi hmem.symm
    rw [hMP.1 c d ⟨i, hi, hne⟩, hPM.1 c d ⟨i, hi', hne⟩]

end

section
variable {N : ℕ} {ι : Type*}

