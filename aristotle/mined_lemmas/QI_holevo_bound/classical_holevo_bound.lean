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
