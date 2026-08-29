import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

/-- The four dimensional real Hilbert space in which we work. -/
abbrev KSSpace : Type := EuclideanSpace ℝ (Fin 4)

/-- A vector of `KSSpace` given by its four coordinates. -/

lemma ksCount_sum_eq_one (v : KSSpace → Bool)
    (hv : ∀ e : Fin 4 → KSSpace, (∀ i, e i ≠ 0) → (∀ i j, i ≠ j → ⟪e i, e j⟫_ℝ = 0) →
      ∃! i, v (e i) = true)
    (x0 x1 x2 x3 : KSSpace)
    (h0 : x0 ≠ 0) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (h3 : x3 ≠ 0)
    (o01 : ⟪x0, x1⟫_ℝ = 0) (o02 : ⟪x0, x2⟫_ℝ = 0) (o03 : ⟪x0, x3⟫_ℝ = 0)
    (o12 : ⟪x1, x2⟫_ℝ = 0) (o13 : ⟪x1, x3⟫_ℝ = 0) (o23 : ⟪x2, x3⟫_ℝ = 0) :
    ksCount v x0 + ksCount v x1 + ksCount v x2 + ksCount v x3 = 1 := by
  have hne : ∀ i : Fin 4, (![x0, x1, x2, x3] : Fin 4 → KSSpace) i ≠ 0 := by
    intro i; fin_cases i <;> simpa using ‹_›
  have hor : ∀ i j : Fin 4, i ≠ j →
      ⟪(![x0, x1, x2, x3] : Fin 4 → KSSpace) i,
        (![x0, x1, x2, x3] : Fin 4 → KSSpace) j⟫_ℝ = 0 := by
    have o10 : ⟪x1, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o01
    have o20 : ⟪x2, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o02
    have o30 : ⟪x3, x0⟫_ℝ = 0 := by rw [real_inner_comm]; exact o03
    have o21 : ⟪x2, x1⟫_ℝ = 0 := by rw [real_inner_comm]; exact o12
    have o31 : ⟪x3, x1⟫_ℝ = 0 := by rw [real_inner_comm]; exact o13
    have o32 : ⟪x3, x2⟫_ℝ = 0 := by rw [real_inner_comm]; exact o23
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨i, hi, hu⟩ := hv _ hne hor
  have e0 : v x0 = true → (0 : Fin 4) = i := fun h => hu 0 (by simpa using h)
  have e1 : v x1 = true → (1 : Fin 4) = i := fun h => hu 1 (by simpa using h)
  have e2 : v x2 = true → (2 : Fin 4) = i := fun h => hu 2 (by simpa using h)
  have e3 : v x3 = true → (3 : Fin 4) = i := fun h => hu 3 (by simpa using h)
  have c0 : ksCount v x0 = if (0 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (0 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e0 hc))]
  have c1 : ksCount v x1 = if (1 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (1 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e1 hc))]
  have c2 : ksCount v x2 = if (2 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (2 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e2 hc))]
  have c3 : ksCount v x3 = if (3 : Fin 4) = i then 1 else 0 := by
    unfold ksCount
    by_cases h : (3 : Fin 4) = i
    · rw [if_pos h, if_pos]
      rw [← h] at hi; simpa using hi
    · rw [if_neg h, if_neg (fun hc => h (e3 hc))]
  rw [c0, c1, c2, c3]
  fin_cases i <;> decide

/-- **Kochen–Specker theorem** (base case: dimension four).

There is no noncontextual hidden-variable assignment for quantum mechanics: no map `v` sending
each nonzero vector `x` of the four dimensional Hilbert space (equivalently, the rank-one
projection onto `ℝ ∙ x`) to a definite truth value `v x`, depending on the vector alone and not
on the measurement context, can have the property that in every orthogonal decomposition of the
identity into four rank-one projections exactly one projection is assigned the value `true`.

The proof is the parity argument of Cabello–Estebaranz–García-Alcaine, using 18 vectors arranged
into 9 orthogonal bases in which each vector occurs exactly twice. -/
