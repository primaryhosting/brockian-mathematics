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
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma Hchain_rowsum (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (B : ℝ)
    (hB : ∀ p, ∑ q, ‖b p q‖ ≤ B) (c : Conf n L) :
    ∑ c', ‖Hchain b c c'‖ ≤ L * B := by
  have key : ∀ j : ZMod L, ∑ c' : Conf n L,
      ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
        then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ ≤ B := by
    intro j
    have e1 : ∀ c' : Conf n L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖
        = if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then ‖b (c j, c (j + 1)) (c' j, c' (j + 1))‖ else 0 := by
      intro c'; split <;> simp
    rw [Finset.sum_congr rfl (fun c' _ => e1 c'), ← Finset.sum_filter]
    have hinj : ∀ x ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
        ∀ y ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
        (fun c' : Conf n L => (c' j, c' (j + 1))) x = (fun c' : Conf n L => (c' j, c' (j + 1))) y →
        x = y := by
      intro x hx y hy hxy
      simp only [Finset.mem_filter] at hx hy
      funext i
      by_cases h1 : i = j
      · subst h1; exact congrArg Prod.fst hxy
      · by_cases h2 : i = j + 1
        · subst h2; exact congrArg Prod.snd hxy
        · rw [← hx.2 i h1 h2, ← hy.2 i h1 h2]
    calc ∑ c' ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
          ‖b (c j, c (j + 1)) (c' j, c' (j + 1))‖
        = ∑ q ∈ (Finset.univ.filter
            (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)).image
            (fun c' : Conf n L => (c' j, c' (j + 1))), ‖b (c j, c (j + 1)) q‖ :=
          (Finset.sum_image (f := fun q => ‖b (c j, c (j + 1)) q‖) hinj).symm
      _ ≤ ∑ q : Fin n × Fin n, ‖b (c j, c (j + 1)) q‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
      _ ≤ B := hB _
  calc ∑ c' : Conf n L, ‖Hchain b c c'‖
      ≤ ∑ c' : Conf n L, ∑ j : ZMod L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ :=
        Finset.sum_le_sum fun c' _ => norm_sum_le _ _
    _ = ∑ j : ZMod L, ∑ c' : Conf n L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ := Finset.sum_comm
    _ ≤ ∑ _j : ZMod L, B := Finset.sum_le_sum fun j _ => key j
    _ = L * B := by simp [ZMod.card, nsmul_eq_mul]

/-- **Flux estimate.**  If the bond matrix conserves the total magnetization, then any two
configurations connected by the Hamiltonian have twist phases differing, modulo `2π`, by at
most `2π(n-1)/L`. -/
