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

lemma theta_flux (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hcons : ∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2)
    (c c' : Conf n L) (h : Hchain b c c' ≠ 0) :
    ∃ k : ℤ, |theta c' - theta c - 2 * Real.pi * k| ≤ 2 * Real.pi * ((n : ℝ) - 1) / L := by
  have hLpos : (0 : ℝ) < L := by
    have := Nat.pos_of_ne_zero (NeZero.ne L); exact_mod_cast this
  rw [Hchain] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hcond : ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i := by
    by_contra hx; rw [if_neg hx] at hj; exact hj rfl
  rw [if_pos hcond] at hj
  have hw : w n (c j) + w n (c (j + 1)) = w n (c' j) + w n (c' (j + 1)) := hcons _ _ hj
  set d : ℤ := (c j).val - (c' j).val with hd
  have hd1 : w n (c' j) - w n (c j) = 2 * d := by simp [w, hd]; ring
  have hd2 : w n (c' (j + 1)) - w n (c (j + 1)) = -(2 * d) := by omega
  have e1 : (w n (c' j) : ℝ) - (w n (c j) : ℝ) = 2 * (d : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hd1
  have e2 : (w n (c' (j + 1)) : ℝ) - (w n (c (j + 1)) : ℝ) = -(2 * (d : ℝ)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hd2
  have hsum : ∑ i ∈ ({j, j + 1} : Finset (ZMod L)),
        (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ))
      = ∑ i : ZMod L, (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ)) := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [hcond i hi.1 hi.2]
    ring
  have hpair : ∑ i ∈ ({j, j + 1} : Finset (ZMod L)),
        (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ))
      = ((j.val : ℝ) - ((j + 1).val : ℝ)) * (2 * (d : ℝ)) := by
    by_cases hjj : j = j + 1
    · have hd0 : d = 0 := by rw [← hjj] at hw; omega
      rw [← hjj]
      simp [e1, hd0]
    · rw [Finset.sum_pair hjj, e1, e2]
      ring
  have hdiff : theta c' - theta c
      = (Real.pi / L) * (((j.val : ℝ) - ((j + 1).val : ℝ)) * (2 * (d : ℝ))) := by
    rw [theta, theta, ← mul_sub, ← Finset.sum_sub_distrib, ← hpair, hsum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
  have hvalj : ((j + 1).val : ℝ) = (j.val : ℝ) + 1 - (if j + 1 = 0 then (L : ℝ) else 0) := by
    have hz := zmod_val_sub_one (L := L) (j + 1)
    rw [add_sub_cancel_right] at hz
    have hz2 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hz2
    split_ifs at hz2 ⊢ with hcase
    · linarith
    · linarith
  have hdn : |(d : ℝ)| ≤ (n : ℝ) - 1 := by
    have h1 : ((c j).val : ℤ) < n := by exact_mod_cast (c j).isLt
    have h2 : ((c' j).val : ℤ) < n := by exact_mod_cast (c' j).isLt
    have h3 : -((n : ℤ) - 1) ≤ d := by omega
    have h4 : d ≤ (n : ℤ) - 1 := by omega
    rw [abs_le]
    constructor
    · have : ((-((n : ℤ) - 1) : ℤ) : ℝ) ≤ ((d : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at this; linarith
    · have : ((d : ℤ) : ℝ) ≤ (((n : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h4
      push_cast at this; linarith
  have hfin : |(-(2 * Real.pi * (d : ℝ) / L))| ≤ 2 * Real.pi * ((n : ℝ) - 1) / L := by
    rw [abs_neg, abs_div, abs_of_pos hLpos, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    gcongr
  by_cases hj0 : j + 1 = 0
  · refine ⟨d, ?_⟩
    rw [hdiff, hvalj, if_pos hj0]
    have heq : (Real.pi / L) * (((j.val : ℝ) - ((j.val : ℝ) + 1 - L)) * (2 * (d : ℝ)))
        - 2 * Real.pi * (d : ℝ) = -(2 * Real.pi * (d : ℝ) / L) := by field_simp; ring
    rw [heq]
    exact hfin
  · refine ⟨0, ?_⟩
    rw [hdiff, hvalj, if_neg hj0]
    have heq : (Real.pi / L) * (((j.val : ℝ) - ((j.val : ℝ) + 1 - 0)) * (2 * (d : ℝ)))
        - 2 * Real.pi * ((0 : ℤ) : ℝ) = -(2 * Real.pi * (d : ℝ) / L) := by
      push_cast; field_simp; ring
    rw [heq]
    exact hfin

/-- **The momentum shift.**  On the zero magnetization sector, translating a configuration
shifts the twist phase by `π` times twice the spin at the origin. -/
