import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

set_option grind.warning false

namespace Frontier

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/

lemma huang_offdiag_sum (x z : Cube n) (hz : ¬ z = x) :
    ∑ p : Fin n × Fin n,
      (if flipAt (flipAt x p.1) p.2 = z then hsign x p.1 * hsign (flipAt x p.1) p.2 else 0)
      = 0 := by
  refine Finset.sum_ninvolution (fun p => (p.2, p.1)) ?_ ?_ (fun _ => Finset.mem_univ _)
    (fun _ => rfl)
  · rintro ⟨i, k⟩
    show (if flipAt (flipAt x i) k = z then hsign x i * hsign (flipAt x i) k else 0)
        + (if flipAt (flipAt x k) i = z then hsign x k * hsign (flipAt x k) i else 0) = 0
    by_cases hik : i = k
    · subst hik
      rw [huang_offdiag_term_diag x z hz i, add_zero]
    · by_cases hc : flipAt (flipAt x i) k = z
      · have hc' : flipAt (flipAt x k) i = z := by rw [← flipAt_comm x hik]; exact hc
        rw [if_pos hc, if_pos hc']
        exact hsign_pair_cancel x hik
      · have hc' : ¬ flipAt (flipAt x k) i = z := by
          rw [← flipAt_comm x hik]; exact hc
        rw [if_neg hc, if_neg hc', add_zero]
  · rintro ⟨i, k⟩ hne hcon
    rw [Prod.ext_iff] at hcon
    obtain ⟨h1, -⟩ := hcon
    exact hne (by
      simp only at h1 ⊢
      subst h1
      exact huang_offdiag_term_diag x z hz k)

