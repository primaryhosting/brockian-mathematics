import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open scoped Pointwise

namespace AdditiveComb

variable {A B : Finset ℤ}

/-- The two "extremal translates" `A + {min B}` and `{max A} + B` meet in exactly one point,
namely `max A + min B`. -/

theorem inter_extremal_translates (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  apply Finset.eq_singleton_iff_unique_mem.2
  constructor
  · exact Finset.mem_inter.2
      ⟨Finset.add_mem_add (A.max'_mem hA) (Finset.mem_singleton_self _),
       Finset.add_mem_add (Finset.mem_singleton_self _) (B.min'_mem hB)⟩
  · rintro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx₁
    obtain ⟨a', ha', b', hb', hab⟩ := Finset.mem_add.1 hx₂
    rw [Finset.mem_singleton] at hb ha'
    subst hb; subst ha'
    have h1 : a ≤ A.max' hA := A.le_max' a ha
    have h2 : B.min' hB ≤ b' := B.min'_le b' hb'
    omega

/-- **Sumset lower bound** (the Cauchy–Davenport analogue over `ℤ`, i.e. the base case of
Freiman's lemma): for finite nonempty sets `A B` of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
