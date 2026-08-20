/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem noElig_dom_of {i x : ℕ} (h : ∀ y, i ≤ y → y < x → (elig M r C i y).Dom) :
    (noElig M r C i x).Dom := by
  induction x with
  | zero => exact trivial
  | succ k ih =>
    have hk := ih (fun y hy hyk => h y hy (by omega))
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp hk
    rw [noElig_succ]
    rcases Nat.lt_or_ge k i with hlt | hge
    · refine Part.dom_iff_mem.mpr ⟨t, ?_⟩
      simp only [Part.mem_bind_iff]
      exact ⟨t, ht, by simp [hlt]⟩
    · obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (h k hge (by omega))
      refine Part.dom_iff_mem.mpr ⟨t && !e, ?_⟩
      simp only [Part.mem_bind_iff]
      refine ⟨t, ht, ?_⟩
      rw [(by simp; omega : decide (k < i) = false)]
      simp only [cond_false, Part.mem_map_iff]
      exact ⟨e, he, rfl⟩

