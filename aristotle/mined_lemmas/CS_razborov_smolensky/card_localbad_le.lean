import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_localbad_le (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) :
    (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card * 2 ^ t
      ≤ Fintype.card (Rand C t) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  rcases gate_dichotomy F C q t x i with hgood | ⟨S, w, j₀, hj₀S, hw, hbad⟩
  · have he : (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ρ _
      exact not_not_intro (hgood ρ)
    rw [he]; simp
  · refine card_gate_bad_le hq2 S (C.up i) ?_ w j₀ hj₀S hw i _ ?_
    · intro a b hab
      exact Fin.ext (by simpa [Circuit.up] using congrArg Fin.val hab)
    · intro ρ hρ
      exact hbad ρ (Finset.mem_filter.1 hρ).2

/-- For a suitable choice of the randomness, the approximation is correct on all but a
`size / 2^t` fraction of the inputs. -/
