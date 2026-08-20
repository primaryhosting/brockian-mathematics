/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem E_limit_finOne : FinOne (E a) a := by
  have hc : (Set.Iio a).Countable := countable_Iio_of_lt ha
  intro v
  refine Set.Finite.subset (Eaux_finOne h0 hs IH (v + 1) v) ?_
  rintro x ⟨hx, hv⟩
  obtain ⟨n, hn⟩ := cseq_cofinal hc hx
  have hex : ∃ k, x < cseq a k := ⟨n, hn⟩
  have hNspec : x < cseq a (Nat.find hex) := Nat.find_spec hex
  have hNpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, cseq_zero] at hNspec
    exact absurd hNspec (by simp)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 :=
    ⟨Nat.find hex - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hNpos)).symm⟩
  have hmin : ¬ (x < cseq a k) := Nat.find_min hex (by omega)
  have hNspec' : x < cseq a (k + 1) := hk ▸ hNspec
  have hval : E a x = max (E (cseq a (k + 1)) x) k := by
    rw [E_eq_Eaux h0 hs hNspec', Eaux_succ, if_neg hmin]
  have hkv : k ≤ v := by rw [← hv, hval]; exact le_max_right _ _
  have hxlt : x < cseq a (v + 1) :=
    lt_of_lt_of_le hNspec' ((cseq_mono a).monotone (Nat.succ_le_succ hkv))
  exact ⟨hxlt, by rw [← E_eq_Eaux h0 hs hxlt]; exact hv⟩

include ha h0 hs IH in
