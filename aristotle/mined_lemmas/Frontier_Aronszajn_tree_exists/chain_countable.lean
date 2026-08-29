/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem chain_countable (C : Set Node) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  by_contra hunc
  -- lengths are injective on `C`
  have hinj : Set.InjOn Node.len C := by
    intro s hs t ht hlen
    rcases eq_or_ne s t with h | h
    · exact h
    · rcases hC hs ht h with hle | hle
      · exact le_antisymm hle ⟨hlen.ge, fun ξ hξ => (hle.2 ξ (hlen ▸ hξ)).symm⟩
      · exact (le_antisymm hle ⟨hlen.le, fun ξ hξ => (hle.2 ξ (hlen ▸ hξ)).symm⟩).symm
  -- `C` has nodes of arbitrarily large length
  have hunbdd : ∀ α < ω₁, ∃ s ∈ C, α < s.len := by
    intro α hα
    by_contra hcon
    push_neg at hcon
    refine hunc (Set.MapsTo.countable_of_injOn (f := Node.len) (t := Set.Iio (α + 1))
      (fun s hs => lt_of_le_of_lt (hcon s hs) (lt_add_one α)) hinj ?_)
    exact countable_Iio_of_lt_omega1 ((Cardinal.isSuccLimit_omega 1).add_one_lt hα)
  -- the union of the chain is a finite-to-one function on `Set.Iio ω₁`
  have hfin : ∀ n : ℕ, {ξ : Ordinal | ξ < ω₁ ∧ chainFn C ξ = n}.Finite := by
    intro n
    rw [← Set.not_infinite]
    intro hinf
    set emb := hinf.natEmbedding with hemb
    obtain ⟨α, hα, hbound⟩ :=
      exists_bound_of_seq (fun k => ((emb k : Ordinal))) (fun k => (emb k).2.1)
    obtain ⟨s, hs, hslen⟩ := hunbdd α hα
    have hsub : Set.range (fun k => ((emb k : Ordinal))) ⊆
        {ξ : Ordinal | ξ < s.len ∧ s.fn ξ = n} := by
      rintro _ ⟨k, rfl⟩
      have h1 : ((emb k : Ordinal)) < s.len := lt_trans (hbound k) hslen
      refine ⟨h1, ?_⟩
      rw [← chainFn_eq hC hs h1]
      exact (emb k).2.2
    have hinjg : Function.Injective (fun k => ((emb k : Ordinal))) := fun a b hab =>
      emb.injective (Subtype.ext hab)
    exact Set.infinite_range_of_injective hinjg (Set.Finite.subset (s.fn_finite_fiber n) hsub)
  -- hence `Set.Iio ω₁` is countable, a contradiction
  refine not_countable_Iio_omega1 ?_
  have : Set.Iio (ω₁ : Ordinal) ⊆ ⋃ n : ℕ, {ξ : Ordinal | ξ < ω₁ ∧ chainFn C ξ = n} := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr ⟨chainFn C ξ, hξ, rfl⟩
  exact Set.Countable.mono this (Set.countable_iUnion fun n => (hfin n).countable)

/-! ## Tree structure -/

