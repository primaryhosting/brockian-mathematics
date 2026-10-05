import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma IWinsFrom_of_forall [Inhabited A] {W : Set (ℕ → A)} {p : List A}
    (hp : Even p.length) (a : A) (h : ∀ b, IWinsFrom W (p ++ [a, b])) : IWinsFrom W p := by
  classical
  choose S hS using h
  refine ⟨fun q => if (p ++ [a]) <+: q then S (q.getD (p.length + 1) default) q else a, ?_⟩
  intro f hfp hfσ
  have hnp : ¬ (p ++ [a] <+: p) := by
    intro hc
    have := hc.length_le
    simp at this
  have hfa : f p.length = a := by
    have h0 := hfσ p.length le_rfl hp
    rw [hfp] at h0
    simpa [hnp] using h0
  obtain ⟨b, hb⟩ : ∃ b, f (p.length + 1) = b := ⟨_, rfl⟩
  have hq : takeF f (p.length + 2) = p ++ [a, b] := by
    rw [show p.length + 2 = (p.length + 1) + 1 from rfl, takeF_succ, takeF_succ, hfp, hfa, hb]
    simp
  refine hS b f (by rw [show (p ++ [a, b]).length = p.length + 2 by simp]; exact hq) ?_
  intro n hn hev
  have hn2 : p.length + 2 ≤ n := by simpa using hn
  have h1 := hfσ n (by omega) hev
  have hpre : p ++ [a] <+: takeF f n := by
    have h2 : takeF f (p.length + 2) <+: takeF f n := takeF_prefix f hn2
    rw [hq] at h2
    exact List.IsPrefix.trans (by simp) h2
  rw [h1]
  simp only [if_pos hpre, takeF_getD f (show p.length + 1 < n by omega), hb]

/-- From a position that is not winning for player I, every move of player I admits
a reply keeping the position not winning for player I. -/
