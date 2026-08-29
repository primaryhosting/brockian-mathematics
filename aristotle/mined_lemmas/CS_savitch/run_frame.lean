/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem run_frame (hl : ∀ x : X, x ∈ l) :
    ∀ (k : ℕ) (f : Frame X), f.lvl = k → ∀ rest : List (Frame X),
      ∃ t b, (sstep badj l)^[t] ⟨f :: rest, none⟩ = ⟨rest, some b⟩ ∧
        (b = true ↔ fval badj l f) := by
  intro k
  induction k with
  | zero =>
    intro f hf rest
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    simp only at hf
    subst hf
    refine ⟨1, decide (u = v) || badj u v, ?_, ?_⟩
    · simp
    · simp [fval]
  | succ k ih =>
    have inner : ∀ (M : ℕ) (u v : X) (mid : ℕ) (ph : Bool),
        2 * (l.length + 1 - mid) + (if ph then 1 else 2) ≤ M → ∀ rest : List (Frame X),
        ∃ t b, (sstep badj l)^[t] ⟨⟨k + 1, u, v, mid, ph⟩ :: rest, none⟩ = ⟨rest, some b⟩ ∧
          (b = true ↔ fval badj l ⟨k + 1, u, v, mid, ph⟩) := by
      intro M
      induction M with
      | zero =>
        intro u v mid ph hm rest
        exfalso
        cases ph <;> simp at hm
      | succ M ihM =>
        intro u v mid ph hm rest
        cases hmid : l[mid]? with
        | none =>
          have hlen : l.length ≤ mid := List.getElem?_eq_none_iff.1 hmid
          refine ⟨1, false, by simpa using sstep_call_none (badj := badj) hmid, ?_⟩
          simp only [Bool.false_eq_true, false_iff]
          cases ph with
          | false =>
            rintro ⟨j, hj, m, hjm, -, -⟩
            rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ j)] at hjm
            simp at hjm
          | true =>
            rintro (⟨m, hjm, -⟩ | ⟨j, hj, m, hjm, -, -⟩)
            · rw [hmid] at hjm; simp at hjm
            · rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ j)] at hjm
              simp at hjm
        | some m =>
          have hmidlt : mid < l.length := by
            by_contra hc
            rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ mid)] at hmid
            simp at hmid
          cases ph with
          | false =>
            obtain ⟨t₁, b₁, ht₁, hb₁⟩ := ih ⟨k, u, m, 0, false⟩ rfl
              (⟨k + 1, u, v, mid, false⟩ :: rest)
            have hchild : (b₁ = true) ↔ Reach (adjOf badj) k u m := by
              rw [hb₁]; exact fval_fresh hl k u m
            have e1 : (sstep badj l)^[1] (⟨⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ : SState X) =
                ⟨⟨k, u, m, 0, false⟩ :: ⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ := by
              simpa using sstep_call_some_false hmid
            have e12 := iterate_trans e1 ht₁
            cases hb : b₁ with
            | true =>
              rw [hb] at e12
              have hReach : Reach (adjOf badj) k u m := hchild.1 hb
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, false⟩ :: rest, some true⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ := by simp
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v mid true (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid, true⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, false⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro (⟨m', hm', hr⟩ | ⟨j, hj, m', hjm', h1, h2⟩)
                  · rw [hmid] at hm'
                    obtain rfl := Option.some.inj hm'
                    exact ⟨mid, le_rfl, m, hmid, hReach, hr⟩
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  rcases eq_or_lt_of_le hj with rfl | hlt
                  · rw [hmid] at hjm'
                    obtain rfl := Option.some.inj hjm'
                    exact Or.inl ⟨m, hmid, h2⟩
                  · exact Or.inr ⟨j, hlt, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
            | false =>
              rw [hb] at e12
              have hnr : ¬ Reach (adjOf badj) k u m := by
                intro hc; simpa [hb] using hchild.2 hc
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, false⟩ :: rest, some false⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid + 1, false⟩ :: rest, none⟩ := by
                simp [Nat.min_eq_left (show mid + 1 ≤ l.length by omega)]
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v (mid + 1) false (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid + 1, false⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, false⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  exact ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  rcases eq_or_lt_of_le hj with rfl | hlt
                  · rw [hmid] at hjm'
                    obtain rfl := Option.some.inj hjm'
                    exact absurd h1 hnr
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
          | true =>
            obtain ⟨t₁, b₁, ht₁, hb₁⟩ := ih ⟨k, m, v, 0, false⟩ rfl
              (⟨k + 1, u, v, mid, true⟩ :: rest)
            have hchild : (b₁ = true) ↔ Reach (adjOf badj) k m v := by
              rw [hb₁]; exact fval_fresh hl k m v
            have e1 : (sstep badj l)^[1] (⟨⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ : SState X) =
                ⟨⟨k, m, v, 0, false⟩ :: ⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ := by
              simpa using sstep_call_some_true hmid
            have e12 := iterate_trans e1 ht₁
            cases hb : b₁ with
            | true =>
              rw [hb] at e12
              have hReach : Reach (adjOf badj) k m v := hchild.1 hb
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, true⟩ :: rest, some true⟩ : SState X) =
                  ⟨rest, some true⟩ := by simp
              refine ⟨1 + (t₁ + 1), true, iterate_trans e12 e3, ?_⟩
              simp only [true_iff]
              exact Or.inl ⟨m, hmid, hReach⟩
            | false =>
              rw [hb] at e12
              have hnr : ¬ Reach (adjOf badj) k m v := by
                intro hc; simpa [hb] using hchild.2 hc
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, true⟩ :: rest, some false⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid + 1, false⟩ :: rest, none⟩ := by
                simp [Nat.min_eq_left (show mid + 1 ≤ l.length by omega)]
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v (mid + 1) false (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid + 1, false⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, true⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  exact Or.inr ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro (⟨m', hm', hr⟩ | ⟨j, hj, m', hjm', h1, h2⟩)
                  · rw [hmid] at hm'
                    obtain rfl := Option.some.inj hm'
                    exact absurd hr hnr
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
    intro f hf rest
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    simp only at hf
    subst hf
    exact inner _ u v mid ph le_rfl rest

/-- Accepting configurations of the stack machine: the stack is empty and the value returned is
`true`. -/
