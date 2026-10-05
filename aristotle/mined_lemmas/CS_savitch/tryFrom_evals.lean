/-
The configuration graph of a space bounded nondeterministic machine, and the
deterministic middle-first search run on it.
-/
import RequestProject.NTM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Sim

variable (M : NTM) (s : ℕ) (x : List Bool)

/-- Vertices of the configuration graph: the configurations of `M`, plus a sink
`none` which is entered from every accepting configuration. -/
abbrev Node : Type := Option (Conf M x.length s)

/-- Edges of the configuration graph.  A single edge query only inspects the
local transition table of `M` at the scanned symbols. -/

theorem tryFrom_evals (E : V → V → Bool) (all : List V) (k : ℕ) (u v : V)
    (IH : ∀ (u' v' : V) (st' : List (Frame V)),
      ∃ n, (step E all)^[n] (.call k u' v' st') = .ret (sreach E all k u' v') st') :
    ∀ (d i : ℕ), all.length - i ≤ d → ∀ st : List (Frame V),
      ∃ n, (step E all)^[n] (tryFrom all k u v i st) =
        .ret ((all.drop i).any (fun m => sreach E all k u m && sreach E all k m v)) st := by
  intro d
  induction d with
  | zero =>
      intro i hi st
      have hlen : all.length ≤ i := by omega
      have hnone : all[i]? = none := List.getElem?_eq_none hlen
      have hdrop : all.drop i = [] := List.drop_eq_nil_of_le hlen
      exact ⟨0, by simp [tryFrom, hnone, hdrop]⟩
  | succ d ih =>
      intro i hi st
      by_cases hlt : i < all.length
      · set m := all[i] with hmdef
        have hgi : all[i]? = some m := List.getElem?_eq_getElem hlt
        have hdrop : all.drop i = m :: all.drop (i + 1) := List.drop_eq_getElem_cons hlt
        have hstart : tryFrom all k u v i st = Cfg.call k u m (.mid1 k u v i m :: st) := by
          simp [tryFrom, hgi]
        obtain ⟨n1, hn1⟩ := IH u m (.mid1 k u v i m :: st)
        by_cases h1 : sreach E all k u m = true
        · obtain ⟨n2, hn2⟩ := IH m v (.mid2 k u v i m :: st)
          have e2 : (step E all)^[1] (Cfg.ret (sreach E all k u m) (.mid1 k u v i m :: st))
              = Cfg.call k m v (.mid2 k u v i m :: st) := by rw [h1]; rfl
          by_cases h2 : sreach E all k m v = true
          · have e4 : (step E all)^[1] (Cfg.ret (sreach E all k m v) (.mid2 k u v i m :: st))
                = Cfg.ret true st := by rw [h2]; rfl
            refine ⟨n1 + 1 + n2 + 1, ?_⟩
            rw [hstart]
            have := iter_trans (step E all) (iter_trans (step E all)
              (iter_trans (step E all) hn1 e2) hn2) e4
            rw [this]
            simp [hdrop, h1, h2]
          · simp only [Bool.not_eq_true] at h2
            obtain ⟨n3, hn3⟩ := ih (i + 1) (by omega) st
            have e4 : (step E all)^[1] (Cfg.ret (sreach E all k m v) (.mid2 k u v i m :: st))
                = tryFrom all k u v (i + 1) st := by rw [h2]; rfl
            refine ⟨n1 + 1 + n2 + 1 + n3, ?_⟩
            rw [hstart]
            have := iter_trans (step E all) (iter_trans (step E all) (iter_trans (step E all)
              (iter_trans (step E all) hn1 e2) hn2) e4) hn3
            rw [this, hdrop]
            simp [h2]
        · simp only [Bool.not_eq_true] at h1
          obtain ⟨n3, hn3⟩ := ih (i + 1) (by omega) st
          have e2 : (step E all)^[1] (Cfg.ret (sreach E all k u m) (.mid1 k u v i m :: st))
              = tryFrom all k u v (i + 1) st := by rw [h1]; rfl
          refine ⟨n1 + 1 + n3, ?_⟩
          rw [hstart]
          have := iter_trans (step E all) (iter_trans (step E all) hn1 e2) hn3
          rw [this, hdrop]
          simp [h1]
      · push_neg at hlt
        have hnone : all[i]? = none := List.getElem?_eq_none hlt
        have hdrop : all.drop i = [] := List.drop_eq_nil_of_le hlt
        exact ⟨0, by simp [tryFrom, hnone, hdrop]⟩

/-- The machine evaluates a call correctly: from `call k u v st` it returns
`sreach E all k u v` on the same stack. -/
