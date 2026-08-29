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

theorem inv2_step (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V)
    (h : Inv K c) (h2 : Inv2 K all c) : Inv2 K all (step E all c) := by
  match c with
  | .call 0 u v st => exact h2
  | .call (k + 1) u v st =>
      have hlen := h.1
      exact inv2_tryFrom 0 (by omega) h2
  | .ret b [] =>
      show Inv2 K all (Cfg.done b)
      intro f hf; simp at hf
  | .ret b (.mid1 k u v i m :: st) =>
      have hf0 := h2 (Frame.mid1 k u v i m) (by simp)
      have hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length := fun f hf =>
        h2 f (by simp [hf])
      by_cases hb : b = true
      · subst hb
        show Inv2 K all (Cfg.call k m v (Frame.mid2 k u v i m :: st))
        intro f hf
        simp only [Cfg.stack_call, List.mem_cons] at hf
        rcases hf with hf | hf
        · subst hf; simpa using hf0
        · exact hst f hf
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv2_tryFrom (i + 1) hf0.1 hst
  | .ret b (.mid2 k u v i m :: st) =>
      have hf0 := h2 (Frame.mid2 k u v i m) (by simp)
      have hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length := fun f hf =>
        h2 f (by simp [hf])
      by_cases hb : b = true
      · subst hb
        show Inv2 K all (Cfg.ret true st)
        exact fun f hf => hst f (by simpa using hf)
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv2_tryFrom (i + 1) hf0.1 hst
  | .done b =>
      show Inv2 K all (Cfg.done b)
      intro f hf; simp at hf

