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

theorem inv_step (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V) (h : Inv K c) :
    Inv K (step E all c) := by
  match c with
  | .call 0 u v st =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      refine ⟨by omega, hchain, ?_⟩
      intro f hf
      have := hhead f hf
      omega
  | .call (k + 1) u v st =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      exact inv_tryFrom (all := all) 0 (by omega) hchain hhead
  | .ret b [] => trivial
  | .ret b (.mid1 k u v i m :: st) =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      have hh : k + (st.length + 1) = K := by
        have := hhead (Frame.mid1 k u v i m) (by simp)
        simpa using this
      obtain ⟨hst, hchain'⟩ := hchain
      simp only [Frame.level_mid1] at hst
      by_cases hb : b = true
      · subst hb
        refine ⟨?_, ⟨?_, hchain'⟩, ?_⟩
        · simp only [List.length_cons]; omega
        · intro g hg; simpa using hst g hg
        · intro f hf
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
          subst hf
          simp
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv_tryFrom (all := all) (i + 1) (by omega)
          hchain' hst
  | .ret b (.mid2 k u v i m :: st) =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      have hh : k + (st.length + 1) = K := by
        have := hhead (Frame.mid2 k u v i m) (by simp)
        simpa using this
      obtain ⟨hst, hchain'⟩ := hchain
      simp only [Frame.level_mid2] at hst
      by_cases hb : b = true
      · subst hb
        refine ⟨by omega, hchain', ?_⟩
        intro g hg
        have := hst g hg
        omega
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv_tryFrom (all := all) (i + 1) (by omega) hchain' hst
  | .done b => trivial

