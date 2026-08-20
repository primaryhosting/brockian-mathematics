import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma uncond_not_condPos {s t : CSt P.N P.V} (h : Uncond P s t) : ¬ CondPos P s t := by
  rintro (hE | ⟨hB, hP, -⟩)
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hB, -, -⟩
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · have h2 := Base9_tpc P hB
      rw [Ext_tpc P hE] at h2; exact absurd h2 (by decide)
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hP', -⟩
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · exact hP hP'

