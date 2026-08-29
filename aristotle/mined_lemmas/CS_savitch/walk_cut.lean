import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem walk_cut {f : ℕ → Fin n} {i j : ℕ} (hf0 : f 0 = a) (hf1 : f t = b)
    (hfs : ∀ u < t, R (f u) (f (u + 1)) = true)
    (hlt : i < j) (hj : j ≤ t) (hfe : f i = f j) : ∃ t' < t, Walk R t' a b := by
  set d := j - i with hd
  have hd0 : 0 < d := by omega
  refine ⟨t - d, by omega, fun u => if u ≤ i then f u else f (u + d), ?_, ?_, ?_⟩
  · simp [hf0]
  · dsimp only
    by_cases h : t - d ≤ i
    · have htj : t = j := by omega
      have hti : t - d = i := by omega
      rw [if_pos h, hti, hfe, ← hf1, htj]
    · rw [if_neg h]
      have he : t - d + d = t := by omega
      rw [he, hf1]
  · intro u hu
    dsimp only
    by_cases hA : u + 1 ≤ i
    · have h2 : u ≤ i := by omega
      rw [if_pos h2, if_pos hA]
      exact hfs u (by omega)
    · have hgu : (if u ≤ i then f u else f (u + d)) = f (u + d) := by
        by_cases h3 : u ≤ i
        · have hui : u = i := by omega
          subst hui
          rw [if_pos h3, hfe]
          congr 1
          omega
        · rw [if_neg h3]
      rw [hgu, if_neg hA]
      have he : u + 1 + d = (u + d) + 1 := by omega
      rw [he]
      exact hfs (u + d) (by omega)

/-- A walk of length at least `n` can be shortened. -/
