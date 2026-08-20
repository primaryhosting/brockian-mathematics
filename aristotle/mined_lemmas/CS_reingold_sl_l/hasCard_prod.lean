/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem hasCard_prod {α β : Type} {N M : Nat} (hα : HasCard α N) (hβ : HasCard β M) :
    HasCard (α × β) (N * M) := by
  obtain ⟨f, hf⟩ := hα
  obtain ⟨g, hg⟩ := hβ
  refine ⟨fun p => ⟨(g p.2).1 + M * (f p.1).1, ?_⟩, ?_⟩
  · have hx : (f p.1).1 < N := (f p.1).2
    have hy : (g p.2).1 < M := (g p.2).2
    have h1 : M * ((f p.1).1 + 1) ≤ M * N := Nat.mul_le_mul_left M hx
    have h2 : M * ((f p.1).1 + 1) = M * (f p.1).1 + M := by
      rw [Nat.mul_add, Nat.mul_one]
    have : N * M = M * N := Nat.mul_comm _ _
    omega
  · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (g b1).1 + M * (f a1).1 = (g b2).1 + M * (f a2).1 := by
      simpa using congrArg Fin.val h
    have hy1 : (g b1).1 < M := (g b1).2
    have hy2 : (g b2).1 < M := (g b2).2
    have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hy1
    have e1 : ((g b1).1 + M * (f a1).1) % M = (g b1).1 % M := Nat.add_mul_mod_self_left _ _ _
    have e2 : ((g b2).1 + M * (f a2).1) % M = (g b2).1 % M := Nat.add_mul_mod_self_left _ _ _
    have hb : (g b1).1 = (g b2).1 := by
      have e3 : (g b1).1 % M = (g b2).1 % M := by rw [← e1, ← e2, h']
      rwa [Nat.mod_eq_of_lt hy1, Nat.mod_eq_of_lt hy2] at e3
    have ha : (f a1).1 = (f a2).1 := by
      have : M * (f a1).1 = M * (f a2).1 := by omega
      exact Nat.eq_of_mul_eq_mul_left hM this
    have ha' : a1 = a2 := hf (Fin.ext ha)
    have hb' : b1 = b2 := hg (Fin.ext hb)
    simp [ha', hb']

/-! ## Undirected graphs presented by rotation maps -/

/-- An undirected `d`-regular (multi)graph on the vertex set `Fin n`, presented by its
*rotation map*: `rot (v, a) = (w, b)` means that the `a`-th edge out of `v` leads to `w`,
and arrives there as the `b`-th edge of `w`.  Involutivity of `rot` is exactly the
statement that the graph is undirected. -/
structure RotGraph (n d : Nat) where
  rot : Fin n × Fin d → Fin n × Fin d
  rot_involutive : ∀ x, rot (rot x) = x

namespace RotGraph

/-- Following the edge labelled `a` out of the vertex `v`. -/
