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

def upd {n d : Nat} (D : Nat) (m : memT n d D) (x : Fin n × Fin d) : memT n d D :=
  let j := m.2.2.1.1
  let j' : Fin (Tm d D + 1) := ⟨min (j + 1) (Tm d D), by omega⟩
  if j % (D + 1) = D then (m.1, m.2.1, j', m.1, m.2.2.2.2)
  else (m.1, m.2.1, j', x.1, m.2.2.2.2 || decide (x.1 = m.2.1))

/-- The machine implementing the algorithm: it enumerates all edge-label sequences of
length `D`, walking along each of them from `s` and checking whether `t` is ever reached. -/
