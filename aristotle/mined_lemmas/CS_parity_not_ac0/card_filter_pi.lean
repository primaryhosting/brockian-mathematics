import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma card_filter_pi {ℓ : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin ℓ → α)).filter (fun T => ∀ r, P (T r))).card
      = ((Finset.univ : Finset α).filter P).card ^ ℓ := by
  classical
  have : ((Finset.univ : Finset (Fin ℓ → α)).filter (fun T => ∀ r, P (T r)))
      = Fintype.piFinset (fun _ : Fin ℓ => (Finset.univ : Finset α).filter P) := by
    ext T
    simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp

