import Mathlib
namespace MS.Algebra


theorem cayley_hamilton {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.eval₂ (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) M = 0 :=
  M.aeval_self_charpoly

