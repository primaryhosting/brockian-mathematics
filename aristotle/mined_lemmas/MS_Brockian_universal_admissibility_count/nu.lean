import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
