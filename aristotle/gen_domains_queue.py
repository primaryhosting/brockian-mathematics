#!/usr/bin/env python3
"""Generate a broad multi-domain proof queue (Lean 4 / Mathlib formalizable statements)
for the overnight Aristotle submitter: quantum computing, quantum physics, mathematical
chemistry, computer science, and pure math. Each item carries a real statement so the
prompt is well-posed (these targets aren't in the Brockian registry)."""
import json
import pathlib

D = {
"qc": [  # quantum computing
 ("QC.no_cloning", "There is no unitary U on H⊗H with U(|ψ⟩⊗|0⟩)=|ψ⟩⊗|ψ⟩ for all states |ψ⟩ (no-cloning)."),
 ("QC.pauli_anticommute", "The Pauli matrices X,Y,Z pairwise anticommute and each squares to I."),
 ("QC.pauli_basis", "{I,X,Y,Z} is a basis of the ℂ-vector space of 2×2 complex matrices."),
 ("QC.hadamard_involutive", "The Hadamard matrix H satisfies H†=H and H²=I."),
 ("QC.hadamard_XZ", "H = (X+Z)/√2, and H X H = Z."),
 ("QC.cnot_unitary_involutive", "CNOT is unitary and CNOT²=I."),
 ("QC.bell_orthonormal", "The four Bell states form an orthonormal basis of ℂ²⊗ℂ²."),
 ("QC.chsh_tsirelson", "The quantum CHSH operator has operator norm ≤ 2√2 (Tsirelson's bound)."),
 ("QC.teleportation_identity", "The teleportation protocol's post-correction state equals the input state."),
 ("QC.deutsch_correct", "Deutsch's algorithm decides constant-vs-balanced of f:{0,1}→{0,1} with one oracle query."),
 ("QC.density_matrix_unitary_invariant", "If ρ⪰0 and Tr ρ=1 then UρU† ⪰0 and Tr(UρU†)=1 for unitary U."),
 ("QC.pure_state_zero_entropy", "The von Neumann entropy S(ρ)= -Tr(ρ log ρ) of a pure state is 0."),
 ("QC.qft_unitary", "The n-qubit quantum Fourier transform matrix is unitary."),
 ("QC.superdense_two_bits", "Superdense coding transmits 2 classical bits via 1 qubit + prior entanglement (encoding is injective on the 4 messages)."),
 ("QC.toffoli_unitary", "The Toffoli (CCNOT) matrix is a permutation matrix hence unitary and its own inverse."),
 ("QC.robertson_uncertainty", "For observables A,B and state ψ: ΔA·ΔB ≥ ½|⟨[A,B]⟩| (Robertson relation)."),
 ("QC.bloch_sphere_bijection", "Pure qubit states modulo global phase biject with points of the 2-sphere S²."),
 ("QC.kraus_trace_preserving", "A CPTP map Σ_k E_k ρ E_k† with Σ_k E_k†E_k = I preserves trace."),
 ("QC.ghz_nonlocal", "The 3-qubit GHZ state yields a deterministic Mermin paradox contradiction with local hidden variables."),
 ("QC.swap_test_overlap", "The SWAP test accepts two states with probability (1+|⟨ψ|φ⟩|²)/2."),
],
"qphys": [  # quantum / mathematical physics
 ("QPhys.canonical_commutator", "On Schwartz space, [x,p]=iℏ with p=-iℏ d/dx."),
 ("QPhys.hermitian_real_spectrum", "Every eigenvalue of a Hermitian operator is real."),
 ("QPhys.unitary_time_evolution", "For self-adjoint H, U(t)=exp(-iHt/ℏ) is unitary for all real t."),
 ("QPhys.oscillator_spectrum", "The quantum harmonic oscillator has spectrum {ℏω(n+½) : n∈ℕ} via ladder operators."),
 ("QPhys.particle_in_box", "The infinite square well of width L has energies E_n = n²π²ℏ²/(2mL²), n≥1."),
 ("QPhys.heisenberg_uncertainty", "Δx·Δp ≥ ℏ/2 for any normalized state (from the canonical commutator + Cauchy–Schwarz)."),
 ("QPhys.ehrenfest", "d⟨A⟩/dt = (i/ℏ)⟨[H,A]⟩ + ⟨∂A/∂t⟩ (Ehrenfest theorem)."),
 ("QPhys.stone_generator", "A strongly continuous one-parameter unitary group has a self-adjoint generator (Stone)."),
 ("QPhys.spectral_theorem_finite", "Every Hermitian matrix is unitarily diagonalizable with real eigenvalues."),
 ("QPhys.bcH_special", "For [A,B] central, e^A e^B = e^{A+B+½[A,B]} (BCH special case)."),
 ("QPhys.variational_bound", "For Hamiltonian H, ⟨ψ|H|ψ⟩/⟨ψ|ψ⟩ ≥ E_0 (ground-state variational bound)."),
 ("QPhys.parseval_fourier", "The Fourier transform is an L² isometry (Plancherel/Parseval)."),
 ("QPhys.noether_translation", "Translation invariance of the Lagrangian implies conservation of momentum (1D)."),
 ("QPhys.pauli_exclusion_antisym", "A two-fermion antisymmetric state with equal single-particle states is zero."),
 ("QPhys.commuting_simultaneous", "Two commuting Hermitian operators are simultaneously diagonalizable."),
],
"chem": [  # mathematical chemistry
 ("Chem.huckel_cycle_spectrum", "The adjacency eigenvalues of the cycle graph C_n are 2cos(2πk/n), k=0..n-1 (Hückel π-energies)."),
 ("Chem.euler_polyhedron", "For a convex polyhedron (e.g. fullerene cage) V−E+F=2 (Euler's formula)."),
 ("Chem.fullerene_pentagons", "A trivalent polyhedron with only pentagon/hexagon faces has exactly 12 pentagons."),
 ("Chem.balance_nullspace", "A chemical reaction balances iff the stoichiometric matrix has a positive integer null vector."),
 ("Chem.gibbs_phase_rule", "Degrees of freedom F = C − P + 2 as an affine-dimension count."),
 ("Chem.alkane_tree", "The carbon skeleton of an acyclic alkane C_nH_{2n+2} is a tree with n−1 C–C bonds."),
 ("Chem.polya_isomer_count", "Counting substitution isomers on a symmetric skeleton equals the Burnside/Pólya cycle-index average."),
 ("Chem.point_group_finite_O3", "Every molecular point group is a finite subgroup of O(3)."),
 ("Chem.benzene_D6h_irreps", "The character table of D₆ₕ has the correct number of irreducible representations (=conjugacy classes)."),
 ("Chem.wiener_path_formula", "The Wiener index of the path graph P_n equals C(n+1,3)."),
 ("Chem.handshake_valence", "Sum of atomic valences (vertex degrees) equals twice the number of bonds."),
 ("Chem.entropy_concave", "The Gibbs entropy −Σ p_i log p_i is concave in the probability vector."),
 ("Chem.arrhenius_monotone", "The Arrhenius rate k=A e^{−Ea/RT} is strictly increasing in T for Ea>0."),
 ("Chem.leChatelier_sign", "For an exothermic reaction, the equilibrium constant K(T) is strictly decreasing in T (van 't Hoff)."),
 ("Chem.molecular_orbital_count", "LCAO of n atomic orbitals yields exactly n molecular orbitals (dimension preservation)."),
],
"cs": [  # computer science
 ("CS.insertion_sort_correct", "insertionSort returns a sorted permutation of its input."),
 ("CS.mergesort_correct", "mergeSort returns a sorted permutation of its input."),
 ("CS.halting_undecidable", "There is no total computable H deciding whether program p halts on input x (diagonalization)."),
 ("CS.pumping_regular", "Every regular language satisfies the pumping lemma."),
 ("CS.euclid_gcd_correct", "Euclid's algorithm returns gcd(a,b) and terminates."),
 ("CS.binary_search_correct", "Binary search on a sorted array returns an index iff the key is present."),
 ("CS.pigeonhole_hash", "Any hash from an (n+1)-set to an n-set has a collision."),
 ("CS.kleene_regex_dfa", "A language is regular iff it is accepted by a DFA (Kleene, finite direction)."),
 ("CS.knaster_tarski", "A monotone map on a complete lattice has a least fixed point."),
 ("CS.cantor_powerset", "There is no surjection A → 𝒫(A) (Cantor)."),
 ("CS.huffman_optimal", "Huffman coding minimizes expected codeword length among prefix codes."),
 ("CS.master_theorem_case1", "T(n)=aT(n/b)+f(n) with f(n)=O(n^{log_b a − ε}) gives T(n)=Θ(n^{log_b a})."),
 ("CS.ackermann_total", "The Ackermann function is total (well-founded on lexicographic ℕ²)."),
 ("CS.dfa_complement_regular", "Regular languages are closed under complement."),
 ("CS.dijkstra_correct", "Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs."),
 ("CS.church_rosser_beta_diamond", "One-step parallel β-reduction in the λ-calculus has the diamond property."),
 ("CS.pcp_pigeon_bound", "Any prefix-free binary code satisfies Kraft's inequality Σ 2^{-ℓ_i} ≤ 1."),
 ("CS.rice_nontrivial", "Every nontrivial semantic property of programs is undecidable (Rice)."),
],
"math": [  # pure math (broad)
 ("Math.quadratic_reciprocity", "For odd primes p≠q: (p/q)(q/p) = (−1)^{((p−1)/2)((q−1)/2)}."),
 ("Math.sum_two_squares", "A prime p is a sum of two squares iff p=2 or p≡1 (mod 4)."),
 ("Math.lagrange_four_squares", "Every natural number is a sum of four squares."),
 ("Math.bertrand_postulate", "For every n≥1 there is a prime p with n<p≤2n."),
 ("Math.wilson_theorem", "n>1 is prime iff (n−1)! ≡ −1 (mod n)."),
 ("Math.cauchy_group", "If a prime p divides |G| then G has an element of order p (Cauchy)."),
 ("Math.lagrange_subgroup", "The order of a subgroup divides the order of a finite group."),
 ("Math.fta_algebra", "Every nonconstant complex polynomial has a root (fundamental theorem of algebra)."),
 ("Math.ivt", "A continuous function on [a,b] attains every value between f(a) and f(b)."),
 ("Math.bolzano_weierstrass", "Every bounded sequence in ℝ^n has a convergent subsequence."),
 ("Math.heine_borel", "A subset of ℝ^n is compact iff it is closed and bounded."),
 ("Math.mean_value", "A differentiable f on [a,b] has c with f'(c)=(f(b)−f(a))/(b−a)."),
 ("Math.weierstrass_approx", "Polynomials are dense in C([a,b]) under the sup norm."),
 ("Math.ramsey_3_3", "R(3,3)=6: any 2-coloring of K₆'s edges has a monochromatic triangle, and K₅ has a coloring without one."),
 ("Math.halls_marriage", "A bipartite graph has a perfect matching iff Hall's condition holds."),
 ("Math.inclusion_exclusion", "|⋃A_i| = Σ(−1)^{|S|+1}|⋂_{i∈S}A_i| (inclusion–exclusion)."),
 ("Math.catalan_closed", "The nth Catalan number equals C(2n,n)/(n+1)."),
 ("Math.euler_pentagonal", "Euler's pentagonal number theorem for the partition generating function."),
 ("Math.brouwer_2d", "Every continuous self-map of the closed 2-disk has a fixed point."),
 ("Math.baire_category", "A complete metric space is not a countable union of nowhere-dense sets."),
 ("Math.dilworth", "In a finite poset, the minimum antichain cover equals the longest chain length."),
 ("Math.sperner_lemma", "Every Sperner coloring of a triangulated simplex has an odd number of rainbow cells."),
 ("Math.chinese_remainder", "For pairwise-coprime moduli, ℤ/(∏nᵢ) ≅ ∏ ℤ/nᵢ."),
 ("Math.fermat_little", "For prime p and a not divisible by p, a^{p−1} ≡ 1 (mod p)."),
 ("Math.abel_ruffini_deg5", "The general quintic is not solvable by radicals (Galois-theoretic)."),
 ("Math.gauss_bonnet_polygon", "The angle sum of a geodesic triangle on the unit sphere exceeds π by its area."),
],
}
RANK = {"qc": 0, "math": 1, "cs": 1, "qphys": 2, "chem": 2}


def main():
    q = []
    for dom, items in D.items():
        for name, stmt in items:
            q.append({"target": name, "tier": f"DOMAIN-{dom}", "goal":
                      f"Prove in Lean 4 (Mathlib), axiom-clean.", "statement": stmt, "rank": RANK[dom]})
    out = pathlib.Path(__file__).resolve().parent / "domains_queue.json"
    out.write_text(json.dumps({"count": len(q), "queue": q}, indent=1))
    print(f"wrote {out} with {len(q)} targets across {len(D)} domains")
    for dom, items in D.items():
        print(f"  {dom}: {len(items)}")


if __name__ == "__main__":
    main()
