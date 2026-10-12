import NLAlib.Matrix.Spectral.SchurTriangularization
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Polynomial

/-!
# Counting characteristic roots in a set

Counts use the actual characteristic-root multiset, so all algebraic
multiplicities are retained. Complete root tuples can be recovered from
finitely many polynomial values, avoiding any choice of continuous root labels.
Source: Horn–Johnson (2013), Theorem 6.1.1.
-/

noncomputable section
open Polynomial
open scoped Matrix Topology Classical

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The number of characteristic eigenvalues in a set, counted with
algebraic multiplicity. Source: Horn–Johnson (2013), Theorem 6.1.1;
the characteristic-root multiset includes every repeated root. -/
def charpolyRootCountIn (A : Matrix n n ℂ) (K : Set ℂ) : ℕ := by
  classical
  exact A.charpoly.roots.countP (fun z => z ∈ K)

/-- A complete characteristic factorization computes root counts by the
number of list entries in the set. Source: Horn–Johnson (2013), Theorem 6.1.1;
this explicitly connects index counts to algebraic multiplicities. -/
theorem charpolyRootCountIn_eq_card_filter (A : Matrix n n ℂ) (K : Set ℂ)
    (d : n → ℂ) (hd : A.charpoly = ∏ i, (X - C (d i))) :
    charpolyRootCountIn A K = (Finset.univ.filter (fun i => d i ∈ K)).card := by
  classical
  have hroots : (∏ i, (X - C (d i))).roots = Finset.univ.val.map d := by
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (d i))
  dsimp only [charpolyRootCountIn]
  rw [hd, hroots, Multiset.countP_map]
  rfl

/-- A characteristic-root count is at most the matrix dimension, including
empty shapes. Source: Horn–Johnson (2013), Theorem 6.1.1. -/
theorem charpolyRootCountIn_le_card (A : Matrix n n ℂ) (K : Set ℂ) :
    charpolyRootCountIn A K ≤ Fintype.card n := by
  classical
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization A (Fintype.equivFin n).symm
  rw [charpolyRootCountIn_eq_card_filter A K (fun i => T i i) hchar]
  exact Finset.card_filter_le Finset.univ (fun i => T i i ∈ K)

/-- Values at `n+1` fixed distinct complex scalars determine a characteristic
polynomial among monic products of `n` root factors. Polynomial interpolation;
helper for exact isolated-spectrum counts. -/
theorem charpoly_eq_prod_of_eval_eq (A : Matrix n n ℂ) (d : n → ℂ)
    (h : ∀ j : Fin (Fintype.card n + 1),
      A.charpoly.eval (j.val : ℂ) = ∏ i, ((j.val : ℂ) - d i)) :
    A.charpoly = ∏ i, (X - C (d i)) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq A.charpoly (∏ i, (X - C (d i)))
    (f := fun j : Fin (Fintype.card n + 1) => (j.val : ℂ))
  · intro i j hij
    apply Fin.ext
    dsimp at hij
    exact_mod_cast hij
  · intro j
    simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h j
  · simp only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
      Finset.card_univ, max_self, Fintype.card_fin, Nat.lt_succ_self]

end NLAlib
