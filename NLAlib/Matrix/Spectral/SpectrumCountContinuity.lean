import NLAlib.Matrix.Spectral.SpectrumCount
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
/-!
# Constant multiplicity counts in separated compact spectral sets

Root tuples with a fixed allocation to two compact sets form a compact box.
Their polynomial values at `n+1` fixed scalars form a compact image, hence
each root-count fiber is closed. The finitely many fibers are also open,
so a connected parameter space has a constant count.
Source: Horn–Johnson (2013), Theorem 6.1.1; no root labeling is assumed.
-/

noncomputable section
open Polynomial
open scoped Matrix Topology Classical

namespace NLAlib

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [TopologicalSpace Ω]

/-- A continuous matrix family confined spectrally to two disjoint compact
sets has closed algebraic root-count fibers in either set. Source:
Horn–Johnson (2013), Theorem 6.1.1; compact images of finite root boxes prove
this without contour integration or a continuous eigenvalue labeling. -/
theorem isClosed_setOf_charpolyRootCountIn_eq
    (A : Ω → Matrix n n ℂ) (hA : Continuous A) (K L : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hdisj : Disjoint K L)
    (hspec : ∀ t, spectrum ℂ (A t) ⊆ K ∪ L) (r : ℕ) :
    IsClosed {t | charpolyRootCountIn (A t) K = r} := by
  let F : (n → ℂ) → Fin (Fintype.card n + 1) → ℂ :=
    fun z j => ∏ i, ((j.val : ℂ) - z i)
  let G : Ω → Fin (Fintype.card n + 1) → ℂ :=
    fun t j => (A t).charpoly.eval (j.val : ℂ)
  let box (s : Finset n) : Set (n → ℂ) := {z | ∀ i, z i ∈ if i ∈ s then K else L}
  let Cᵣ : Set (Fin (Fintype.card n + 1) → ℂ) :=
    ⋃ s : {s : Finset n // s.card = r}, F '' box s.val
  have hF : Continuous F := by fun_prop
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    change Continuous (fun t => (A t).charpoly.eval (j.val : ℂ))
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hA).matrix_det
  have hbox (s : Finset n) : IsCompact (box s) := by
    apply isCompact_pi_infinite
    intro i
    split_ifs <;> assumption
  have hC : IsCompact Cᵣ := isCompact_iUnion fun s => (hbox s.val).image hF
  have hcount (t : Ω) (s : Finset n) (z : n → ℂ) (hz : z ∈ box s) (hval : F z = G t) :
      charpolyRootCountIn (A t) K = s.card := by
    have hchar : (A t).charpoly = ∏ i, (X - C (z i)) :=
      charpoly_eq_prod_of_eval_eq (A t) z (fun j => (congrFun hval j).symm)
    rw [charpolyRootCountIn_eq_card_filter (A t) K z hchar]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ s
    · have hzi : z i ∈ K := by simpa only [box, hi, ite_true] using hz i
      exact iff_of_true hzi hi
    · have hzi : z i ∈ L := by simpa only [box, hi, ite_false] using hz i
      have hnot : z i ∉ K := fun hk => Set.disjoint_left.mp hdisj hk hzi
      exact iff_of_false hnot hi
  have heq : {t | charpolyRootCountIn (A t) K = r} = G ⁻¹' Cᵣ := by
    ext t
    constructor
    · intro ht
      obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization
        (A t) (Fintype.equivFin n).symm
      let z : n → ℂ := fun i => T i i
      let s : Finset n := Finset.univ.filter (fun i => z i ∈ K)
      have hsc : s.card = r := (charpolyRootCountIn_eq_card_filter (A t) K z hchar).symm.trans ht
      have hzspec (i : n) : z i ∈ spectrum ℂ (A t) := by
        apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
        rw [hchar]
        simp only [Polynomial.IsRoot, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [z]
      have hzbox : z ∈ box s := by
        intro i
        by_cases hi : z i ∈ K
        · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_true]
        · have hzL : z i ∈ L := (hspec t (hzspec i)).resolve_left hi
          simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_false] using hzL
      have hval : F z = G t := by
        funext j
        change (∏ i, ((j.val : ℂ) - T i i)) = (A t).charpoly.eval (j.val : ℂ)
        rw [hchar]
        simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact Set.mem_iUnion.mpr ⟨⟨s, hsc⟩, z, hzbox, hval⟩
    · intro ht
      obtain ⟨s, z, hz, hval⟩ := Set.mem_iUnion.mp ht
      exact (hcount t s.val z hz hval).trans s.property
  rw [heq]
  exact hC.isClosed.preimage hG

/-- Along a continuous family over a preconnected parameter space, the
number of characteristic roots in either of two disjoint compact spectral
sets is constant, including algebraic multiplicities. Source:
Horn–Johnson (2013), Theorem 6.1.1; the finite closed root-count fibers are
clopen, so no root tracking or analytic projector is required. -/
theorem charpolyRootCountIn_eq_of_preconnected [PreconnectedSpace Ω]
    (A : Ω → Matrix n n ℂ) (hA : Continuous A) (K L : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hdisj : Disjoint K L)
    (hspec : ∀ t, spectrum ℂ (A t) ⊆ K ∪ L) (s t : Ω) :
    charpolyRootCountIn (A s) K = charpolyRootCountIn (A t) K := by
  have hclosed (r : ℕ) : IsClosed {x | charpolyRootCountIn (A x) K = r} :=
    isClosed_setOf_charpolyRootCountIn_eq A hA K L hK hL hdisj hspec r
  let r := charpolyRootCountIn (A s) K
  let S : Set Ω := {x | charpolyRootCountIn (A x) K = r}
  have hcomp : Sᶜ = ⋃ j : {j : Fin (Fintype.card n + 1) // (j : ℕ) ≠ r},
      {x | charpolyRootCountIn (A x) K = (j.val : ℕ)} := by
    ext x
    constructor
    · intro hx
      change charpolyRootCountIn (A x) K ≠ r at hx
      refine Set.mem_iUnion.mpr ⟨⟨⟨charpolyRootCountIn (A x) K,
        Nat.lt_succ_of_le (charpolyRootCountIn_le_card (A x) K)⟩, hx⟩, rfl⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      change charpolyRootCountIn (A x) K ≠ r
      rw [show charpolyRootCountIn (A x) K = (j.val : ℕ) from hj]
      exact j.property
  have hopen : IsOpen S := by
    rw [← isClosed_compl_iff, hcomp]
    exact isClosed_iUnion_of_finite fun j => hclosed j.val
  have hall : (Set.univ : Set Ω) ⊆ S :=
    isPreconnected_univ.subset_isClopen ⟨hclosed r, hopen⟩ ⟨s, Set.mem_univ s, rfl⟩
  exact (hall (Set.mem_univ t)).symm

end NLAlib
