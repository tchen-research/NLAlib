import NLAlib.Matrix.InterlacingConverse
import NLAlib.Matrix.InterlacingReindex

/-!
# Converse interlacing for prescribed real symmetric matrices

Every weakly interlacing ordered target spectrum is realized by bordering,
a positive rank-one update, or a negative rank-one update of the prescribed
matrix. Characteristic polynomials retain all algebraic multiplicities;
trace and squared coupling norms have their exact sum-difference values.
Source: Horn–Johnson (2013), Theorems 4.3.21 and 4.3.26.
-/
noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Any weakly interlacing target list is the spectrum of a symmetric
border of a prescribed real symmetric matrix, with the last diagonal entry
fixed by the difference of spectral sums. The supplied complete original
root list records its actual spectrum. Source: Horn–Johnson (2013),
Theorem 4.3.21; repeated roots and empty leading matrices are included.
atlas: interlacing-converse (partial) -/
theorem exists_bordered_charpoly_of_interlacing
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (d : Fin (Fintype.card n) → ℝ) (b : Fin (Fintype.card n + 1) → ℝ)
    (hd : Monotone d) (hb : Monotone b)
    (hchar : A.charpoly = ∏ i, (X - C (d i)))
    (hinter : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) :
    ∃ v : n → ℝ, ∃ a : ℝ,
      (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) v)
        (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a)).charpoly =
          (∏ i, (X - C (b i))) ∧ a = (∑ i, b i) - ∑ i, d i := by
  obtain ⟨v, a, hv⟩ := exists_bordered_diagonal_charpoly d b hd hb hinter
  let e := (Fintype.equivFin n).symm
  have hdN : A.charpoly = ∏ i, (X - C ((d ∘ e.symm) i)) :=
    hchar.trans (e.symm.prod_comp (fun i => X - C (d i))).symm
  obtain ⟨u, hu⟩ := exists_bordered_charpoly_of_diagonal_construction
    A hA (d ∘ e.symm) (v ∘ e.symm) a hdN
  have hout := hu.trans ((charpoly_diagonal_arrowhead_reindex e d v a).trans hv)
  refine ⟨u, a, hout, ?_⟩
  rw [border_eq_sum_sub_trace_of_charpoly_eq_prod A u a b hout,
    trace_eq_sum_of_charpoly_eq_prod A d hchar]

/-- Any weakly interlacing positive rank-one target list is realized by
`A+vvᵀ` for a prescribed real symmetric matrix, with squared coupling norm
the difference of target and original spectral sums. Source: Horn–Johnson
(2013), Theorem 4.3.26; all repeated roots, equalities and empty shapes remain.
atlas: interlacing-converse (partial) -/
theorem exists_add_vecMulVec_charpoly_of_interlacing
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (d b : Fin (Fintype.card n) → ℝ) (hd : Monotone d) (hb : Monotone b)
    (hchar : A.charpoly = ∏ i, (X - C (d i)))
    (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j, i.val + 1 = j.val → b i ≤ d j) :
    ∃ v : n → ℝ, (A + Matrix.vecMulVec v v).charpoly =
      (∏ i, (X - C (b i))) ∧ (∑ i, (v i) ^ 2) = (∑ i, b i) - ∑ i, d i := by
  obtain ⟨v, hv⟩ := exists_diagonal_add_vecMulVec_charpoly d b hd hb hlo hhi
  let e := (Fintype.equivFin n).symm
  have hdN : A.charpoly = ∏ i, (X - C ((d ∘ e.symm) i)) :=
    hchar.trans (e.symm.prod_comp (fun i => X - C (d i))).symm
  obtain ⟨u, hu⟩ := exists_add_vecMulVec_charpoly_of_diagonal_construction
    A hA (d ∘ e.symm) (v ∘ e.symm) hdN
  have hout := hu.trans ((charpoly_diagonal_add_vecMulVec_reindex e d v).trans hv)
  refine ⟨u, hout, ?_⟩
  rw [sum_sq_eq_sum_sub_trace_of_charpoly_add_vecMulVec A u b hout,
    trace_eq_sum_of_charpoly_eq_prod A d hchar]

/-- Any weakly interlacing negative rank-one target list is realized by
`A-vvᵀ` for a prescribed real symmetric matrix, with squared coupling norm
the original spectral sum minus the target sum. Source: Horn–Johnson
(2013), Theorem 4.3.26; reversal and negation reduce to the positive case,
without strictness assumptions or loss of multiplicities or empty cases.
atlas: interlacing-converse (partial) -/
theorem exists_sub_vecMulVec_charpoly_of_interlacing
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (d b : Fin (Fintype.card n) → ℝ) (hd : Monotone d) (hb : Monotone b)
    (hchar : A.charpoly = ∏ i, (X - C (d i)))
    (hlo : ∀ i, b i ≤ d i)
    (hhi : ∀ i j, i.val + 1 = j.val → d i ≤ b j) :
    ∃ v : n → ℝ, (A - Matrix.vecMulVec v v).charpoly =
      (∏ i, (X - C (b i))) ∧ (∑ i, (v i) ^ 2) = (∑ i, d i) - ∑ i, b i := by
  let d' : Fin (Fintype.card n) → ℝ := fun i => -d i.rev
  let b' : Fin (Fintype.card n) → ℝ := fun i => -b i.rev
  have hd' : Monotone d' := fun i j hij => neg_le_neg (hd (Fin.rev_le_rev.mpr hij))
  have hb' : Monotone b' := fun i j hij => neg_le_neg (hb (Fin.rev_le_rev.mpr hij))
  have hlo' (i : Fin (Fintype.card n)) : d' i ≤ b' i := neg_le_neg (hlo i.rev)
  have hhi' (i j : Fin (Fintype.card n)) (hij : i.val + 1 = j.val) : b' i ≤ d' j := by
    apply neg_le_neg
    apply hhi j.rev i.rev
    simp only [Fin.val_rev]
    omega
  let e := (Fintype.equivFin n).symm
  have hdN : A.charpoly = ∏ i, (X - C ((d ∘ e.symm) i)) :=
    hchar.trans (e.symm.prod_comp (fun i => X - C (d i))).symm
  have hneg : (-A).charpoly = ∏ i, (X - C (d' i)) := by
    rw [charpoly_neg_eq_prod_of_isHermitian A hA (d ∘ e.symm) hdN]
    calc
      (∏ i, (X - C (-((d ∘ e.symm) i)))) = ∏ i, (X - C (-d i)) :=
        e.symm.prod_comp (fun i => X - C (-d i))
      _ = ∏ i, (X - C (d' i)) := (Equiv.prod_comp Fin.revPerm (fun i => X - C (-d i))).symm
  obtain ⟨v, hv, _⟩ := exists_add_vecMulVec_charpoly_of_interlacing
    (-A) hA.neg d' b' hd' hb' hneg hlo' hhi'
  have hS : (-A + Matrix.vecMulVec v v).IsHermitian := by
    apply hA.neg.add
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_vecMulVec]
  have hbN : (-A + Matrix.vecMulVec v v).charpoly = ∏ i, (X - C ((b' ∘ e.symm) i)) :=
    hv.trans (e.symm.prod_comp (fun i => X - C (b' i))).symm
  have hout : (A - Matrix.vecMulVec v v).charpoly = ∏ i, (X - C (b i)) := by
    have ht := charpoly_neg_eq_prod_of_isHermitian _ hS (b' ∘ e.symm) hbN
    have hmat : -(-A + Matrix.vecMulVec v v) = A - Matrix.vecMulVec v v := by abel
    rw [hmat] at ht
    refine ht.trans ?_
    calc
      (∏ i, (X - C (-((b' ∘ e.symm) i)))) = ∏ i, (X - C (-b' i)) :=
        e.symm.prod_comp (fun i => X - C (-b' i))
      _ = ∏ i : Fin (Fintype.card n), (X - C (b i.rev)) := by simp only [b', neg_neg]
      _ = ∏ i, (X - C (b i)) := Equiv.prod_comp Fin.revPerm (fun i => X - C (b i))
  refine ⟨v, hout, ?_⟩
  rw [sum_sq_eq_trace_sub_sum_of_charpoly_sub_vecMulVec A v b hout,
    trace_eq_sum_of_charpoly_eq_prod A d hchar]

end NLAlib
