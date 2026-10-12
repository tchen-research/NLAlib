import NLAlib.ForMathlib.Algebra.InterlacingWeights
import NLAlib.ForMathlib.Algebra.InterlacingInterpolation
import NLAlib.Matrix.InterlacingDeterminants

/-!
# Inverse interlacing for distinct original eigenvalues

Nonnegative residues and exact polynomial interpolation construct bordered
matrices and positive rank-one updates. The target spectrum may have
repetitions or coincide with original roots; zero residues give zero
couplings. Source: Horn--Johnson (2013), Section 4.3.
-/

noncomputable section
open Polynomial
open scoped BigOperators Matrix
namespace NLAlib

/-- Any weakly interlacing target list is the exact characteristic spectrum
of a real symmetric border of a strictly ordered diagonal matrix. The
border's corner is the trace difference. Empty original lists, target
repetitions, and zero couplings are included. Source: Horn--Johnson (2013),
Section 4.3; atlas: interlacing-converse (partial). -/
theorem exists_bordered_diagonal_charpoly_of_strictMono
    {n : ℕ} (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ)
    (hd : StrictMono d) (hb : Monotone b)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) :
    ∃ (v : Fin n → ℝ) (a : ℝ), a = (∑ i, b i) - (∑ i, d i) ∧
      (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
        (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a)).charpoly =
          ∏ j, (X - C (b j)) := by
  let p : ℝ[X] := ∏ i, (X - C (d i))
  let q : ℝ[X] := ∏ i, (X - C (b i))
  let a : ℝ := (∑ i, b i) - (∑ i, d i)
  let w (j : Fin n) : ℝ := -q.eval (d j) /
    (∏ l ∈ Finset.univ.erase j, (d j - d l))
  have hw (j : Fin n) : 0 ≤ w j := by
    simpa [w, q, eval_prod] using
      neg_prod_sub_div_prod_erase_nonneg_of_bordered_interlacing d b hd hb h j
  let v (j : Fin n) : ℝ := Real.sqrt (w j)
  have hv (j : Fin n) : (v j) ^ 2 = w j := Real.sq_sqrt (hw j)
  have hp : p.Monic := monic_prod_X_sub_C _ _
  have hq : q.Monic := monic_prod_X_sub_C _ _
  have hpn : p.natDegree = n := by simp [p]
  have hqn : q.natDegree = n + 1 := by simp [q]
  have hbase : ((X - C a) * p).Monic := (monic_X_sub_C a).mul hp
  have hbn : ((X - C a) * p).natDegree = n + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero a) hp.ne_zero, natDegree_X_sub_C, hpn]
    omega
  have hc : q.nextCoeff = ((X - C a) * p).nextCoeff := by
    rw [(monic_X_sub_C a).nextCoeff_mul hp, nextCoeff_X_sub_C]
    simp only [p, q, prod_X_sub_C_nextCoeff]
    dsimp only [a]
    ring
  have hdeg : (q - (X - C a) * p).degree < (Fintype.card (Fin n) : WithBot ℕ) := by
    simpa using degree_sub_lt_of_monic_nextCoeff_eq hq hbase hqn hbn hc
  have hpzero (j : Fin n) : p.eval (d j) = 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hpoly := polynomial_eq_base_sub_residue_sum d hd.injective q
    ((X - C a) * p) hdeg (fun j => by rw [eval_mul, hpzero, mul_zero])
  refine ⟨v, a, rfl, ?_⟩
  rw [charpoly_fromBlocks_diagonal_replicate]
  simp only [hv]
  exact hpoly.symm

/-- Any weakly interlacing target list above a strictly ordered original
list is the exact characteristic spectrum of a positive rank-one update.
Target repetitions and zero updates are allowed, including dimension zero.
Source: Horn--Johnson (2013), Section 4.3;
atlas: interlacing-converse (partial). -/
theorem exists_diagonal_add_vecMulVec_charpoly_of_strictMono
    {n : ℕ} (d b : Fin n → ℝ) (hd : StrictMono d) (hb : Monotone b)
    (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j : Fin n, i.val + 1 = j.val → b i ≤ d j) :
    ∃ v : Fin n → ℝ, (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
      ∏ j, (X - C (b j)) := by
  let p : ℝ[X] := ∏ i, (X - C (d i))
  let q : ℝ[X] := ∏ i, (X - C (b i))
  let w (j : Fin n) : ℝ := -q.eval (d j) /
    (∏ l ∈ Finset.univ.erase j, (d j - d l))
  have hw (j : Fin n) : 0 ≤ w j := by
    simpa [w, q, eval_prod] using
      neg_prod_sub_div_prod_erase_nonneg_of_rank_one_interlacing d b hd hb hlo hhi j
  let v (j : Fin n) : ℝ := Real.sqrt (w j)
  have hv (j : Fin n) : (v j) ^ 2 = w j := Real.sq_sqrt (hw j)
  have hp : p.Monic := monic_prod_X_sub_C _ _
  have hq : q.Monic := monic_prod_X_sub_C _ _
  have hpn : p.natDegree = n := by simp [p]
  have hqn : q.natDegree = n := by simp [q]
  have hdeg : (q - p).degree < (Fintype.card (Fin n) : WithBot ℕ) := by
    simpa using degree_sub_lt_of_monic_natDegree_eq hq hp hqn hpn
  have hpzero (j : Fin n) : p.eval (d j) = 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hpoly := polynomial_eq_base_sub_residue_sum d hd.injective q p hdeg hpzero
  refine ⟨v, ?_⟩
  rw [charpoly_diagonal_add_vecMulVec]
  simp only [hv]
  exact hpoly.symm

end NLAlib
