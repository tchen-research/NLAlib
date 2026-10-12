import NLAlib.Matrix.Perturbation.EigenvaluePencil
import NLAlib.Matrix.Inequalities.KyFanSums

/-!
# Subsequential first variation of signed eigenvalue sums

Compactness of real orthogonal eigenframes gives a subsequential first variation
at every symmetric matrix, without differentiable or measurable eigenvector
choices. The limiting frame's Ky Fan trace bound supplies the exact top-eigenvalue
constant. Source: `matrix_toolkit_remaining_operator_derivations.tex`,
Lemma (15), the operator route to Bhatia 1997, Theorem III.4.1. Supports `lidskii`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
open Filter Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An eigenframe sequence along any real symmetric pencil has a convergent
orthogonal subsequence. Finite unit-vector compactness; Lidskii variation step.
-/
theorem exists_subseq_eigenvectorUnitary_pencil_tendsto {C B : Matrix n n ℝ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (h : ℕ → ℝ) :
    ∃ U : Matrix n n ℝ, Uᵀ * U = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun ν => ((isHermitian_add_smul hC hB (h (φ ν))).eigenvectorUnitary :
        Matrix n n ℝ)) atTop (𝓝 U) := by
  let V : ℕ → Matrix n n ℝ := fun ν => (isHermitian_add_smul hC hB (h ν)).eigenvectorUnitary
  have hc := (isCompact_closedBall (0 : Matrix n n ℝ) 1).isSeqCompact
  have hm (ν : ℕ) : V ν ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact entrywise_sup_norm_bound_of_unitary
      (isHermitian_add_smul hC hB (h ν)).eigenvectorUnitary.property
  obtain ⟨U, _, φ, hφ, hlim⟩ := hc hm
  have hmul := (continuous_id.matrix_transpose.matrix_mul continuous_id).tendsto U |>.comp hlim
  have hmulone : Tendsto (fun ν => (V (φ ν))ᵀ * V (φ ν)) atTop (𝓝 (1 : Matrix n n ℝ)) := by
    have heq : (fun ν => (V (φ ν))ᵀ * V (φ ν)) = fun _ => (1 : Matrix n n ℝ) := by
      funext ν
      exact transpose_eigenvectorUnitary_mul_self (isHermitian_add_smul hC hB (h (φ ν)))
    rw [heq]
    exact tendsto_const_nhds
  refine ⟨U, tendsto_nhds_unique hmul hmulone, φ, hφ, ?_⟩
  exact hlim

omit [Fintype n] [DecidableEq n] in
private theorem continuous_col (j : n) : Continuous (fun U : Matrix n n ℝ => fun i => U i j) :=
  continuous_pi fun i => continuous_id.matrix_elem i j

private theorem col_dotProduct_self_eq_one {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (j : n) :
    (fun i => U i j) ⬝ᵥ (fun i => U i j) = 1 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, dotProduct] using
    congrArg (fun M => M j j) hU

private theorem eigenvalues₀_pencil_zero {C B : Matrix n n ℝ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    (isHermitian_add_smul hC hB 0).eigenvalues₀ i = hC.eigenvalues₀ i := by
  exact eigenvalues₀_eq_of_eq (by simp) _ hC i

set_option maxHeartbeats 2000000 in
/-- Any positive perturbation sequence tending to zero admits a subsequence of
the selected eigenvalue difference quotients converging to a value bounded by
the exact top-`|J|` eigenvalue sum of the perturbation. The compact-eigenframe
argument treats repeated and negative eigenvalues without extra hypotheses.
Source: manuscript Lemma (15), Bhatia 1997, Theorem III.4.1 proof route.
-/
theorem exists_subseq_eigenvalues₀_sum_difference_quotient_tendsto
    {C B : Matrix n n ℝ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (J : Finset (Fin (Fintype.card n))) (h : ℕ → ℝ) (hhpos : ∀ ν, 0 < h ν)
    (hh : Tendsto h atTop (𝓝 0)) :
    ∃ c : ℝ, c ≤ eigenvaluePrefix hB (k := J.card) (by simpa using Finset.card_le_univ J) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto
        (fun ν => ((∑ j ∈ J, (isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j) -
          ∑ j ∈ J, hC.eigenvalues₀ j) / h (φ ν)) atTop (𝓝 c) := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  obtain ⟨U, hU, φ, hφ, hframe⟩ := exists_subseq_eigenvectorUnitary_pencil_tendsto hC hB h
  have hhφ : Tendsto (fun ν => h (φ ν)) atTop (𝓝 0) := hh.comp hφ.tendsto_atTop
  let u (j : Fin (Fintype.card n)) : n → ℝ := fun i => U i (e j)
  let v (ν : ℕ) (j : Fin (Fintype.card n)) : n → ℝ :=
    fun i => (isHermitian_add_smul hC hB (h (φ ν))).eigenvectorUnitary i (e j)
  have hv (j : Fin (Fintype.card n)) : Tendsto (fun ν => v ν j) atTop (𝓝 (u j)) :=
    (continuous_col (e j)).tendsto U |>.comp hframe
  have hLambda (j : Fin (Fintype.card n)) : Tendsto
      (fun ν => (isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j)
      atTop (𝓝 (hC.eigenvalues₀ j)) := by
    have hl := (continuous_eigenvalues₀_pencil hC hB j).tendsto 0 |>.comp hhφ
    change Tendsto (fun ν => (isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j)
      atTop (𝓝 ((isHermitian_add_smul hC hB 0).eigenvalues₀ j)) at hl
    rw [eigenvalues₀_pencil_zero hC hB j] at hl
    exact hl
  have hvEig (ν : ℕ) (j : Fin (Fintype.card n)) :
      (C + h (φ ν) • B) *ᵥ v ν j =
        (isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j • v ν j := by
    simpa only [v, Matrix.IsHermitian.eigenvectorUnitary_apply,
      Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      (isHermitian_add_smul hC hB (h (φ ν))).mulVec_eigenvectorBasis (e j)
  have huEig (j : Fin (Fintype.card n)) : C *ᵥ u j = hC.eigenvalues₀ j • u j := by
    have hlhs : Tendsto (fun ν => (C + h (φ ν) • B) *ᵥ v ν j) atTop (𝓝 (C *ᵥ u j)) :=
      by
        apply tendsto_pi_nhds.mpr
        intro i
        change Tendsto (fun ν => ∑ k, (C i k + h (φ ν) * B i k) * v ν j k)
          atTop (𝓝 (∑ k, C i k * u j k))
        apply tendsto_finsetSum
        intro k _
        have hconst : Tendsto (fun _ : ℕ => C i k) atTop (𝓝 (C i k)) := tendsto_const_nhds
        have hentry : Tendsto (fun ν => C i k + h (φ ν) * B i k) atTop (𝓝 (C i k)) := by
          simpa only [zero_mul, add_zero] using hconst.add (hhφ.mul_const (B i k))
        exact hentry.mul (tendsto_pi_nhds.mp (hv j) k)
    have hrhs := (hLambda j).smul (hv j)
    have heq : (fun ν => (C + h (φ ν) • B) *ᵥ v ν j) =
        fun ν => (isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j • v ν j :=
      funext fun ν => hvEig ν j
    rw [heq] at hlhs
    exact tendsto_nhds_unique hlhs hrhs
  have hover (j : Fin (Fintype.card n)) : Tendsto (fun ν => u j ⬝ᵥ v ν j) atTop (𝓝 1) := by
    have hc : Continuous (fun x : n → ℝ => u j ⬝ᵥ x) := continuous_const.dotProduct continuous_id
    have hd := hc.tendsto (u j) |>.comp (hv j)
    simpa only [Function.comp_def, u, col_dotProduct_self_eq_one hU] using hd
  have hquot (j : Fin (Fintype.card n)) : Tendsto
      (fun ν => ((isHermitian_add_smul hC hB (h (φ ν))).eigenvalues₀ j - hC.eigenvalues₀ j) /
        h (φ ν)) atTop (𝓝 (quadForm B (u j))) := by
    have hnumerator : Tendsto (fun ν => u j ⬝ᵥ (B *ᵥ v ν j)) atTop
        (𝓝 (u j ⬝ᵥ (B *ᵥ u j))) := by
      have hc : Continuous (fun x : n → ℝ => u j ⬝ᵥ (B *ᵥ x)) :=
        continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)
      exact hc.tendsto (u j) |>.comp (hv j)
    have hdivision := hnumerator.div (hover j) one_ne_zero
    simp only [div_one] at hdivision
    apply hdivision.congr'
    filter_upwards [(hover j).eventually_ne one_ne_zero] with ν hne
    have hCtrans : Cᵀ = C := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.eq
    have hCsym : u j ⬝ᵥ (C *ᵥ v ν j) = hC.eigenvalues₀ j * (u j ⬝ᵥ v ν j) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCtrans,
        huEig j, smul_dotProduct, smul_eq_mul]
    have hEq := congrArg (fun x => u j ⬝ᵥ x) (hvEig ν j)
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, hCsym] at hEq
    apply (div_eq_div_iff hne (ne_of_gt (hhpos (φ ν)))).mpr
    nlinarith
  let Q : Matrix n J ℝ := U.submatrix id (fun j : J => e j)
  have hQ : HasOrthonormalCols Q :=
    HasOrthonormalCols.submatrix_cols hU
      ⟨fun j : J => e j, fun i j hij => Subtype.ext (e.injective hij)⟩
  let c : ℝ := ∑ j ∈ J, quadForm B (u j)
  have hc : c ≤ eigenvaluePrefix hB (k := J.card) (by simpa using Finset.card_le_univ J) := by
    have htrace : (Qᵀ * B * Q).trace = c := by
      calc
        _ = ∑ j : J, quadForm B (u j) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
            Q, Matrix.submatrix_apply, id_eq, quadForm, u, Matrix.mulVec, dotProduct,
            Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = c := Finset.sum_coe_sort J (fun j => quadForm B (u j))
    have hbound := trace_compression_le_eigenvaluePrefix hB hQ
    rw [htrace] at hbound
    have hcard : Fintype.card J = J.card := Fintype.card_coe J
    simpa only [hcard] using hbound
  refine ⟨c, hc, φ, hφ, ?_⟩
  have hsum := tendsto_finsetSum J (fun j _ => hquot j)
  simpa only [← Finset.sum_div, Finset.sum_sub_distrib, c] using hsum

end NLAlib
