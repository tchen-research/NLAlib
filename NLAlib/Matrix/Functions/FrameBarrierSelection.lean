import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Functions.ReciprocalBarrier

/-!
# Frame barrier candidate selection

This file proves the single candidate-selection step used by the deterministic
rank-one sparsification argument of Batson--Spielman--Srivastava: given a
finite isotropic frame `∑ i, v_i v_iᵀ = 1`, two positive definite barriers
`MU`, `ML` and shifts `δU`, `δL > 0` satisfying the strict lower potential
cap `δL * tr(ML⁻¹) < 1` and compatibility
`1/δU + tr(MU⁻¹) ≤ 1/δL - tr(ML⁻¹)`, one of the frame vectors has an upper
barrier score `U_i` and a lower barrier score `L_i` satisfying `0 < U_i ≤ L_i`.
The ambient index type is nonempty. The score-sum comparison is derived from the actual matrix
trace identity and the matrix reciprocal-barrier inequalities of
`NLAlib.Matrix.Functions.ReciprocalBarrier`; no score hypotheses are assumed.

The definitions use total matrix inverses and real division. Their positivity
properties require the stated hypotheses. This file provides candidate selection
and a positive reciprocal step size; it does not yet prove preservation of the
potentials after a rank-one update or the finite sparsification iteration.

Source: Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers* (2008),
Section 3.2 ([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)).
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix BigOperators

namespace NLAlib

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- Actual trace identity for an isotropic frame: for every real matrix
`R : Matrix n n ℝ`, `∑ i, v_i ⬝ᵥ R *ᵥ v_i = trace R`. -/
private theorem sum_dot_mulVec_eq_trace_of_frame (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (R : Matrix n n ℝ) :
    ∑ i, (v i ⬝ᵥ R.mulVec (v i)) = R.trace := by
  have hstep (i : I) : v i ⬝ᵥ R.mulVec (v i) =
      (R * Matrix.vecMulVec (v i) (v i)).trace := by
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  calc
    ∑ i, (v i ⬝ᵥ R.mulVec (v i)) =
        ∑ i, (R * Matrix.vecMulVec (v i) (v i)).trace := by
      exact Finset.sum_congr rfl (fun i _ => hstep i)
    _ = (R * ∑ i, Matrix.vecMulVec (v i) (v i)).trace := by
      rw [Finset.mul_sum, Matrix.trace_sum]
    _ = R.trace := by
      rw [hframe, Matrix.mul_one]

/-- Sum of quadratic forms under an isotropic frame equals the trace. -/
theorem sum_quadForm_eq_trace_of_frame (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (A : Matrix n n ℝ) :
    ∑ i, quadForm A (v i) = A.trace := by
  simpa [quadForm_def, star_trivial] using
    sum_dot_mulVec_eq_trace_of_frame v hframe A

/-- An isotropic frame over a nonempty space contains a nonzero vector. -/
private theorem exists_ne_zero_of_frame [Nonempty n] (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1) :
    ∃ i, v i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨j⟩ := ‹Nonempty n›
  have hsum : (∑ i, Matrix.vecMulVec (v i) (v i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [h i]
  have hjj : (0 : ℝ) = 1 := by
    simpa [hsum] using congrArg (fun M : Matrix n n ℝ => M j j) hframe
  norm_num at hjj

namespace RankOneBarrier

/-- The shifted-and-inverted upper barrier matrix `(MU + δ•1)⁻¹`. -/
def upperMatrix (MU : Matrix n n ℝ) (δ : ℝ) : Matrix n n ℝ :=
  (MU + δ • (1 : Matrix n n ℝ))⁻¹

/-- The upper reciprocal-barrier gap
`tr(MU⁻¹) - tr((MU + δ•1)⁻¹)`. -/
def upperGap (MU : Matrix n n ℝ) (δ : ℝ) : ℝ :=
  MU⁻¹.trace - (upperMatrix MU δ).trace

/-- The shifted-and-inverted lower barrier matrix `(ML - δ•1)⁻¹`. -/
def lowerMatrix (ML : Matrix n n ℝ) (δ : ℝ) : Matrix n n ℝ :=
  (ML - δ • (1 : Matrix n n ℝ))⁻¹

/-- The lower reciprocal-barrier gap
`tr((ML - δ•1)⁻¹) - tr(ML⁻¹)`. -/
def lowerGap (ML : Matrix n n ℝ) (δ : ℝ) : ℝ :=
  (lowerMatrix ML δ).trace - ML⁻¹.trace

/-- The upper candidate score `quadForm (RU²) v / DU + quadForm RU v`. -/
def upperScore (RU : Matrix n n ℝ) (DU : ℝ) (v : n → ℝ) : ℝ :=
  quadForm (RU ^ 2) v / DU + quadForm RU v

/-- The lower candidate score `quadForm (RL²) v / DL - quadForm RL v`. -/
def lowerScore (RL : Matrix n n ℝ) (DL : ℝ) (v : n → ℝ) : ℝ :=
  quadForm (RL ^ 2) v / DL - quadForm RL v

/-- The upper shifted matrix is positive definite. -/
theorem upperMatrix_posDef (MU : Matrix n n ℝ) (hMU : MU.PosDef)
    {δ : ℝ} (hδ : 0 < δ) : (upperMatrix MU δ).PosDef := by
  unfold upperMatrix
  exact (hMU.add_smul_one_posDef hδ).inv

/-- The lower shifted matrix is positive definite under the strict potential
cap `δ * tr(ML⁻¹) < 1`. -/
theorem lowerMatrix_posDef (ML : Matrix n n ℝ) (hML : ML.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * ML⁻¹.trace < 1) :
    (lowerMatrix ML δ).PosDef := by
  unfold lowerMatrix
  exact (hML.sub_smul_one_posDef_of_mul_trace_inv_lt_one hδ hcap).inv

/-- The upper reciprocal-barrier gap is positive on a nonempty index type. -/
theorem upperGap_pos [Nonempty n] (MU : Matrix n n ℝ) (hMU : MU.PosDef)
    {δ : ℝ} (hδ : 0 < δ) : 0 < upperGap MU δ := by
  unfold upperGap upperMatrix
  exact hMU.trace_inv_sub_trace_add_smul_one_inv_pos hδ

/-- The lower reciprocal-barrier gap is positive under the strict potential
cap on a nonempty index type. -/
theorem lowerGap_pos [Nonempty n] (ML : Matrix n n ℝ) (hML : ML.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * ML⁻¹.trace < 1) :
    0 < lowerGap ML δ := by
  unfold lowerGap lowerMatrix
  exact hML.trace_sub_smul_one_inv_sub_trace_inv_pos hδ hcap

/-- The upper candidate score is positive at a nonzero vector. -/
theorem upperScore_pos_of_ne_zero {RU : Matrix n n ℝ} (hRU : RU.PosDef)
    {DU : ℝ} (hDU : 0 < DU) {v : n → ℝ} (hv : v ≠ 0) :
    0 < upperScore RU DU v := by
  unfold upperScore
  have hq2 : 0 ≤ quadForm (RU ^ 2) v :=
    (hRU.posSemidef.pow 2).quadForm_nonneg v
  have hq1 : 0 < quadForm RU v := hRU.quadForm_pos hv
  have hdiv : 0 ≤ quadForm (RU ^ 2) v / DU := div_nonneg hq2 hDU.le
  linarith

/-- The upper candidate score of the zero vector is zero, for every gap. -/
@[simp] theorem upperScore_zero (RU : Matrix n n ℝ) (DU : ℝ) :
    upperScore RU DU 0 = 0 := by
  simp [upperScore]

/-- The lower candidate score of the zero vector is zero, for every gap. -/
@[simp] theorem lowerScore_zero (RL : Matrix n n ℝ) (DL : ℝ) :
    lowerScore RL DL 0 = 0 := by
  simp [lowerScore]

/-- Sum of the upper candidate scores over an isotropic frame. -/
theorem sum_upperScore_eq (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (RU : Matrix n n ℝ) (DU : ℝ) :
    ∑ i, upperScore RU DU (v i) =
      (RU ^ 2).trace / DU + RU.trace := by
  unfold upperScore
  calc
    ∑ i, (quadForm (RU ^ 2) (v i) / DU + quadForm RU (v i))
        = (∑ i, quadForm (RU ^ 2) (v i)) / DU +
            ∑ i, quadForm RU (v i) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = (RU ^ 2).trace / DU + RU.trace := by
          rw [sum_quadForm_eq_trace_of_frame v hframe (RU ^ 2),
            sum_quadForm_eq_trace_of_frame v hframe RU]

/-- Sum of the lower candidate scores over an isotropic frame. -/
theorem sum_lowerScore_eq (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (RL : Matrix n n ℝ) (DL : ℝ) :
    ∑ i, lowerScore RL DL (v i) =
      (RL ^ 2).trace / DL - RL.trace := by
  unfold lowerScore
  calc
    ∑ i, (quadForm (RL ^ 2) (v i) / DL - quadForm RL (v i))
        = (∑ i, quadForm (RL ^ 2) (v i)) / DL -
            ∑ i, quadForm RL (v i) := by
          rw [Finset.sum_sub_distrib]
          congr 1
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = (RL ^ 2).trace / DL - RL.trace := by
          rw [sum_quadForm_eq_trace_of_frame v hframe (RL ^ 2),
            sum_quadForm_eq_trace_of_frame v hframe RL]

/-- **Candidate selection.** For an isotropic frame and two positive definite
barriers with shifts satisfying the reciprocal-potential and potential cap
hypotheses, some nonzero frame vector has upper score positive and no larger
than its lower score. -/
theorem exists_candidate [Nonempty n] (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (MU : Matrix n n ℝ) (hMU : MU.PosDef)
    (ML : Matrix n n ℝ) (hML : ML.PosDef)
    (δU δL : ℝ) (hδU : 0 < δU) (hδL : 0 < δL)
    (hcap : δL * ML⁻¹.trace < 1)
    (hpot : 1 / δU + MU⁻¹.trace ≤ 1 / δL - ML⁻¹.trace) :
    ∃ i, v i ≠ 0 ∧
      0 < upperScore (upperMatrix MU δU) (upperGap MU δU) (v i) ∧
      upperScore (upperMatrix MU δU) (upperGap MU δU) (v i) ≤
        lowerScore (lowerMatrix ML δL) (lowerGap ML δL) (v i) := by
  classical
  set RU : Matrix n n ℝ := upperMatrix MU δU with hRUdef
  set RL : Matrix n n ℝ := lowerMatrix ML δL with hRLdef
  set DU : ℝ := upperGap MU δU with hDUdef
  set DL : ℝ := lowerGap ML δL with hDLdef
  have hRU : RU.PosDef := by
    rw [hRUdef]
    exact (hMU.add_smul_one_posDef hδU).inv
  have hDU : 0 < DU := by
    rw [hDUdef]
    exact hMU.trace_inv_sub_trace_add_smul_one_inv_pos hδU
  have hUbar : (RU ^ 2).trace / DU + RU.trace ≤
      1 / δU + MU⁻¹.trace := by
    rw [hRUdef, hDUdef]
    simpa [upperMatrix, upperGap] using hMU.reciprocal_barrier_upper_le hδU
  have hLbar : 1 / δL - ML⁻¹.trace ≤
      (RL ^ 2).trace / DL - RL.trace := by
    rw [hRLdef, hDLdef]
    simpa [lowerMatrix, lowerGap] using hML.reciprocal_barrier_lower_le hδL hcap
  have hsum_le :
      ∑ i, upperScore RU DU (v i) ≤ ∑ i, lowerScore RL DL (v i) := by
    calc
      ∑ i, upperScore RU DU (v i)
          = (RU ^ 2).trace / DU + RU.trace :=
            sum_upperScore_eq v hframe RU DU
      _ ≤ 1 / δU + MU⁻¹.trace := hUbar
      _ ≤ 1 / δL - ML⁻¹.trace := hpot
      _ ≤ (RL ^ 2).trace / DL - RL.trace := hLbar
      _ = ∑ i, lowerScore RL DL (v i) :=
            (sum_lowerScore_eq v hframe RL DL).symm
  obtain ⟨j, hj⟩ := exists_ne_zero_of_frame v hframe
  by_contra hbad
  have hgt : ∀ i, v i ≠ 0 →
      lowerScore RL DL (v i) < upperScore RU DU (v i) := by
    intro i hv
    have hpos : 0 < upperScore RU DU (v i) :=
      upperScore_pos_of_ne_zero hRU hDU hv
    have hnot : ¬ (0 < upperScore RU DU (v i) ∧
        upperScore RU DU (v i) ≤ lowerScore RL DL (v i)) := by
      intro h
      exact hbad ⟨i, hv, h⟩
    have hnotle : ¬ upperScore RU DU (v i) ≤ lowerScore RL DL (v i) := by
      intro hle
      exact hnot ⟨hpos, hle⟩
    exact lt_of_not_ge hnotle
  have hle : ∀ i ∈ (Finset.univ : Finset I),
      lowerScore RL DL (v i) ≤ upperScore RU DU (v i) := by
    intro i hi
    by_cases hv : v i = 0
    · simp [hv]
    · exact le_of_lt (hgt i hv)
  have hlt : ∃ i ∈ (Finset.univ : Finset I),
      lowerScore RL DL (v i) < upperScore RU DU (v i) :=
    ⟨j, Finset.mem_univ _, hgt j hj⟩
  have hsum_lt : (∑ i, lowerScore RL DL (v i)) <
      ∑ i, upperScore RU DU (v i) :=
    Finset.sum_lt_sum hle hlt
  exact (not_lt_of_ge hsum_le) hsum_lt

/-- **Candidate step.** Under the hypotheses of `exists_candidate` there is a
nonzero frame vector `v i` and a positive `t` with the upper score at most
`1 / t` and `1 / t` at most the lower score.  Taking `t = 1 / U_i` realises
the reciprocal bridging step used by the BSS rank-one potential update. -/
theorem exists_candidate_inverse [Nonempty n] (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (MU : Matrix n n ℝ) (hMU : MU.PosDef)
    (ML : Matrix n n ℝ) (hML : ML.PosDef)
    (δU δL : ℝ) (hδU : 0 < δU) (hδL : 0 < δL)
    (hcap : δL * ML⁻¹.trace < 1)
    (hpot : 1 / δU + MU⁻¹.trace ≤ 1 / δL - ML⁻¹.trace) :
    ∃ i, v i ≠ 0 ∧ ∃ t : ℝ, 0 < t ∧
      upperScore (upperMatrix MU δU) (upperGap MU δU) (v i) ≤ 1 / t ∧
      1 / t ≤ lowerScore (lowerMatrix ML δL) (lowerGap ML δL) (v i) := by
  obtain ⟨i, hvec, hpos, hle⟩ :=
    exists_candidate v hframe MU hMU ML hML δU δL hδU hδL hcap hpot
  let t : ℝ := (upperScore (upperMatrix MU δU) (upperGap MU δU) (v i))⁻¹
  have ht_pos : 0 < t := by
    unfold t
    exact inv_pos.mpr hpos
  have ht_eq : 1 / t =
      upperScore (upperMatrix MU δU) (upperGap MU δU) (v i) := by
    unfold t
    rw [one_div, inv_inv]
  refine ⟨i, hvec, t, ht_pos, ?_, ?_⟩
  · rw [ht_eq]
  · rw [ht_eq]
    exact hle

end RankOneBarrier

end NLAlib
