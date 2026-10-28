import NLAlib.Estimation.Reconstruction.ChebyshevProbeBudget
import NLAlib.Estimation.Trace.HutchinsonTail
import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Spectral.HermitianExtremaNorm

/-!
# Native Rademacher concentration for Chebyshev moment estimates

The estimates use actual Rademacher vector laws. Different degrees may share
their probes: the final weighted-error estimate uses only a finite union bound.
Source: Musco--Musco--Rosenblatt--Singh, Section 5, Lemma 18 and Theorem 19;
the explicit constant comes from the library's proved Hanson--Wright bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix
namespace NLAlib

variable {n κ Ω : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A contraction has Frobenius square at most its ambient dimension. -/
private theorem frobNorm_sq_le_card_of_specNorm_le_one (A : Matrix n n ℝ)
    (hA : specNorm A ≤ 1) : frobNorm A ^ 2 ≤ Fintype.card n := by
  rw [frobNorm_sq]
  apply (frobSq_le_rank_mul_specNorm_sq A).trans
  have hr : (A.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast Matrix.rank_le_card_width A
  calc
    _ ≤ (A.rank : ℝ) * 1 := by
      gcongr
      simpa using (sq_le_sq₀ (specNorm_nonneg _) (by norm_num)).2 hA
    _ ≤ _ := by simpa using hr

/-- The polynomial spectral bound supplies the contraction needed in each
moment estimate; a norm bound on a nonsymmetric matrix would not suffice. -/
private theorem specNorm_aeval_chebyshev_le_one {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hbound : specNorm A ≤ 1) (j : ℕ) :
    specNorm (aeval A (Chebyshev.T ℝ (j : ℤ))) ≤ 1 := by
  apply specNorm_aeval_le hA _ zero_le_one
  intro i
  apply Chebyshev.abs_eval_T_real_le_one
  calc
    |hA.eigenvalues i| = ‖hA.eigenvalues i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖hA.eigenvalues‖ := norm_le_pi_norm _ _
    _ = specNorm A := hA.specNorm_eq_norm_eigenvalues.symm
    _ ≤ 1 := hbound

open scoped Matrix.Norms.L2Operator in
/-- A normalized trace of a contraction has the dimension-enhanced
Rademacher tail, including the zero matrix. -/
theorem measureReal_abs_hutchinsonEstimate_div_card_sub_trace_div_card_gt_le
    [Nonempty n] [Nonempty κ] (A : Matrix n n ℝ) (hA : specNorm A ≤ 1)
    {Z : Ω → Matrix n κ ℝ}
    (hZ : HasLaw (fun ω (e : n × κ) => Z ω e.1 e.2) (rademacherVector (n × κ)) μ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    μ.real {ω | a < |hutchinsonEstimate A (Z ω) / Fintype.card n -
      A.trace / Fintype.card n|} ≤
      2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
        (Fintype.card κ * Fintype.card n * a ^ 2)) := by
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hzero : A = 0
  · have he : {ω | a < |hutchinsonEstimate A (Z ω) / Fintype.card n -
        A.trace / Fintype.card n|} = ∅ := by
      ext ω
      simp [hzero, hutchinsonEstimate, quadForm, ha.not_gt]
    rw [he, measureReal_empty]
    positivity
  have hS : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne
    (fun h => hzero (norm_eq_zero.mp ((specNorm_eq_norm A).symm.trans h.symm)))
  have hF : 0 < frobNorm A ^ 2 := sq_pos_of_ne_zero
    (fun h => hzero ((frobNorm_eq_zero_iff A).mp h))
  have hFbound := frobNorm_sq_le_card_of_specNorm_le_one A hA
  have hexp : (Fintype.card κ : ℝ) * Fintype.card n * a ^ 2 ≤
      min (Fintype.card κ * ((Fintype.card n : ℝ) * a) ^ 2 / frobNorm A ^ 2)
        (Fintype.card κ * ((Fintype.card n : ℝ) * a) / specNorm A) := by
    apply le_min
    · apply (le_div_iff₀ hF).2
      calc
        _ ≤ (Fintype.card κ : ℝ) * Fintype.card n * a ^ 2 * Fintype.card n := by gcongr
        _ = _ := by ring
    · apply (le_div_iff₀ hS).2
      calc
        _ ≤ (Fintype.card κ : ℝ) * Fintype.card n * a ^ 2 * 1 := by gcongr
        _ ≤ _ := by
          have : a ^ 2 ≤ a := by nlinarith
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ Fintype.card κ * Fintype.card n by positivity)
            (sub_nonneg.mpr this)]
  calc
    _ ≤ μ.real {ω | (Fintype.card n : ℝ) * a ≤ |hutchinsonEstimate A (Z ω) - A.trace|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq, ← sub_div, abs_div, abs_of_pos hn] at hω ⊢
      exact (mul_comm _ _).trans_le ((lt_div_iff₀ hn).mp hω).le
    _ ≤ _ := (measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_rademacherVector
      A hZ _ (by positivity)).trans (by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hexp (neg_nonpos.mpr (by positivity)))

omit [DecidableEq n] [Fintype κ] [DecidableEq κ] [IsProbabilityMeasure μ] in
/-- Selecting a prefix from one Rademacher array preserves its joint law. -/
private theorem hasLaw_rademacherVector_prefix {L q : ℕ} (hq : q ≤ L)
    {G : Ω → Matrix n (Fin L) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin L) => G ω e.1 e.2)
      (rademacherVector (n × Fin L)) μ) :
    HasLaw (fun ω (e : n × Fin q) => G ω e.1 (e.2.castLE hq))
      (rademacherVector (n × Fin q)) μ := by
  apply hasLaw_rademacherVector_of_iIndepFun
    (x := fun (e : n × Fin q) ω => G ω e.1 (e.2.castLE hq))
    (fun e => hG.hasLaw_eval_rademacherMeasure (e.1, e.2.castLE hq))
  exact hG.iIndepFun_eval_of_rademacherVector.precomp
    (g := fun e : n × Fin q => (e.1, e.2.castLE hq)) (by
      intro a b he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg (fun e : n × Fin L => e.2.val) he
      exact Prod.ext h₁ (Fin.ext h₂))

omit [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The degree-`j` estimate uses the first prescribed number of columns from
one common probe array. Degree zero is the exact mass. -/
def chebyshevTraceMomentEstimate (A : Matrix n n ℝ) (a : ℝ) (ha : 0 ≤ a)
    (G : Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (j : ℕ) : ℝ :=
  if hj : 1 ≤ j then
    hutchinsonEstimate (aeval A (Chebyshev.T ℝ (j : ℤ)))
      (fun i (t : Fin (chebyshevProbeCount a j)) => G i (t.castLE
        (chebyshevProbeCount_antitone ha (by simp) hj hj))) / Fintype.card n
  else 1

omit [Fintype κ] [DecidableEq κ] in
/-- The prescribed decreasing count gives the failure budget `delta / k`
for each Chebyshev moment, with all moments drawn from the same probe array. -/
theorem measureReal_abs_chebyshevTraceMomentEstimate_sub_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (hbound : specNorm A ≤ 1)
    {k j : ℕ} (hk : 2 ≤ k) (hj : j ∈ Finset.Icc 1 k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) =>
      G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1))) μ) :
    μ.real {ω | Real.sqrt j * chebyshevProbeAccuracy k <
      |chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
        (chebyshevProbeBudget_nonneg _ _ _) (G ω) j -
        (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n|} ≤ δ / k := by
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjk := (Finset.mem_Icc.mp hj).2
  have ha := chebyshevProbeBudget_nonneg (Fintype.card n) k δ
  let a := chebyshevProbeBudget (Fintype.card n) k δ
  have : Nonempty (Fin (chebyshevProbeCount a j)) :=
    Fin.pos_iff_nonempty.mp (chebyshevProbeCount_pos ha j)
  have hprefix := hasLaw_rademacherVector_prefix
    (chebyshevProbeCount_antitone ha (by simp) hj1 hj1) hG
  have ht : 0 < Real.sqrt j * chebyshevProbeAccuracy k := mul_pos
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))) (chebyshevProbeAccuracy_pos (by omega))
  have htail := measureReal_abs_hutchinsonEstimate_div_card_sub_trace_div_card_gt_le
    (Z := fun ω i (t : Fin (chebyshevProbeCount a j)) => G ω i
      (t.castLE (chebyshevProbeCount_antitone ha (by simp) hj1 hj1)))
    (aeval A (Chebyshev.T ℝ (j : ℤ))) (specNorm_aeval_chebyshev_le_one hA hbound j)
    hprefix ht (sqrt_mul_chebyshevProbeAccuracy_le_one (by omega) hjk)
  simp only [chebyshevTraceMomentEstimate, dif_pos hj1]
  refine htail.trans ?_
  simpa only [Fintype.card_fin] using
    exp_neg_probeCount_mul_le_div Fintype.card_pos hk (by omega) hδ hδ1

omit [Fintype κ] [DecidableEq κ] in
/-- The actual shared-probe estimator achieves weighted moment error `1/k`
except on an event of probability at most `delta`. -/
theorem measureReal_weightedChebyshevError_traceMomentEstimate_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (hbound : specNorm A ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) =>
      G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1))) μ) :
    μ.real {ω | 1 / (k : ℝ) < weightedChebyshevError k
      (chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
        (chebyshevProbeBudget_nonneg _ _ _) (G ω))
      (fun j => (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n)} ≤ δ := by
  let E : ℕ → Set Ω := fun j => {ω | Real.sqrt j * chebyshevProbeAccuracy k <
      |chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
        (chebyshevProbeBudget_nonneg _ _ _) (G ω) j -
        (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n|}
  calc
    _ ≤ μ.real (⋃ j ∈ Finset.Icc 1 k, E j) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      by_contra hnot
      have hcoord : ∀ j ∈ Finset.Icc 1 k,
          |chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
            (chebyshevProbeBudget_nonneg _ _ _) (G ω) j -
            (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n| ≤
              Real.sqrt j * chebyshevProbeAccuracy k := by
        intro j hj
        exact le_of_not_gt fun hgt => hnot (Set.mem_biUnion hj hgt)
      exact (not_lt_of_ge (weightedChebyshevError_le_inv_of_coordinate_error (by omega) _ _ hcoord)) hω
    _ ≤ ∑ j ∈ Finset.Icc 1 k, μ.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 k, δ / k := by
      apply Finset.sum_le_sum
      intro j hj
      exact measureReal_abs_chebyshevTraceMomentEstimate_sub_gt_le hA hbound hk hj hδ hδ1 hG
    _ = δ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp

end NLAlib
