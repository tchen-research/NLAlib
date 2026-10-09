/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae,
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. Only the two used legacy
vocabulary definitions are supplied locally; there is no HighDimProb dependency.
-/
import NLAlib.Matrix.Norms
import NLAlib.Concentration.OrliczMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import NLAlib.Concentration.HansonWright.Geometry

/-!
# Hanson–Wright proof: CutAverages

A focused leaf of the transported independent-coordinate proof.
Shared helper declarations live in `NLAlib.HansonWrightProof`; the canonical
public bounds are in `NLAlib.Estimation.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib
namespace HansonWrightProof

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Source-transport helper `four_mul_card_powerset_filter_mem_notMem` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma four_mul_card_powerset_filter_mem_notMem {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    4 * (((Finset.univ : Finset (Fin n)).powerset.filter
      (fun s => i ∈ s ∧ j ∉ s)).card) =
      ((Finset.univ : Finset (Fin n)).powerset).card := by
  classical
  let T : Finset (Fin n) := ((Finset.univ : Finset (Fin n)).erase i).erase j
  have hcard_filter :
      (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun s => i ∈ s ∧ j ∉ s)).card) = T.powerset.card := by
    simpa [T] using card_powerset_filter_mem_notMem_eq (n := n) hij
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    rw [Finset.mem_erase]
    exact ⟨hij.symm, Finset.mem_univ j⟩
  have hT_card_add :
      T.card + 2 = (Finset.univ : Finset (Fin n)).card := by
    have h1 :
        ((Finset.univ : Finset (Fin n)).erase i).card + 1 =
          (Finset.univ : Finset (Fin n)).card :=
      Finset.card_erase_add_one (Finset.mem_univ i)
    have h2 :
        T.card + 1 = ((Finset.univ : Finset (Fin n)).erase i).card := by
      dsimp [T]
      exact Finset.card_erase_add_one hj_mem
    omega
  rw [hcard_filter, Finset.card_powerset, Finset.card_powerset]
  rw [← hT_card_add]
  rw [Nat.pow_add]
  norm_num
  rw [Nat.mul_comm]

/-- Source-transport helper `sum_powerset_cut_indicator` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma sum_powerset_cut_indicator {n : ℕ} (i j : Fin n) (a : ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (if i ∈ s ∧ j ∉ s then a else 0)) =
      (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun s => i ∈ s ∧ j ∉ s)).card : ℝ) * a := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- Source-transport helper `four_mul_sum_cut_quadraticForm_eq_card_mul_offDiagonal` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma four_mul_sum_cut_quadraticForm_eq_card_mul_offDiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    4 * (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      matrixQuadraticForm (cutMatrix A s) x) =
      (((Finset.univ : Finset (Fin n)).powerset).card : ℝ) *
        matrixQuadraticForm (offDiagonalMatrix A) x := by
  classical
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  have hpair : ∀ i j : Fin n,
      4 * (∑ s ∈ P, (if i ∈ s ∧ j ∉ s then A i j * x i * x j else 0)) =
        (P.card : ℝ) * ((if i = j then 0 else A i j) * x i * x j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [P]
    · have hsum :=
        sum_powerset_cut_indicator (n := n) i j (A i j * x i * x j)
      have hcount_nat :
          4 * ((P.filter (fun s => i ∈ s ∧ j ∉ s)).card) = P.card := by
        simpa [P] using four_mul_card_powerset_filter_mem_notMem (n := n) hij
      have hcount_real :
          (4 : ℝ) * ((P.filter (fun s => i ∈ s ∧ j ∉ s)).card : ℝ) =
            (P.card : ℝ) := by
        exact_mod_cast hcount_nat
      calc
        4 * (∑ s ∈ P, (if i ∈ s ∧ j ∉ s then A i j * x i * x j else 0))
            = 4 * (((P.filter (fun s => i ∈ s ∧ j ∉ s)).card : ℝ) *
                (A i j * x i * x j)) := by
                rw [hsum]
        _ = ((4 : ℝ) * ((P.filter (fun s => i ∈ s ∧ j ∉ s)).card : ℝ)) *
              (A i j * x i * x j) := by ring
        _ = (P.card : ℝ) * (A i j * x i * x j) := by rw [hcount_real]
        _ = (P.card : ℝ) * ((if i = j then 0 else A i j) * x i * x j) := by
              simp [hij]
  calc
    4 * (∑ s ∈ P, matrixQuadraticForm (cutMatrix A s) x)
        = 4 * (∑ i, ∑ j, ∑ s ∈ P,
            (if i ∈ s ∧ j ∉ s then A i j * x i * x j else 0)) := by
            congr 1
            unfold matrixQuadraticForm cutMatrix
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro s _
            by_cases hs : i ∈ s ∧ j ∉ s
            · rw [if_pos hs, if_pos hs]
              ring
            · rw [if_neg hs, if_neg hs]
              ring
    _ = ∑ i, ∑ j,
          4 * (∑ s ∈ P, (if i ∈ s ∧ j ∉ s then A i j * x i * x j else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ j,
          (P.card : ℝ) * ((if i = j then 0 else A i j) * x i * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hpair i j
    _ = (P.card : ℝ) * matrixQuadraticForm (offDiagonalMatrix A) x := by
            unfold matrixQuadraticForm offDiagonalMatrix
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Source-transport helper `quadraticForm_offDiagonal_eq_average_cut` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma quadraticForm_offDiagonal_eq_average_cut {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    matrixQuadraticForm (offDiagonalMatrix A) x =
      (4 / (((Finset.univ : Finset (Fin n)).powerset).card : ℝ)) *
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          matrixQuadraticForm (cutMatrix A s) x := by
  classical
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  have hP_pos : 0 < (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨∅, Finset.empty_mem_powerset _⟩
  have hmul := four_mul_sum_cut_quadraticForm_eq_card_mul_offDiagonal A x
  change matrixQuadraticForm (offDiagonalMatrix A) x =
    (4 / (P.card : ℝ)) * ∑ s ∈ P, matrixQuadraticForm (cutMatrix A s) x
  calc
    matrixQuadraticForm (offDiagonalMatrix A) x
        = (P.card : ℝ)⁻¹ * ((P.card : ℝ) *
            matrixQuadraticForm (offDiagonalMatrix A) x) := by
            field_simp [ne_of_gt hP_pos]
    _ = (P.card : ℝ)⁻¹ *
          (4 * ∑ s ∈ P, matrixQuadraticForm (cutMatrix A s) x) := by
            rw [← hmul]
    _ = (4 / (P.card : ℝ)) * ∑ s ∈ P, matrixQuadraticForm (cutMatrix A s) x := by
            field_simp [ne_of_gt hP_pos]

/-- Source-transport helper `exp_mul_quadraticForm_offDiagonal_le_average_cut` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma exp_mul_quadraticForm_offDiagonal_le_average_cut {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (l : ℝ) :
    exp (l * matrixQuadraticForm (offDiagonalMatrix A) x) ≤
      (((Finset.univ : Finset (Fin n)).powerset).card : ℝ)⁻¹ *
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          exp (4 * l * matrixQuadraticForm (cutMatrix A s) x) := by
  classical
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  let w : Finset (Fin n) → ℝ := fun _ => (P.card : ℝ)⁻¹
  let p : Finset (Fin n) → ℝ := fun s => 4 * l * matrixQuadraticForm (cutMatrix A s) x
  have hP_pos : 0 < (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨∅, Finset.empty_mem_powerset _⟩
  have hw_nonneg : ∀ s ∈ P, 0 ≤ w s := by
    intro s hs
    dsimp [w]
    exact inv_nonneg.mpr hP_pos.le
  have hw_sum : ∑ s ∈ P, w s = 1 := by
    simp [w]
    field_simp [ne_of_gt hP_pos]
  have hp_mem : ∀ s ∈ P, p s ∈ (Set.univ : Set ℝ) := by
    simp
  have hconv := convexOn_exp.map_sum_le (s := Set.univ) (t := P)
    (w := w) (p := p) hw_nonneg hw_sum hp_mem
  have harg :
      (∑ s ∈ P, w s • p s) =
        l * matrixQuadraticForm (offDiagonalMatrix A) x := by
    rw [quadraticForm_offDiagonal_eq_average_cut A x]
    dsimp only [w, p]
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    field_simp [ne_of_gt hP_pos]
    ring
  have hrhs :
      (∑ s ∈ P, w s • exp (p s)) =
        (P.card : ℝ)⁻¹ * ∑ s ∈ P,
          exp (4 * l * matrixQuadraticForm (cutMatrix A s) x) := by
    simp [w, p, smul_eq_mul, Finset.mul_sum]
  rw [harg, hrhs] at hconv
  simpa [P] using hconv

/-- Source-transport helper `quadraticForm_eq_inner_toEuclideanCLM` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma quadraticForm_eq_inner_toEuclideanCLM {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    matrixQuadraticForm A x =
      inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x)) (WithLp.toLp 2 x) := by
  unfold matrixQuadraticForm
  rw [Matrix.toEuclideanCLM_toLp, PiLp.inner_apply]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [show inner ℝ (∑ j : Fin n, A i j * x j) (x i) =
      (∑ j : Fin n, A i j * x j) * x i by
        exact real_inner_mul _ _]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Source-transport helper `sum_diag_sq_le_frobeniusNormSq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma sum_diag_sq_le_frobeniusNormSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, A i i ^ 2) ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  exact Finset.sum_le_sum fun i _ => by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)

/-- Source-transport helper `sum_diag_sq_le_frobeniusNorm_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma sum_diag_sq_le_frobeniusNorm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, A i i ^ 2) ≤ deterministicFrobeniusNorm A ^ 2 := by
  rw [frobeniusNorm_sq]
  exact sum_diag_sq_le_frobeniusNormSq A

/-- Source-transport helper `abs_diag_le_operatorNorm` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma abs_diag_le_operatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    |A i i| ≤ deterministicOperatorNorm A := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have hcoord :
      |A i i| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A e‖ := by
    have h :=
      PiLp.norm_apply_le
        (x := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A e) i
    simpa [e, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one, Real.norm_eq_abs]
      using h
  have hop :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).le_opNorm e
  have he_norm : ‖e‖ = 1 := by
    simp [e]
  calc
    |A i i| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A e‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ * ‖e‖ := hop
    _ = deterministicOperatorNorm A := by
      rw [he_norm, mul_one]
      rfl

/-- Source-transport helper `abs_quadraticForm_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma abs_quadraticForm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x : Fin n → ℝ} {K : ℝ} (hK : 0 ≤ K) (hx : ∀ i, |x i| ≤ K) :
    |matrixQuadraticForm A x| ≤ K ^ 2 * entrywiseL1Norm A := by
  unfold matrixQuadraticForm entrywiseL1Norm
  calc |∑ i, ∑ j, x i * A i j * x j|
      ≤ ∑ i, |∑ j, x i * A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * x j| := by
        exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| * K ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc |x i * A i j * x j|
            = |x i| * |A i j| * |x j| := by rw [abs_mul, abs_mul]
          _ ≤ |A i j| * K * K := by
              have hprod : |x i| * |x j| ≤ K * K :=
                mul_le_mul (hx i) (hx j) (abs_nonneg _) hK
              calc |x i| * |A i j| * |x j|
                  = |A i j| * (|x i| * |x j|) := by ring
                _ ≤ |A i j| * (K * K) :=
                    mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
                _ = |A i j| * K * K := by ring
          _ = |A i j| * K ^ 2 := by ring
    _ = K ^ 2 * ∑ i, ∑ j, |A i j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Source-transport helper `randomQuadraticForm_aemeasurable` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma randomQuadraticForm_aemeasurable {μ : Measure Ω} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (randomQuadraticForm A X) μ := by
  unfold randomQuadraticForm matrixQuadraticForm
  exact Finset.aemeasurable_fun_sum _ fun i _ =>
    Finset.aemeasurable_fun_sum _ fun j _ =>
      (((hX_meas i).mul (hX_meas j)).const_mul (A i j)).congr
        (ae_of_all _ fun ω => by
          change A i j * (X i ω * X j ω) = X i ω * A i j * X j ω
          ring)

/-- Source-transport helper `randomQuadraticForm_mem_Icc_of_ae_coord_bound` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma randomQuadraticForm_mem_Icc_of_ae_coord_bound {μ : Measure Ω} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {X : Fin n → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hX_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K) :
    ∀ᵐ ω ∂μ, randomQuadraticForm A X ω ∈
      Set.Icc (-(K ^ 2 * entrywiseL1Norm A)) (K ^ 2 * entrywiseL1Norm A) := by
  rw [← ae_all_iff] at hX_bound
  filter_upwards [hX_bound] with ω hω
  have h_abs := abs_quadraticForm_le A hK (fun i => hω i)
  exact abs_le.mp h_abs

/-- Source-transport helper `bounded_hansonWright_cgf_constant_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma bounded_hansonWright_cgf_constant_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {K C : ℝ}
    (hC_bound : 2 * entrywiseL1Norm A ^ 2 ≤ C * deterministicFrobeniusNorm A ^ 2) (l : ℝ) :
    2 * (K ^ 2 * entrywiseL1Norm A) ^ 2 * l ^ 2 ≤
      C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by
  have hmul : 0 ≤ K ^ 4 * l ^ 2 := by positivity
  calc 2 * (K ^ 2 * entrywiseL1Norm A) ^ 2 * l ^ 2
      = (2 * entrywiseL1Norm A ^ 2) * (K ^ 4 * l ^ 2) := by ring
    _ ≤ (C * deterministicFrobeniusNorm A ^ 2) * (K ^ 4 * l ^ 2) := by
        exact mul_le_mul_of_nonneg_right hC_bound hmul
    _ = C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by ring

/-- The local quadratic CGF estimate used in the Hanson-Wright proof.

For `Y = Xᵀ A X - E Xᵀ A X`, this records
`cgf Y λ ≤ C λ² K⁴ ‖A‖_F²` for
`|λ| ≤ (2 C K² ‖A‖)⁻¹`, together with local exponential integrability. -/
def HasHansonWrightMGF {n : ℕ} (μ : Measure Ω) (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (K C : ℝ) : Prop :=
  (∀ l : ℝ, |l| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ →
    cgf (centeredQuadraticForm μ A X) μ l ≤
      C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2) ∧
  ∀ l : ℝ, |l| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ →
    Integrable (fun ω => exp (l * centeredQuadraticForm μ A X ω)) μ

/-- Convexity of `exp` gives the chord bound on a compact interval. -/
lemma exp_le_chord {R t x : ℝ} (hR : 0 < R) (hx : x ∈ Set.Icc (-R) R) :
    exp (t * x) ≤ ((R - x) / (2 * R)) * exp (t * (-R)) +
      ((x + R) / (2 * R)) * exp (t * R) := by
  let w : Fin 2 → ℝ :=
    fun i => if i = 0 then (R - x) / (2 * R) else (x + R) / (2 * R)
  let p : Fin 2 → ℝ := fun i => if i = 0 then t * (-R) else t * R
  have hden : 0 < 2 * R := by positivity
  have hw0 : 0 ≤ (R - x) / (2 * R) :=
    div_nonneg (sub_nonneg.mpr hx.2) hden.le
  have hw1 : 0 ≤ (x + R) / (2 * R) := by
    refine div_nonneg ?_ hden.le
    linarith [hx.1]
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · simpa [w] using hw0
    · simpa [w] using hw1
  have hw_sum : ∑ i : Fin 2, w i = 1 := by
    simp [w]
    field_simp [hR.ne']
    ring
  have hp_mem : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ∈ (Set.univ : Set ℝ) := by
    simp
  have hconv := convexOn_exp.map_sum_le (s := Set.univ) (t := Finset.univ)
    (w := w) (p := p) hw_nonneg hw_sum hp_mem
  have harg : (∑ i : Fin 2, w i • p i) = t * x := by
    simp [w, p]
    field_simp [hR.ne']
    ring
  have hrhs : (∑ i : Fin 2, w i • exp (p i)) =
      ((R - x) / (2 * R)) * exp (t * (-R)) +
        ((x + R) / (2 * R)) * exp (t * R) := by
    simp [w, p]
  rw [harg, hrhs] at hconv
  simpa [smul_eq_mul] using hconv

end HansonWrightProof
end NLAlib
