import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Norms.Core
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Frobenius isotropy from actual right-unitary invariance

Invariance rotates an arbitrary unit direction into a fixed coordinate. Summing
the directional second moments gives the normalized Frobenius identity. No
covariance matrix is supplied as an assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {K r q p : Type*} [RCLike K] [MeasurableSpace K] [BorelSpace K]
  [Fintype r] [Fintype q] [Fintype p]
  [DecidableEq q]

/-- The actual matrix law is unchanged by every right-unitary multiplication. -/
def RightUnitaryInvariant (μ : Measure (Matrix r q K)) : Prop :=
  ∀ U : Matrix.unitaryGroup q K, μ.map (fun Z => Z*(U : Matrix q q K)) = μ

omit [MeasurableSpace K] [BorelSpace K] [DecidableEq q] in
private theorem norm_column_sq_le_frobSq (Z : Matrix r q K) (j : q) :
    ‖WithLp.toLp 2 (Z.col j)‖^2 ≤ frobSq Z := by
  rw [PiLp.norm_sq_eq_of_L2,frobSq_eq_sum_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖Z i k‖) (Finset.mem_univ j)

omit [DecidableEq q] in
/-- Finite Frobenius second moment gives integrable squared norms of all linear images. -/
theorem integrable_norm_mulVec_sq_of_integrable_frobSq
    (μ : Measure (Matrix r q K)) (hμ : Integrable (fun Z => frobSq Z) μ) (x : q → K) :
    Integrable (fun Z => ‖WithLp.toLp 2 (Z*ᵥx)‖^2) μ := by
  apply (hμ.mul_const (‖WithLp.toLp 2 x‖^2)).mono' (by fun_prop)
  apply ae_of_all
  intro Z
  rw [Real.norm_of_nonneg (sq_nonneg _),PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  exact sum_norm_sq_mulVec_le_frobSq Z x

omit [MeasurableSpace K] [BorelSpace K] in
private theorem exists_unitary_column_eq (x : q → K) (hx : ‖WithLp.toLp 2 x‖=1) (j : q) :
    ∃ U : Matrix.unitaryGroup q K,(U : Matrix q q K).col j=x := by
  classical
  let V : Matrix q Unit K := fun i _ => x i
  have hV : HasOrthonormalCols V := by
    apply (hasOrthonormalCols_iff_orthonormal V).mpr
    rw [orthonormal_iff_ite]
    intro a b
    have hab : a=b := Subsingleton.elim _ _
    subst b
    change inner K (WithLp.toLp 2 x) (WithLp.toLp 2 x) = _
    rw [inner_self_eq_norm_sq_to_K,hx]
    simp
  let e : Unit ↪ q := ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨W,hW,hcol⟩ := exists_unitary_completion V hV e
  refine ⟨⟨W,Matrix.mem_unitaryGroup_iff'.mpr hW⟩,?_⟩
  funext i
  exact hcol i ()

private theorem integral_norm_mulVec_sq_eq_fixed_column
    (μ : Measure (Matrix r q K)) (hinv : RightUnitaryInvariant μ) (j : q) (x : q → K) :
    (∫ Z,‖WithLp.toLp 2 (Z*ᵥx)‖^2 ∂μ) =
      ‖WithLp.toLp 2 x‖^2 * ∫ Z,‖WithLp.toLp 2 (Z.col j)‖^2 ∂μ := by
  by_cases hx : x=0
  · simp [hx]
  have hn : ‖WithLp.toLp 2 x‖≠0 := by
    intro h
    exact hx ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp h))
  let y : q → K := (‖WithLp.toLp 2 x‖⁻¹ : ℝ) • x
  have hy : ‖WithLp.toLp 2 y‖=1 := by
    change ‖(‖WithLp.toLp 2 x‖⁻¹ : ℝ) • WithLp.toLp 2 x‖=1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  obtain ⟨U,hU⟩ := exists_unitary_column_eq y hy j
  have hrep : x = (‖WithLp.toLp 2 x‖ : ℝ) • y := by
    dsimp [y]
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hcol (Z : Matrix r q K) : (Z*(U : Matrix q q K)).col j = Z*ᵥy := by
    funext i
    change ∑ k,Z i k*(U : Matrix q q K) k j = ∑ k,Z i k*y k
    apply Finset.sum_congr rfl
    intro k _
    rw [← congrFun hU k]
    rfl
  have hp (Z : Matrix r q K) : ‖WithLp.toLp 2 (Z*ᵥx)‖^2 =
      ‖WithLp.toLp 2 x‖^2 * ‖WithLp.toLp 2 ((Z*(U : Matrix q q K)).col j)‖^2 := by
    conv_lhs => rw [hrep]
    rw [Matrix.mulVec_smul,WithLp.toLp_smul,norm_smul,Real.norm_of_nonneg (norm_nonneg _),mul_pow,hcol]
  have hl : HasLaw (fun Z : Matrix r q K => Z*(U : Matrix q q K)) μ μ :=
    ⟨(by fun_prop),hinv U⟩
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  exact hl.integral_comp (f := fun Z : Matrix r q K => ‖WithLp.toLp 2 (Z.col j)‖^2) (by
    apply Continuous.aestronglyMeasurable
    unfold Matrix.col
    fun_prop)

/-- Right-unitary invariance and a finite Frobenius second moment force the
exact directional second moment in every fixed input direction. -/
theorem integral_norm_mulVec_sq_of_rightUnitaryInvariant [Nonempty q]
    (μ : Measure (Matrix r q K)) (hμ : Integrable (fun Z => frobSq Z) μ)
    (hinv : RightUnitaryInvariant μ) (x : q → K) :
    (∫ Z,‖WithLp.toLp 2 (Z*ᵥx)‖^2 ∂μ) =
      ((∫ Z,frobSq Z ∂μ)/Fintype.card q)*‖WithLp.toLp 2 x‖^2 := by
  let j : q := Classical.arbitrary q
  let c := ∫ Z,‖WithLp.toLp 2 (Z.col j)‖^2 ∂μ
  have he (i : q) : (∫ Z,‖WithLp.toLp 2 (Z.col i)‖^2 ∂μ)=c := by
    have h := integral_norm_mulVec_sq_eq_fixed_column μ hinv j (Pi.single i 1)
    simpa using h
  have hc : (∫ Z,frobSq Z ∂μ) = Fintype.card q*c := by
    have hpoint (Z : Matrix r q K) : frobSq Z = ∑ i,‖WithLp.toLp 2 (Z.col i)‖^2 := by
      simp only [frobSq_eq_sum_norm_sq,PiLp.norm_sq_eq_of_L2,Matrix.col_apply]
      exact Finset.sum_comm
    simp_rw [hpoint]
    rw [integral_finsetSum _ (fun i _ => hμ.mono' (by
        apply Continuous.aestronglyMeasurable
        unfold Matrix.col
        fun_prop)
      (ae_of_all _ fun Z => by rw [Real.norm_of_nonneg (sq_nonneg _)];exact norm_column_sq_le_frobSq Z i))]
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [integral_norm_mulVec_sq_eq_fixed_column μ hinv j x,hc]
  have hn : (Fintype.card q : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero (α := q)
  dsimp [c]
  field_simp

/-- Every fixed matrix image is integrable and has the exact isotropic
Frobenius expectation. Empty row/output dimensions are included. -/
theorem integrable_and_integral_frobSq_mul_of_rightUnitaryInvariant [Nonempty q]
    (μ : Measure (Matrix r q K)) (hμ : Integrable (fun Z => frobSq Z) μ)
    (hinv : RightUnitaryInvariant μ) (D : Matrix q p K) :
    Integrable (fun Z => frobSq (Z*D)) μ ∧
      (∫ Z,frobSq (Z*D) ∂μ) = ((∫ Z,frobSq Z ∂μ)/Fintype.card q)*frobSq D := by
  have hp (Z : Matrix r q K) : frobSq (Z*D) = ∑ j,‖WithLp.toLp 2 (Z*ᵥD.col j)‖^2 := by
    simp only [frobSq_eq_sum_norm_sq,PiLp.norm_sq_eq_of_L2,Matrix.mul_apply,Matrix.mulVec,Matrix.col_apply,dotProduct]
    exact Finset.sum_comm
  constructor
  · simp_rw [hp]
    exact integrable_finsetSum _ (fun j _ => integrable_norm_mulVec_sq_of_integrable_frobSq μ hμ (D.col j))
  · simp_rw [hp]
    rw [integral_finsetSum _ (fun j _ => integrable_norm_mulVec_sq_of_integrable_frobSq μ hμ (D.col j))]
    simp_rw [integral_norm_mulVec_sq_of_rightUnitaryInvariant μ hμ hinv]
    rw [← Finset.mul_sum]
    congr 1
    simp only [PiLp.norm_sq_eq_of_L2,frobSq_eq_sum_norm_sq,Matrix.col_apply]
    exact Finset.sum_comm

open scoped Matrix.Norms.L2Operator in
private local instance unitaryIsotropyRealNormedSpace : NormedSpace ℝ (Matrix r q K) :=
  NormedSpace.restrictScalars ℝ K (Matrix r q K)

local instance : SecondCountableTopology (Matrix r q K) :=
  inferInstanceAs (SecondCountableTopology (r → q → K))

open scoped Matrix.Norms.L2Operator in
/-- A finite Frobenius second moment gives an integrable actual matrix mean. -/
theorem integrable_matrix_of_integrable_frobSq
    (μ : Measure (Matrix r q K)) [IsFiniteMeasure μ] (hμ : Integrable (fun Z => frobSq Z) μ) :
    Integrable (fun Z => Z) μ := by
  have hs : Integrable (fun Z : Matrix r q K => ‖Z‖^2) μ := by
    apply hμ.mono' (by fun_prop)
    apply ae_of_all
    intro Z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact specNorm_sq_le_frobSq Z
  exact ((memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hs).integrable (by norm_num)

open scoped Matrix.Norms.L2Operator in
/-- Right-unitary invariance forces the actual mean matrix to vanish, via `-I`. -/
theorem integral_matrix_eq_zero_of_rightUnitaryInvariant
    (μ : Measure (Matrix r q K)) (hinv : RightUnitaryInvariant μ) : (∫ Z,Z ∂μ)=0 := by
  let U : Matrix.unitaryGroup q K := ⟨-1,Matrix.mem_unitaryGroup_iff'.mpr (by simp)⟩
  have hl : HasLaw (fun Z : Matrix r q K => Z*(U : Matrix q q K)) μ μ :=
    ⟨(by fun_prop),hinv U⟩
  have he := hl.integral_eq
  change (∫ Z,Z*(-1 : Matrix q q K) ∂μ)=∫ Z,Z ∂μ at he
  simp only [Matrix.mul_neg,Matrix.mul_one] at he
  rw [integral_neg (fun Z : Matrix r q K => Z)] at he
  ext i j
  have h := congrArg (fun Z : Matrix r q K => Z i j) he
  change -(∫ Z,Z ∂μ) i j = (∫ Z,Z ∂μ) i j at h
  change (∫ Z,Z ∂μ) i j = 0
  linear_combination -(1/2 : K)*h

end NLAlib
