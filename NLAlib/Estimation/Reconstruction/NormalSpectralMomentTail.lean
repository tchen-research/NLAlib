import NLAlib.Estimation.Reconstruction.NormalEmpiricalSpectralLaw
import NLAlib.Probability.Gaussian.Concentration.ComplexSphereDiagonal
import NLAlib.Polynomial.FunctionApproximation.ChebyshevBounds
import NLAlib.Probability.Transforms.TensorChebyshevMomentWasserstein
import NLAlib.Probability.Transforms.TensorChebyshevLattice

/-!
# Native normal spectral-moment concentration

The weighted law uses the actual random starting vector. Unitary invariance
transfers the finite diagonal sphere estimate to native spectral integrals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Real Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem integral_diagonalSpectralLaw_real (U : Matrix.unitaryGroup n ℂ)
    (d : n → ℂ) (b : n → ℂ) (f : ℂ → ℝ) :
    ∫ z, f z ∂diagonalSpectralLaw U d b =
      ∑ i, Complex.normSq (((U : Matrix n n ℂ)ᴴ *ᵥ b) i)*f (d i) := by
  have he := congrArg Complex.re (integral_diagonalSpectralLaw U d b (fun z => (f z : ℂ)))
  simpa only [integral_complex_ofReal,Complex.ofReal_re,Complex.re_sum,Complex.smul_re,
    Complex.normSq_eq_norm_sq,smul_eq_mul] using he

omit [DecidableEq n] in
private theorem integral_uniformComplexSpectralLaw_real (d : n → ℂ) (f : ℂ → ℝ) :
    ∫ z, f z ∂uniformComplexSpectralLaw d = (∑ i, f (d i))/(Fintype.card n : ℝ) := by
  have he := congrArg Complex.re (integral_uniformComplexSpectralLaw d (fun z => (f z : ℂ)))
  simp only [integral_complex_ofReal,Complex.ofReal_re] at he
  convert he using 1
  rw [← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re]

/-- Any bounded real function on a specified normal spectrum has its genuine
weighted spectral integral concentrated about the empirical spectral integral.
The function need not be continuous: the spectral laws are finite atomic laws. -/
theorem measureReal_normalSpectralLaw_integral_sub_empirical_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A)
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hU : A = (U : Matrix n n ℂ)*Matrix.diagonal d*(U : Matrix n n ℂ)ᴴ)
    (f : ℂ → ℝ) (hf : ∀ i, f (d i) ∈ Set.Icc (-1 : ℝ) 1) {r : ℝ} (hr : 0 < r) :
    (complexSphereVector n).real {b | r < |(∫ z, f z ∂normalSpectralLaw hA b) -
      ∫ z, f z ∂normalEmpiricalSpectralLaw hA|} ≤
      2*exp (-(Fintype.card n : ℝ)*r^2/2) := by
  let c : n → ℝ := fun i => f (d i)
  let m := (∑ i, c i)/(Fintype.card n : ℝ)
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmean : ∑ i, c i = (Fintype.card n : ℝ)*m := by dsimp [m];field_simp
  have hm : m ∈ Set.Icc (-1 : ℝ) 1 := by
    have hlow : ∑ i, (-1 : ℝ) ≤ ∑ i, c i := Finset.sum_le_sum (fun i _ => (hf i).1)
    have hhigh : ∑ i, c i ≤ ∑ i, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hf i).2)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_neg,mul_one] at hlow hhigh
    constructor
    · exact (le_div_iff₀ hn).mpr (by linarith)
    · exact (div_le_iff₀ hn).mpr (by linarith)
  have he (b : n → ℂ) :
      (∫ z, f z ∂normalSpectralLaw hA b) - ∫ z, f z ∂normalEmpiricalSpectralLaw hA =
        sphereDiagonalForm c ((U : Matrix n n ℂ)ᴴ *ᵥ b)-m := by
    rw [normalSpectralLaw_eq_diagonalSpectralLaw hA U d hU b,
      normalEmpiricalSpectralLaw_eq_uniformComplexSpectralLaw hA U d hU,
      integral_diagonalSpectralLaw_real,integral_uniformComplexSpectralLaw_real]
    simp only [sphereDiagonalForm,c,m,mul_comm]
  simp_rw [he]
  have hunit : HasOrthonormalCols (U : Matrix n n ℂ)ᴴ := by
    change ((U : Matrix n n ℂ)ᴴ)ᴴ * (U : Matrix n n ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact Unitary.coe_mul_star_self U
  have hl := hasLaw_mulVec_complexSphereVector_unitary (U : Matrix n n ℂ)ᴴ hunit
  rw [hl.measureReal_eq (p := fun b : n → ℂ => r < |sphereDiagonalForm c b-m|) (by
    unfold sphereDiagonalForm
    exact measurableSet_lt measurable_const (by fun_prop))]
  exact measureReal_abs_sphereDiagonalForm_sub_mean_gt_le c hm hr hf hmean

open scoped Matrix.Norms.L2Operator in
private theorem norm_diagonal_atom_le_specNorm {A : Matrix n n ℂ}
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hU : A = (U : Matrix n n ℂ)*Matrix.diagonal d*(U : Matrix n n ℂ)ᴴ) (i : n) :
    ‖d i‖ ≤ specNorm A := by
  let : Nonempty n := ⟨i⟩
  have hs : spectrum ℂ A = Set.range d := by
    rw [hU]
    simpa only [← Matrix.star_eq_conjTranspose,Unitary.coe_star,spectrum_diagonal] using
      (Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal d) (U := U))
  have hm : d i ∈ spectrum ℂ A := hs.symm ▸ Set.mem_range_self i
  simpa only [← specNorm_eq_norm] using spectrum.norm_le_norm_of_mem hm

/-- Every actual normalized mixed tensor moment has a dimension-dependent
native probability tail. The target is the empirical eigenvalue measure. -/
theorem measureReal_normalTensorMomentDiscrepancy_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) (hbound : specNorm A ≤ 1)
    (α : Fin 2 → ℕ) {r : ℝ} (hr : 0 < r) :
    (complexSphereVector n).real {b | r < |tensorChebyshevMomentDiscrepancy
      (normalCoordinateSpectralLaw hA b) (normalEmpiricalCoordinateSpectralLaw hA) α|} ≤
      2*exp (-(Fintype.card n : ℝ)*r^2/2) := by
  obtain ⟨U,d,hU⟩ := exists_unitary_diagonalization_of_normal hA
  let f : ℂ → ℝ := fun z => tensorNormalizedChebyshev α
    (WithLp.ofLp (Complex.orthonormalBasisOneI.repr z))
  have hf : ∀ i, f (d i) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    apply abs_le.mp
    apply abs_tensorNormalizedChebyshev_le_one
    have hz := (norm_diagonal_atom_le_specNorm U d hU i).trans hbound
    intro j
    fin_cases j
    · exact abs_le.mp ((Complex.abs_re_le_norm (d i)).trans hz)
    · exact abs_le.mp ((Complex.abs_im_le_norm (d i)).trans hz)
  have he (b : n → ℂ) : tensorChebyshevMomentDiscrepancy
      (normalCoordinateSpectralLaw hA b) (normalEmpiricalCoordinateSpectralLaw hA) α =
      (∫ z, f z ∂normalSpectralLaw hA b) - ∫ z, f z ∂normalEmpiricalSpectralLaw hA := by
    rw [tensorChebyshevMomentDiscrepancy,normalCoordinateSpectralLaw,
      normalEmpiricalCoordinateSpectralLaw,integral_map
      Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable
      (by fun_prop),integral_map
      Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable (by fun_prop)]
  simp_rw [he]
  exact measureReal_normalSpectralLaw_integral_sub_empirical_gt_le hA U d hU f hf hr

/-- A simultaneous failure bound for every retained normalized tensor moment;
all moments use one native random starting vector. -/
theorem measureReal_exists_normalTensorMomentDiscrepancy_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) (hbound : specNorm A ≤ 1)
    (M : ℕ) {r : ℝ} (hr : 0 < r) :
    (complexSphereVector n).real {b | ∃ α ∈ tensorChebyshevMomentIndices 2 M,
      r < |tensorChebyshevMomentDiscrepancy (normalCoordinateSpectralLaw hA b)
        (normalEmpiricalCoordinateSpectralLaw hA) α|} ≤
      (tensorChebyshevMomentIndices 2 M).card *
        (2*exp (-(Fintype.card n : ℝ)*r^2/2)) := by
  let E := fun α : Fin 2 → ℕ => {b : n → ℂ |
    r < |tensorChebyshevMomentDiscrepancy (normalCoordinateSpectralLaw hA b)
      (normalEmpiricalCoordinateSpectralLaw hA) α|}
  change (complexSphereVector n).real {b | ∃ α ∈ tensorChebyshevMomentIndices 2 M,b ∈ E α} ≤ _
  have he : {b | ∃ α ∈ tensorChebyshevMomentIndices 2 M,b ∈ E α} =
      ⋃ α ∈ tensorChebyshevMomentIndices 2 M,E α := by ext b;simp
  rw [he]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _α ∈ tensorChebyshevMomentIndices 2 M,
        2*exp (-(Fintype.card n : ℝ)*r^2/2) :=
      Finset.sum_le_sum fun α _ => measureReal_normalTensorMomentDiscrepancy_gt_le hA hbound α hr
    _ = _ := by simp

/-- The explicit deviation radius in the normal spectral-density card. -/
def normalTensorMomentRadius (n M : ℕ) (δ : ℝ) : ℝ :=
  sqrt ((8/(2*(n : ℝ)-1))*log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ))

/-- The radius is strictly positive throughout the card's parameter range. -/
theorem normalTensorMomentRadius_pos {n M : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < normalTensorMomentRadius n M δ := by
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKnat : 1 ≤ (M+1)^2-1 := by
    have : 4 ≤ (M+1)^2 := by nlinarith
    omega
  have hK : (1 : ℝ) ≤ ((M+1)^2-1 : ℕ) := by exact_mod_cast hKnat
  have hden : 0 < 2*(n : ℝ)-1 := by linarith
  apply sqrt_pos.mpr
  apply mul_pos (div_pos (by norm_num) hden)
  apply log_pos
  exact (one_lt_div hδ).mpr (by linarith)

/-- The stronger quadratic-form exponent pays the complete simultaneous
failure budget at the source's explicit radius. -/
theorem card_mul_exp_normalTensorMomentRadius_le {n M : ℕ}
    (hn : 1 ≤ n) (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (((M+1)^2-1 : ℕ) : ℝ)*(2*exp (-(n : ℝ)*(normalTensorMomentRadius n M δ)^2/2)) ≤ δ := by
  let K : ℝ := ((M+1)^2-1 : ℕ)
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKnat : 1 ≤ (M+1)^2-1 := by
    have : 4 ≤ (M+1)^2 := by nlinarith
    omega
  have hK : (1 : ℝ) ≤ K := by dsimp [K];exact_mod_cast hKnat
  have hden : 0 < 2*(n : ℝ)-1 := by linarith
  have harg : 1 < 2*K/δ := (one_lt_div hδ).mpr (by linarith)
  have hl : 0 < log (2*K/δ) := log_pos harg
  have hsq : normalTensorMomentRadius n M δ ^ 2 =
      8/(2*(n : ℝ)-1)*log (2*K/δ) := by
    unfold normalTensorMomentRadius
    exact sq_sqrt (mul_nonneg (by positivity) hl.le)
  have hc : 1 ≤ 4*(n : ℝ)/(2*(n : ℝ)-1) := (le_div_iff₀ hden).mpr (by linarith)
  have hexp : exp (-(n : ℝ)*(normalTensorMomentRadius n M δ)^2/2) ≤ δ/(2*K) := by
    calc
      _ ≤ exp (-log (2*K/δ)) := by
        apply exp_le_exp.mpr
        rw [hsq]
        have h := mul_le_mul_of_nonneg_right hc hl.le
        calc
          _ = -(4*(n : ℝ)/(2*(n : ℝ)-1)*log (2*K/δ)) := by ring
          _ ≤ _ := by simpa only [one_mul] using neg_le_neg h
      _ = δ/(2*K) := by rw [exp_neg,exp_log (by positivity)];field_simp
  change K*(2*exp _) ≤ δ
  calc
    _ ≤ K*(2*(δ/(2*K))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by linarith)
    _ = δ := by field_simp

/-- With the explicit radius, the full native family of mixed moments fails
with probability at most `δ`. -/
theorem measureReal_exists_normalTensorMomentDiscrepancy_radius_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) (hbound : specNorm A ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (complexSphereVector n).real {b | ∃ α ∈ tensorChebyshevMomentIndices 2 M,
      normalTensorMomentRadius (Fintype.card n) M δ <
        |tensorChebyshevMomentDiscrepancy (normalCoordinateSpectralLaw hA b)
          (normalEmpiricalCoordinateSpectralLaw hA) α|} ≤ δ := by
  apply (measureReal_exists_normalTensorMomentDiscrepancy_gt_le hA hbound M
    (normalTensorMomentRadius_pos Fintype.card_pos hM hδ hδ1)).trans
  rw [card_tensorChebyshevMomentIndices]
  exact card_mul_exp_normalTensorMomentRadius_le Fintype.card_pos hM hδ hδ1

/-- The source's complete weighted normalized-moment bound for a single native
complex-sphere starting vector and the empirical normal spectral law. -/
theorem measureReal_normalTensorMomentError_radius_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ = Aᴴ*A) (hbound : specNorm A ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (complexSphereVector n).real {b |
      normalTensorMomentRadius (Fintype.card n) M δ * sqrt (5+(π/2)*log M) <
        tensorChebyshevMomentError (normalCoordinateSpectralLaw hA b)
          (normalEmpiricalCoordinateSpectralLaw hA) M} ≤ δ := by
  apply (measureReal_mono ?_).trans
    (measureReal_exists_normalTensorMomentDiscrepancy_radius_gt_le hA hbound hM hδ hδ1)
  intro b hb
  change normalTensorMomentRadius (Fintype.card n) M δ * sqrt (5+(π/2)*log M) <
    tensorChebyshevMomentError (normalCoordinateSpectralLaw hA b)
      (normalEmpiricalCoordinateSpectralLaw hA) M at hb
  by_contra he
  have hcoord : ∀ α ∈ tensorChebyshevMomentIndices 2 M,
      |tensorChebyshevMomentDiscrepancy (normalCoordinateSpectralLaw hA b)
        (normalEmpiricalCoordinateSpectralLaw hA) α| ≤
        normalTensorMomentRadius (Fintype.card n) M δ := by
    intro α hα
    exact le_of_not_gt (fun h => he ⟨α,hα,h⟩)
  exact (not_lt_of_ge (tensorChebyshevMomentError_le_of_discrepancy_le _ _ hM
    (normalTensorMomentRadius_pos Fintype.card_pos hM hδ hδ1).le hcoord)) hb

end NLAlib
