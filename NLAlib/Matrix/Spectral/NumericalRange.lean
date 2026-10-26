import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Spectral.EigenvectorPairing
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Numerical range

The numerical range is the image of the complex Euclidean unit sphere under
the quadratic form. Real matrices use their complexification. Its definition
includes empty matrix labels, for which the numerical range is empty.
Source: Horn–Johnson (1991), Chapter 1; Greenbaum (1997), Section 3.2.
Atlas: `field-of-values-def` (definition, compactness, norm, affine and isometry clauses).
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The numerical range of a complex matrix, defined using unit vectors in
the Euclidean norm. Empty matrices have empty numerical range.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  {z | ∃ x : n → ℂ, ‖WithLp.toLp 2 x‖ = 1 ∧ quadForm A x = z}

omit [DecidableEq n] in
/-- Membership in the numerical range is witnessed by a complex unit vector. -/
theorem mem_numericalRange_iff (A : Matrix n n ℂ) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : n → ℂ,
      ‖WithLp.toLp 2 x‖ = 1 ∧ quadForm A x = z := Iff.rfl

omit [DecidableEq n] in
/-- The numerical range is a compact image of the finite-dimensional unit sphere.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem isCompact_numericalRange (A : Matrix n n ℂ) : IsCompact (numericalRange A) := by
  have hc : Continuous (fun x : EuclideanSpace ℂ n => quadForm A x.ofLp) := by
    unfold quadForm
    exact (PiLp.continuous_ofLp 2 (fun _ : n => ℂ)).star.dotProduct
      (continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 (fun _ : n => ℂ)))
  have heq : numericalRange A = (fun x : EuclideanSpace ℂ n => quadForm A x.ofLp) ''
      Metric.sphere 0 1 := by
    ext z
    simp only [numericalRange, Set.mem_ofPred_eq, Set.mem_image, Metric.mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨WithLp.toLp 2 x, hx, hz⟩
    · rintro ⟨x, hx, hz⟩
      exact ⟨x.ofLp, hx, hz⟩
  rw [heq]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).image hc

/-- The modulus of the quadratic form is bounded by the spectral norm times
the vector's squared Euclidean norm. Cauchy–Schwarz gives the full complex
modulus, rather than only its real part. -/
theorem norm_quadForm_le_specNorm {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) (x : n → 𝕜) :
    ‖quadForm A x‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hi : inner 𝕜 (WithLp.toLp 2 x : EuclideanSpace 𝕜 n)
      (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace 𝕜 n) = quadForm A x := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rfl
  have hh := norm_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 x : EuclideanSpace 𝕜 n)
    (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace 𝕜 n)
  rw [hi] at hh
  calc
    _ ≤ _ := hh
    _ ≤ ‖WithLp.toLp 2 x‖ * (specNorm A * ‖WithLp.toLp 2 x‖) := by
      gcongr
      open scoped Matrix.Norms.L2Operator in
      exact A.l2_opNorm_mulVec (WithLp.toLp 2 x)
    _ = _ := by ring

/-- Every numerical-range point lies in the closed disk of radius the spectral norm.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem norm_le_specNorm_of_mem_numericalRange {A : Matrix n n ℂ} {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ specNorm A := by
  obtain ⟨x, hx, rfl⟩ := hz
  simpa only [hx, one_pow, mul_one] using norm_quadForm_le_specNorm A x

omit [DecidableEq n] in
/-- The Hermitian self-pairing of a complex unit vector is one. -/
theorem star_dotProduct_self_eq_one_of_norm_toLp_eq_one {x : n → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : star x ⬝ᵥ x = 1 := by
  calc
    star x ⬝ᵥ x = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 x) := by
      rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    _ = (‖WithLp.toLp 2 x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
    _ = 1 := by rw [hx]; norm_num

/-- Every spectral point belongs to the numerical range: normalize a nonzero
eigenvector. Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem spectrum_subset_numericalRange (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro z hz
  obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hz
  have hx' : (WithLp.toLp 2 x : EuclideanSpace ℂ n) ≠ 0 := by
    intro h
    apply hx
    exact congrArg WithLp.ofLp h
  have hn : ‖WithLp.toLp 2 x‖ ≠ 0 := (norm_pos_iff.mpr hx').ne'
  let c : ℂ := (‖WithLp.toLp 2 x‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖WithLp.toLp 2 x‖⁻¹ := by
    simp [c, norm_inv, Complex.norm_real]
  have hu : ‖WithLp.toLp 2 (c • x)‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, hc, inv_mul_cancel₀ hn]
  refine ⟨c • x, hu, ?_⟩
  have heigen : A *ᵥ (c • x) = z • (c • x) := by
    rw [Matrix.mulVec_smul, hAx, smul_comm]
  rw [quadForm, heigen, dotProduct_smul,
    star_dotProduct_self_eq_one_of_norm_toLp_eq_one hu, smul_eq_mul, mul_one]

/-- Affine transformations of matrices induce the same affine transformation
of the numerical range. No nonzero coefficient assumption is needed.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem numericalRange_smul_add_smul_one (A : Matrix n n ℂ) (α β : ℂ) :
    numericalRange (α • A + β • (1 : Matrix n n ℂ)) =
      (fun z => α * z + β) '' numericalRange A := by
  have hform (x : n → ℂ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
      quadForm (α • A + β • (1 : Matrix n n ℂ)) x = α * quadForm A x + β := by
    simp only [quadForm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul,
      star_dotProduct_self_eq_one_of_norm_toLp_eq_one hx, mul_one]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨quadForm A x, ⟨x, hx, rfl⟩, (hform x hx).symm⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hform x hx⟩

omit [DecidableEq m] in
/-- Multiplication by a matrix with orthonormal columns preserves vector norms. -/
theorem norm_toLp_mulVec_of_hasOrthonormalCols {Q : Matrix m n ℂ}
    (hQ : HasOrthonormalCols Q) (x : n → ℂ) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct]
  rw [← quadForm_conjTranspose_mul_self, hQ.conjTranspose_mul_self,
    quadForm_def, Matrix.one_mulVec]

omit [DecidableEq m] in
/-- Orthogonal compression can only shrink the numerical range.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem numericalRange_conjTranspose_mul_mul_subset {Q : Matrix m n ℂ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m m ℂ) :
    numericalRange (Qᴴ * A * Q) ⊆ numericalRange A := by
  rintro z ⟨x, hx, hz⟩
  refine ⟨Q *ᵥ x, ?_, ?_⟩
  · rw [norm_toLp_mulVec_of_hasOrthonormalCols hQ, hx]
  · rw [← quadForm_conjTranspose_mul_mul]
    exact hz

/-- Unitary similarity preserves the numerical range, including empty matrices.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem numericalRange_unitary_conjTranspose_mul_mul
    (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    numericalRange ((U : Matrix n n ℂ)ᴴ * A * (U : Matrix n n ℂ)) = numericalRange A := by
  have hU : HasOrthonormalCols (U : Matrix n n ℂ) := by
    change (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1
    simpa only [← Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hUt : HasOrthonormalCols (U : Matrix n n ℂ)ᴴ := by
    change (U : Matrix n n ℂ)ᴴᴴ * (U : Matrix n n ℂ)ᴴ = 1
    simpa only [Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_star, Unitary.coe_star]
      using Unitary.coe_mul_star_self U
  apply Set.Subset.antisymm (numericalRange_conjTranspose_mul_mul_subset hU A)
  have h := numericalRange_conjTranspose_mul_mul_subset hUt
    ((U : Matrix n n ℂ)ᴴ * A * (U : Matrix n n ℂ))
  have heq : (U : Matrix n n ℂ) *
      ((U : Matrix n n ℂ)ᴴ * A * (U : Matrix n n ℂ)) * (U : Matrix n n ℂ)ᴴ = A := by
    have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
      simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star] using
        Unitary.coe_mul_star_self U
    calc
      _ = ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) * A *
          ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  simpa only [Matrix.conjTranspose_conjTranspose, heq] using h

end NLAlib
