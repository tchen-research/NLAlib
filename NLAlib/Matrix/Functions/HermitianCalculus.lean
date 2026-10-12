import NLAlib.Matrix.Basic.Dilation
import Mathlib.Analysis.CStarAlgebra.Spectrum
import NLAlib.Matrix.Functions.ExpLogPosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Hermitian calculus for complex matrices

Small deterministic facts used throughout the matrix concentration files, collected here so that
each has one copy:

* spectral calculus of a Hermitian matrix: `matrixExp_smul_eq_cfc`, `traceExp_smul_eq_sum`,
  `le_of_mem_spectrum_of_lambdaMax_le`, `abs_le_norm_of_mem_spectrum`;
* Loewner bounds for the matrix exponential (moved from `Concentration/Matrix/BernsteinMgfCgf`):
  `one_add_smul_add_smul_sq_eq_cfc`, `matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le`,
  `one_add_le_matrixExp_of_isHermitian`;
* reindexing: `reindexStarAlgEquiv`, `norm_reindex`, `lambdaMax_reindex`;
* the Hermitian dilation and block-diagonal matrices: `dilationLinearMap`, `dilation_sq`,
  `fromBlocks₁₁CLM`, `fromBlocks₂₂CLM`;
* block-diagonal positivity and norm: `posSemidef_fromBlocks_diag`, `norm_fromBlocks_diag`, and the
  isometric-compression bound `norm_conjTranspose_mul_mul_le`.

The integral versions (`integral_reindex`, `integral_fromBlocks_diag`) are in
`NLAlib.Probability.Concentration.Basic.MatrixCalculus`.

Atlas: support for `matrix-laplace`, `matrix-gaussian-series`, `matrix-chernoff`,
`matrix-bernstein`, `hermitian-dilation`, `intrinsic-dimension`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8*
(Tropp 2015), where each of these appeared as a private helper in several files; moved from
`NLAlib.Probability.Concentration.Basic.MatrixCalculus` (dedup round 2026-10-12).
-/

open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace NLAlib

section Spectral

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For Hermitian `A`, `matrixExp (s • A)` is the functional calculus of `x ↦ exp (s x)` at `A`.
Tropp 2015, §2.1.11. -/
theorem matrixExp_smul_eq_cfc (A : Matrix d d ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

/-- For Hermitian `A`, `traceExp (θ • A) = ∑ i, exp (θ λᵢ)` over the eigenvalues of `A`. Tropp
2015, §3.1. -/
theorem traceExp_smul_eq_sum (A : Matrix d d ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

/-- For Hermitian `A` with `lambdaMax A ≤ L`, every real spectral value of `A` is at most `L`.
Tropp 2015, §2.1. -/
theorem le_of_mem_spectrum_of_lambdaMax_le (A : Matrix d d ℂ) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

/-- A real spectral value of a square complex matrix is bounded in absolute value by its ℓ₂
operator norm. Tropp 2015, §2.1. -/
theorem abs_le_norm_of_mem_spectrum [Nonempty d] (B : Matrix d d ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

/-- Real functional calculus evaluates the actual affine-quadratic polynomial at any
finite Hermitian matrix.
Source: scalar polynomial functional calculus, Tropp 2015, Section 2.1.11;
reused by `matrix-bernstein` and `matrix-freedman` (partial). -/
theorem one_add_smul_add_smul_sq_eq_cfc (A : Matrix d d ℂ) (hA : A.IsHermitian) (θ c : ℝ) :
    1 + θ • A + c • A ^ 2 = cfc (fun x => 1 + θ * x + c * x ^ 2) A := by
  have e1 := cfc_add A (fun x => 1 + θ * x) (fun x => c * x ^ 2)
  have e2 := cfc_const_add 1 (fun x => θ * x) A
  rw [e1, e2, cfc_const_mul_id θ A, cfc_const_mul c (fun x : ℝ => x ^ 2) A,
    cfc_pow_id A 2 hA.isSelfAdjoint, map_one]

/-- A scalar exponential-versus-quadratic comparison on the actual spectrum transfers
to Loewner order for a finite Hermitian matrix.
Source: scalar functional calculus monotonicity, Tropp 2015, Lemma 6.6.2;
reused by `matrix-bernstein` and `matrix-freedman` (partial). -/
theorem matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le
    (A : Matrix d d ℂ) (hA : A.IsHermitian) {θ c : ℝ}
    (hb : ∀ x ∈ spectrum ℝ A, Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2) :
    matrixExp (θ • A) ≤ 1 + θ • A + c • A ^ 2 := by
  rw [matrixExp_smul_eq_cfc A hA θ, one_add_smul_add_smul_sq_eq_cfc A hA θ c]
  exact cfc_mono hb

/-- The scalar tangent inequality `1+x ≤ exp x` transfers to every finite Hermitian
matrix as `I+B ≤ exp B`, without a lower or upper spectral bound.
Source: `Real.add_one_le_exp` and scalar functional calculus, Tropp 2015, Section 2.1.11;
reused by `matrix-bernstein` and `matrix-freedman` (partial). -/
theorem one_add_le_matrixExp_of_isHermitian (B : Matrix d d ℂ) (hB : B.IsHermitian) :
    1 + B ≤ matrixExp B := by
  have e1 : 1 + B = cfc (fun x : ℝ => 1 + x) B := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) B, cfc_id' ℝ B hB.isSelfAdjoint, map_one]
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hB, e1]
  exact cfc_mono (fun x _ => by linarith [Real.add_one_le_exp x])

end Spectral

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- `Matrix.reindex e e` as a `⋆`-algebra equivalence of square complex matrices over `ℂ`. -/
def reindexStarAlgEquiv (e : ι ≃ κ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

/-- Reindexing preserves the ℓ₂ operator norm. -/
theorem norm_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖Matrix.reindex e e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (reindexStarAlgEquiv e) A

/-- Reindexing preserves the real spectrum: `spectrum ℝ (reindex e e A) = spectrum ℝ A`. -/
theorem spectrum_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    spectrum ℝ (Matrix.reindex e e A) = spectrum ℝ A := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e) A
  rwa [Matrix.coe_reindexAlgEquiv] at h

/-- Reindexing preserves the real spectrum, hence `lambdaMax`. -/
theorem lambdaMax_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    lambdaMax (Matrix.reindex e e A) = lambdaMax A := by
  unfold lambdaMax
  rw [spectrum_reindex]

end Reindex

section Blocks

open Matrix

/-- The Hermitian dilation as a real-linear map. Tropp 2015, Def. 2.1.5. Atlas:
`hermitian-dilation`. -/
def dilationLinearMap (m n : Type*) : Matrix m n ℂ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun := dilation
  map_add' X Y := by
    simp [dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' c X := by
    simp [dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

/-- `dilationLinearMap` applies `dilation`. -/
@[simp]
theorem dilationLinearMap_apply {m n : Type*} (X : Matrix m n ℂ) :
    dilationLinearMap m n X = dilation X := rfl

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The square of the Hermitian dilation is block diagonal: `(dilation X)² =
fromBlocks (X Xᴴ) 0 0 (Xᴴ X)`. Tropp 2015, eq. (2.1.28). Atlas: `hermitian-dilation`. -/
theorem dilation_sq (X : Matrix m n ℂ) :
    dilation X ^ 2 = fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
  simp [dilation, sq, fromBlocks_multiply]

variable (n) in
/-- The upper-left block inclusion `P ↦ fromBlocks P 0 0 0` as a continuous linear map. -/
def fromBlocks₁₁CLM : Matrix m m ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => fromBlocks P 0 0 0
      map_add' := fun P P' => by rw [fromBlocks_add]; simp
      map_smul' := fun c P => by rw [fromBlocks_smul]; simp }

variable (m) in
/-- The lower-right block inclusion `Q ↦ fromBlocks 0 0 0 Q` as a continuous linear map. -/
def fromBlocks₂₂CLM : Matrix n n ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q => fromBlocks 0 0 0 Q
      map_add' := fun Q Q' => by rw [fromBlocks_add]; simp
      map_smul' := fun c Q => by rw [fromBlocks_smul]; simp }

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₁₁CLM` puts its argument in the upper-left block. -/
@[simp]
theorem fromBlocks₁₁CLM_apply (P : Matrix m m ℂ) :
    fromBlocks₁₁CLM n P = fromBlocks P 0 0 0 := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₂₂CLM` puts its argument in the lower-right block. -/
@[simp]
theorem fromBlocks₂₂CLM_apply (Q : Matrix n n ℂ) :
    fromBlocks₂₂CLM m Q = fromBlocks 0 0 0 Q := rfl

end Blocks

section BlockDiagonal

/-! ### Block-diagonal matrices: positivity and operator norm -/

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A block-diagonal matrix `fromBlocks P 0 0 Q` with positive semidefinite diagonal blocks is
positive semidefinite (over any star-ordered commutative ring, in particular `ℝ` and `ℂ`).
Tropp 2015, §2.1.16 and §7.3; atlas `intrinsic-dimension` (helper). Promoted from private copies in
`Concentration/Matrix/{BlockIntrinsic,IntrinsicBernsteinExpectation}` (dedup round 2026-10-12). -/
theorem posSemidef_fromBlocks_diag {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] {P : Matrix m m R} {Q : Matrix n n R}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks hP.1 (by simp) hQ.1) fun x => ?_
  have e : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    rw [fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg (hP.dotProduct_mulVec_nonneg _) (hQ.dotProduct_mulVec_nonneg _)

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq m] [DecidableEq n]

/-- Compression by an isometry does not increase the L2 operator norm: if `Eᴴ E = 1` then
`‖Eᴴ M E‖ ≤ ‖M‖`. Tropp 2015, §2.1.16; atlas `hermitian-dilation`, `intrinsic-dimension`
(helper). Promoted from the private `norm_compress_le` of
`Concentration/Matrix/{DilationVariance,BlockIntrinsic}` (dedup round 2026-10-12). -/
theorem norm_conjTranspose_mul_mul_le {k : Type*} [Fintype k] [DecidableEq k]
    (E : Matrix k m 𝕜) (hE : Eᴴ * E = 1) (M : Matrix k k 𝕜) :
    ‖Eᴴ * M * E‖ ≤ ‖M‖ := by
  have hE1 : ‖E‖ ≤ 1 := by
    have h1 : ‖(1 : Matrix m m 𝕜)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
    have h2 : ‖E‖ * ‖E‖ ≤ 1 := by
      rw [← l2_opNorm_conjTranspose_mul_self, hE]; exact h1
    nlinarith [norm_nonneg E]
  calc ‖Eᴴ * M * E‖ ≤ ‖Eᴴ * M‖ * ‖E‖ := l2_opNorm_mul _ _
    _ ≤ ‖Eᴴ‖ * ‖M‖ * ‖E‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

/-- The L2 operator norm of a block-diagonal matrix is the larger of the block norms:
`‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖`. Tropp 2015, eq. (2.2.10) and (7.3.4); atlas
`hermitian-dilation`, `intrinsic-dimension` (helper). Promoted from private copies in
`Concentration/Matrix/{DilationVariance,BlockIntrinsic}` (dedup round 2026-10-12). -/
theorem norm_fromBlocks_diag (P : Matrix m m 𝕜) (Q : Matrix n n 𝕜) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  apply le_antisymm
  · rw [cstar_norm_def]
    set c := max ‖P‖ ‖Q‖
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    let x₁ : EuclideanSpace 𝕜 m := WithLp.toLp 2 (fun i => x (Sum.inl i))
    let x₂ : EuclideanSpace 𝕜 n := WithLp.toLp 2 (fun i => x (Sum.inr i))
    have h1 := l2_opNorm_mulVec P x₁
    have h2 := l2_opNorm_mulVec Q x₂
    have hx : ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂]
    have hT : ‖toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks P 0 0 Q) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv m 𝕜).symm (P *ᵥ x₁)‖ ^ 2 +
          ‖(EuclideanSpace.equiv n 𝕜).symm (Q *ᵥ x₂)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [fromBlocks_mulVec, Fintype.sum_sum_type, x₁, x₂, Function.comp_def]
    have hP : ‖P‖ ≤ c := le_max_left _ _
    have hQ : ‖Q‖ ≤ c := le_max_right _ _
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hT, mul_pow, hx, mul_add]
    gcongr
    · calc _ ≤ (‖P‖ * ‖x₁‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
    · calc _ ≤ (‖Q‖ * ‖x₂‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
  · apply max_le
    · have h := norm_conjTranspose_mul_mul_le (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : P = (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h
    · have h := norm_conjTranspose_mul_mul_le (fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : Q = (fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h

end BlockDiagonal

section EigenProjections

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The rank-one spectral projection `U eᵢ eᵢᴴ Uᴴ` of a Hermitian matrix onto its `i`-th
eigenvector. Tropp 2015, §2.1.6 (helper). -/
noncomputable def eigenProj (A : Matrix d d ℂ) (hA : A.IsHermitian) (i : d) :
    Matrix d d ℂ :=
  (hA.eigenvectorUnitary : Matrix d d ℂ) * Matrix.single i i 1 *
    star (hA.eigenvectorUnitary : Matrix d d ℂ)

/-- Spectral decomposition of the functional calculus:
`cfc f A = ∑ᵢ f (λᵢ) • eigenProj A hA i`. Tropp 2015, §2.1.6 (helper). -/
theorem cfc_eq_sum_smul_eigenProj (A : Matrix d d ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (hA.eigenvalues i) • eigenProj A hA i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.sum_single_eq_diagonal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : Matrix.single i i ((RCLike.ofReal ∘ f ∘ hA.eigenvalues) i : ℂ)
      = f (hA.eigenvalues i) • (Matrix.single i i (1 : ℂ)) := by
    rw [Matrix.smul_single]; simp [Complex.real_smul]
  rw [this, eigenProj, Matrix.mul_smul, Matrix.smul_mul]

/-- `c • A² = cfc (x ↦ c x²) A` for Hermitian `A`. Tropp 2015, §4.6 (helper). -/
theorem smul_sq_eq_cfc (A : Matrix d d ℂ) (hA : A.IsHermitian) (c : ℝ) :
    c • A ^ 2 = cfc (fun x => c * x ^ 2) A := by
  rw [cfc_const_mul c (fun x : ℝ => x ^ 2) A, cfc_pow_id A 2 hA.isSelfAdjoint]

/-- `matrixExp (c • A²) = cfc (x ↦ exp (c x²)) A` for Hermitian `A`. Tropp 2015, §4.6 (helper). -/
theorem matrixExp_smul_sq_eq_cfc (A : Matrix d d ℂ) (hA : A.IsHermitian) (c : ℝ) :
    matrixExp (c • A ^ 2) = cfc (fun x => Real.exp (c * x ^ 2)) A := by
  rw [matrixExp_smul_eq_cfc (A ^ 2) (hA.pow 2) c,
    ← cfc_comp_pow (fun y => Real.exp (c * y)) 2 A (by fun_prop) hA.isSelfAdjoint]

end EigenProjections

end NLAlib
