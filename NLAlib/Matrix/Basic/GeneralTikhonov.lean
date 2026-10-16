import NLAlib.Matrix.Basic.Tikhonov
import NLAlib.Matrix.Factorizations.GeneralizedSVD
/-!+# General-form Tikhonov minimizers

The penalty matrix may have any rank and may share a kernel with the data
matrix. The full minimizer affine space is the Moore–Penrose normal solution
plus that common kernel. Normalized GSVD coordinates give the explicit filter.

Source: Hansen, Rank-Deficient and Discrete Ill-Posed Problems, §4.4;
matrix-toolkit re-derivation §28. Atlas: `general-form-tikhonov-gsvd`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- The general-form regularized normal matrix. -/
def generalTikhonovNormal (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (β : ℝ) : Matrix n n 𝕜 :=
  Aᴴ * A + β • (Lᴴ * L)

/-- Squared data residual plus the actual squared penalty norm. -/
def generalTikhonovObjective (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (β : ℝ) (x : n → 𝕜) : ℝ :=
  ‖WithLp.toLp 2 (A *ᵥ x - b)‖ ^ 2 + β * ‖WithLp.toLp 2 (L *ᵥ x)‖ ^ 2

/-- The normal matrix is positive semidefinite for every nonnegative parameter. -/
theorem posSemidef_generalTikhonovNormal (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    {β : ℝ} (hβ : 0 ≤ β) : (generalTikhonovNormal A L β).PosSemidef :=
  (Matrix.posSemidef_conjTranspose_mul_self A).add
    ((Matrix.posSemidef_conjTranspose_mul_self L).smul hβ)

/-- The squared-residual objective equals twice the normal quadratic,
plus its fixed data energy. -/
theorem generalTikhonovObjective_eq_quadraticObjective (A : Matrix m n 𝕜)
    (L : Matrix p n 𝕜) (b : m → 𝕜) (β : ℝ) (x : n → 𝕜) :
    generalTikhonovObjective A L b β x =
      2 * quadraticObjective (generalTikhonovNormal A L β) (Aᴴ *ᵥ b) x +
        ‖WithLp.toLp 2 b‖ ^ 2 := by
  have hc : star (Aᴴ *ᵥ b) ⬝ᵥ x = star b ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose]
  have hr : RCLike.re (star (A *ᵥ x) ⬝ᵥ b) = RCLike.re (star b ⬝ᵥ (A *ᵥ x)) := by
    calc
      _ = RCLike.re (star (star b ⬝ᵥ (A *ᵥ x))) := by
        congr 1
        rw [← Matrix.star_dotProduct_star, star_star]
      _ = _ := by simp [RCLike.star_def]
  have hq : RCLike.re (quadForm (generalTikhonovNormal A L β) x) =
      RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) +
        β * RCLike.re (star (L *ᵥ x) ⬝ᵥ (L *ᵥ x)) := by
    simp only [generalTikhonovNormal, quadForm, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, map_add, RCLike.real_smul_eq_coe_mul,
      RCLike.re_ofReal_mul]
    rw [← quadForm, quadForm_conjTranspose_mul_self, ← quadForm,
      quadForm_conjTranspose_mul_self]
  simp only [generalTikhonovObjective, norm_toLp_sq_eq_re_star_dotProduct, star_sub,
    sub_dotProduct, dotProduct_sub, map_sub, quadraticObjective, hq, hc, hr]
  ring

/-- The diagonal of the normal matrix in normalized GSVD coordinates. -/
theorem IsNormalizedGSVD.generalTikhonovNormal_congruence
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (β : ℝ) :
    Xᴴ * generalTikhonovNormal A L β * X =
      diagonal (fun i => ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) := by
  rw [generalTikhonovNormal, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, h.left_gram, h.right_gram]
  ext i j
  by_cases he : i = j
  · subst j
    simp [Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul, map_add, map_mul, map_pow]
  · simp [Matrix.diagonal_apply, he]

/-- The data coefficient vanishes when its generalized singular data column does. -/
theorem IsNormalizedGSVD.coefficient_eq_zero_of_left_eq_zero
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) (i : n) (hi : c i = 0) :
    (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i = 0 := by
  have hc := h.left_col_eq_zero i hi
  rw [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul]
  change ∑ j, star ((A * X) j i) * b j = 0
  simp only [show ∀ j, (A * X) j i = 0 from fun j => congrFun hc j,
    star_zero, zero_mul, Finset.sum_const_zero]

/-- The explicit GSVD filter solves the normal equation, even at deficient
stacked rank: zero denominators have zero numerators.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.generalTikhonov_filter_normal_equation
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    generalTikhonovNormal A L β *ᵥ
      (X *ᵥ (fun i => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜))) =
        Aᴴ *ᵥ b := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_conjTranspose X).mpr h.invertible)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.generalTikhonovNormal_congruence]
  ext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : c i ^ 2 + β * s i ^ 2 = 0
  · have hc : c i = 0 := by nlinarith [sq_nonneg (c i), sq_nonneg (s i)]
    rw [h.coefficient_eq_zero_of_left_eq_zero b i hc, zero_div, mul_zero]
  · have hcast : ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hi
    exact mul_div_cancel₀ _ hcast

/-- The Moore–Penrose normal solution satisfies the normal equation at
every rank, without an additional range hypothesis.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem generalTikhonov_pinv_normal_equation (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    generalTikhonovNormal A L β *ᵥ
      (moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b)) = Aᴴ *ᵥ b := by
  obtain ⟨X, c, s, h⟩ := exists_isNormalizedGSVD A L
  have he := h.generalTikhonov_filter_normal_equation b hβ
  rw [← he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    mul_moorePenroseInverse_mul]

/-- Completing the square at any normal-equation solution leaves exactly
the two squared feasible-direction energies. -/
theorem generalTikhonovObjective_add_of_normal_equation
    (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β)
    (x : n → 𝕜) (hx : generalTikhonovNormal A L β *ᵥ x = Aᴴ *ᵥ b) (z : n → 𝕜) :
    generalTikhonovObjective A L b β (x + z) = generalTikhonovObjective A L b β x +
      ‖WithLp.toLp 2 (A *ᵥ z)‖ ^ 2 + β * ‖WithLp.toLp 2 (L *ᵥ z)‖ ^ 2 := by
  have he := quadraticObjective_add_of_mulVec_eq
    (posSemidef_generalTikhonovNormal A L hβ).isHermitian hx z
  simp only [generalTikhonovObjective_eq_quadraticObjective, he]
  have hq : RCLike.re (quadForm (generalTikhonovNormal A L β) z) =
      ‖WithLp.toLp 2 (A *ᵥ z)‖ ^ 2 + β * ‖WithLp.toLp 2 (L *ᵥ z)‖ ^ 2 := by
    simp only [generalTikhonovNormal, quadForm, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, map_add, RCLike.real_smul_eq_coe_mul,
      RCLike.re_ofReal_mul]
    rw [← quadForm, quadForm_conjTranspose_mul_self, ← quadForm,
      quadForm_conjTranspose_mul_self]
    simp only [norm_toLp_sq_eq_re_star_dotProduct]
  rw [hq]
  ring

/-- All minimizers are exactly the Moore–Penrose normal solution plus
the full common kernel. Uniqueness is therefore exactly triviality of
that kernel, rather than full rank of the data matrix alone.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem generalTikhonov_minimizers_iff (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) (y : n → 𝕜) :
    (∀ z, generalTikhonovObjective A L b β y ≤ generalTikhonovObjective A L b β z) ↔
      ∃ v, A *ᵥ v = 0 ∧ L *ᵥ v = 0 ∧
        y = moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b) + v := by
  let x := moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b)
  have hx := generalTikhonov_pinv_normal_equation A L b hβ
  have he (z : n → 𝕜) : generalTikhonovObjective A L b β z =
      generalTikhonovObjective A L b β x + ‖WithLp.toLp 2 (A *ᵥ (z - x))‖ ^ 2 +
        β * ‖WithLp.toLp 2 (L *ᵥ (z - x))‖ ^ 2 := by
    simpa only [add_sub_cancel] using
      generalTikhonovObjective_add_of_normal_equation A L b hβ.le x hx (z - x)
  have hmin (z : n → 𝕜) : generalTikhonovObjective A L b β x ≤
      generalTikhonovObjective A L b β z := by
    rw [he z]
    have hn := mul_nonneg hβ.le (sq_nonneg ‖WithLp.toLp 2 (L *ᵥ (z - x))‖)
    linarith [sq_nonneg ‖WithLp.toLp 2 (A *ᵥ (z - x))‖]
  constructor
  · intro hy
    have hle := hy x
    rw [he y] at hle
    have hA : A *ᵥ (y - x) = 0 := by
      have hn : ‖WithLp.toLp 2 (A *ᵥ (y - x))‖ = 0 := by
        nlinarith [sq_nonneg ‖WithLp.toLp 2 (A *ᵥ (y - x))‖,
          sq_nonneg ‖WithLp.toLp 2 (L *ᵥ (y - x))‖,
          norm_nonneg (WithLp.toLp 2 (A *ᵥ (y - x)))]
      exact congrArg WithLp.ofLp (norm_eq_zero.mp hn)
    have hL : L *ᵥ (y - x) = 0 := by
      have hn : ‖WithLp.toLp 2 (L *ᵥ (y - x))‖ = 0 := by
        apply le_antisymm _ (norm_nonneg _)
        by_contra hh
        have hp := mul_pos hβ (sq_pos_of_pos (lt_of_not_ge hh))
        nlinarith [sq_nonneg ‖WithLp.toLp 2 (A *ᵥ (y - x))‖]
      exact congrArg WithLp.ofLp (norm_eq_zero.mp hn)
    exact ⟨y - x, hA, hL, (add_sub_cancel _ _).symm⟩
  · rintro ⟨v, hA, hL, rfl⟩ z
    rw [generalTikhonovObjective_add_of_normal_equation A L b hβ.le x hx v, hA, hL]
    simpa using hmin z

/-- Uniqueness of the actual minimizer is equivalent to triviality of
the common kernel, at every positive parameter and for every data vector.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem generalTikhonov_unique_minimizer_iff (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    (∃! x, ∀ z, generalTikhonovObjective A L b β x ≤ generalTikhonovObjective A L b β z) ↔
      ∀ v : n → 𝕜, A *ᵥ v = 0 → L *ᵥ v = 0 → v = 0 := by
  let x := moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b)
  have hx : ∀ z, generalTikhonovObjective A L b β x ≤ generalTikhonovObjective A L b β z := by
    apply (generalTikhonov_minimizers_iff A L b hβ x).mpr
    exact ⟨0, by simp, by simp, by simp [x]⟩
  constructor
  · rintro ⟨y, hy, hu⟩ v hvA hvL
    have hxy : x = y := hu x hx
    have hv : ∀ z, generalTikhonovObjective A L b β (x + v) ≤
        generalTikhonovObjective A L b β z := by
      apply (generalTikhonov_minimizers_iff A L b hβ (x + v)).mpr
      exact ⟨v, hvA, hvL, rfl⟩
    have hh : x + v = x := (hu _ hv).trans hxy.symm
    exact add_left_cancel (hh.trans (add_zero x).symm)
  · intro hN
    refine ⟨x, hx, ?_⟩
    intro y hy
    obtain ⟨v, hvA, hvL, hv⟩ := (generalTikhonov_minimizers_iff A L b hβ y).mp hy
    simpa only [hN v hvA hvL, add_zero] using hv

end NLAlib
