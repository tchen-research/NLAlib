import NLAlib.Matrix.Functions.ExtremeEigenvalues
import NLAlib.Matrix.Basic.QuadForm
/-!+# Smallest Hermitian eigenvalue: attained minimum and equality

The minimum uses every domain-side Gram eigenvalue, including zeros for
wide or deficient matrices. Its nonnegative shifted form identifies the
entire minimum eigenspace, including repeated minimum eigenvalues.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Subtracting the smallest Hermitian eigenvalue yields a PSD matrix. -/
theorem _root_.Matrix.IsHermitian.posSemidef_sub_lambdaMin_smul_one [Nonempty n]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    (H - (lambdaMin H : 𝕜) • 1).PosSemidef := by
  let U : Matrix n n 𝕜 := hH.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hD : H = U * diagonal (fun i => (hH.eigenvalues i : 𝕜)) * Uᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hH.spectral_theorem
  have hmin (i : n) : lambdaMin H ≤ hH.eigenvalues i := by
    exact csInf_le (Set.toFinite (spectrum ℝ H)).bddBelow (hH.eigenvalues_mem_spectrum_real i)
  have hpos : (diagonal (fun i => ((hH.eigenvalues i - lambdaMin H : ℝ) : 𝕜))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : 𝕜) ≤ ((hH.eigenvalues i - lambdaMin H : ℝ) : 𝕜)
      exact_mod_cast sub_nonneg.mpr (hmin i))
  have he : H - (lambdaMin H : 𝕜) • 1 =
      U * diagonal (fun i => ((hH.eigenvalues i - lambdaMin H : ℝ) : 𝕜)) * Uᴴ := by
    rw [show diagonal (fun i => ((hH.eigenvalues i - lambdaMin H : ℝ) : 𝕜)) =
        diagonal (fun i => (hH.eigenvalues i : 𝕜)) - (lambdaMin H : 𝕜) • 1 by
          ext i j; by_cases hij : i = j <;>
            simp [Matrix.diagonal_apply, Matrix.one_apply, hij, smul_eq_mul,
              RCLike.real_smul_eq_coe_mul]]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU, ← hD]
  rw [he]
  exact hpos.mul_mul_conjTranspose_same U

/-- Every Hermitian matrix has a unit smallest-eigenvalue vector. -/
theorem _root_.Matrix.IsHermitian.exists_unit_lambdaMin_eigenvector [Nonempty n]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∃ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ H *ᵥ v = (lambdaMin H : 𝕜) • v := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let j : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt Fintype.card_pos⟩
  have he : hH.eigenvalues (e j) = lambdaMin H := by
    rw [lambdaMin_eq_eigenvalues₀_last hH]
    simp [Matrix.IsHermitian.eigenvalues, e, j]
  refine ⟨⇑(hH.eigenvectorBasis (e j)), hH.eigenvectorBasis.orthonormal.norm_eq_one _, ?_⟩
  have hh := hH.mulVec_eigenvectorBasis (e j)
  rw [he] at hh
  ext i
  simpa only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul] using congrFun hh i

/-- A shift strictly below the smallest Hermitian eigenvalue is positive
definite. This applies in particular to strict-gap TLS normal matrices. -/
theorem _root_.Matrix.IsHermitian.posDef_sub_smul_one_of_lt_lambdaMin [Nonempty n]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {a : ℝ} (ha : a < lambdaMin H) :
    (H - (a : 𝕜) • 1).PosDef := by
  have hp := Matrix.PosDef.posSemidef_add hH.posSemidef_sub_lambdaMin_smul_one
    (Matrix.PosDef.one.smul (sub_pos.mpr ha))
  convert hp using 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, RCLike.real_smul_eq_coe_mul, map_sub]
    ring
  · simp [Matrix.one_apply, hij]

/-- The Gram Rayleigh defect is exactly the shifted PSD quadratic. -/
theorem re_quadForm_gram_sub_lambdaMin (C : Matrix m n 𝕜) (v : n → 𝕜) :
    RCLike.re (quadForm (Cᴴ * C - (lambdaMin (Cᴴ * C) : 𝕜) • 1) v) =
      ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 - lambdaMin (Cᴴ * C) * ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp only [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, map_sub, smul_eq_mul, RCLike.re_ofReal_mul,
    norm_toLp_sq_eq_re_star_dotProduct]
  rw [← quadForm, quadForm_conjTranspose_mul_self]

/-- The least Gram eigenvalue bounds every unit-direction residual. -/
theorem lambdaMin_gram_le_norm_mulVec_sq [Nonempty n] (C : Matrix m n 𝕜)
    {v : n → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    lambdaMin (Cᴴ * C) ≤ ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 := by
  have hp := (Matrix.isHermitian_conjTranspose_mul_self C).posSemidef_sub_lambdaMin_smul_one
  have hn := hp.re_quadForm_nonneg v
  rw [re_quadForm_gram_sub_lambdaMin, hv, one_pow, mul_one] at hn
  linarith

/-- Equality in the unit Rayleigh lower bound identifies the entire
minimum eigenspace, with no simplicity assumption. -/
theorem norm_mulVec_sq_eq_lambdaMin_gram_iff [Nonempty n] (C : Matrix m n 𝕜)
    {v : n → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 = lambdaMin (Cᴴ * C) ↔
      (Cᴴ * C) *ᵥ v = (lambdaMin (Cᴴ * C) : 𝕜) • v := by
  let H := Cᴴ * C - (lambdaMin (Cᴴ * C) : 𝕜) • 1
  have hp : H.PosSemidef :=
    (Matrix.isHermitian_conjTranspose_mul_self C).posSemidef_sub_lambdaMin_smul_one
  have he : RCLike.re (quadForm H v) = ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 - lambdaMin (Cᴴ * C) := by
    rw [re_quadForm_gram_sub_lambdaMin, hv, one_pow, mul_one]
  have hzero : quadForm H v = 0 ↔ RCLike.re (quadForm H v) = 0 := by
    constructor
    · intro hh; rw [hh, map_zero]
    · intro hh; rw [← hp.isHermitian.ofReal_re_quadForm v, hh, RCLike.ofReal_zero]
  rw [← sub_eq_zero, ← he, ← hzero, quadForm,
    hp.dotProduct_mulVec_zero_iff]
  simp only [H, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

end NLAlib
