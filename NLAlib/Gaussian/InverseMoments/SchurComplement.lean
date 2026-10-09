/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_schur_offdiag_inv`, `Sol_GaussianMatrix_regression_residual_indep`).
-/
import NLAlib.Gaussian.InverseMoments
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Covariance

/-!
# Schur complements of the Gram matrix and Gaussian regression

Deterministic and Gaussian facts about one row `g` of a matrix against the remaining rows `H`,
used to compute second moments of the inverse Wishart matrix `(G Gᵀ)⁻¹`.

* `measurable_inv_self_mul_transpose_apply`: the entries of `(G Gᵀ)⁻¹` are measurable in `G`.
* `det_ne_zero_of_rank_eq`: a full-rank square matrix has nonzero determinant.
* `posSemidef_inv_self_mul_transpose`, `abs_apply_le_apply_self_add_apply_self`:
  `(G Gᵀ)⁻¹` is positive semidefinite, so its off-diagonal entries are dominated by the
  diagonal ones.
* `inv_self_mul_transpose_apply_succAbove`: an off-diagonal entry in row `i` of `(G Gᵀ)⁻¹` is
  `-cₐ (G Gᵀ)⁻¹ᵢᵢ`, where `c = (H Hᵀ)⁻¹ H g` are the regression coefficients of row `g = Gᵢ` on
  the other rows `H` (Schur complement; companion of `inv_self_mul_transpose_apply_self`).
* `indepFun_mulVec_sq_dist_rowSpace`: for a standard Gaussian vector `g` and a fixed full-rank
  `H`, the projection data `H g` and the squared residual `‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g)` are
  independent.

Atlas: `inverse-wishart-frob-moment` and `pinv-frob-fourth-moment` (helpers). Proof source:
Prove2me workspace, Gaussian Random Matrices series (`schur_offdiag_inv`,
`regression_residual_indep`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Measurability and positivity of the inverse Gram matrix -/

/-- The entries of `(G Gᵀ)⁻¹` are measurable functions of `G` (with Mathlib's convention
`A⁻¹ = 0` for singular `A`).

Helper for the inverse-Wishart moment computations (Tropp–Webber 2023, App. B). Atlas:
`inverse-wishart-mean` (helper). Ported from the Prove2me solutions of the inverse Wishart
series (`iwd_measurable_inv_entry`). -/
theorem measurable_inv_self_mul_transpose_apply {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

/-- `(G Gᵀ)⁻¹` is positive semidefinite for every real matrix `G`.

Helper for Tropp–Webber 2023, App. B. Atlas: `inverse-wishart-mean` (helper). Ported from the
Prove2me solution `Sol_GaussianMatrix_inverse_wishart_rotation_relation` (`iwr_psd_inv`). -/
theorem posSemidef_inv_self_mul_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) : ((G * Gᵀ)⁻¹).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose G
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.inv

/-- An off-diagonal entry of a real positive semidefinite matrix is dominated by the diagonal:
`|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ`.

Helper for Tropp–Webber 2023, App. B. Atlas: `inverse-wishart-mean` (helper). Ported from the
Prove2me solution `Sol_GaussianMatrix_inverse_wishart_rotation_relation` (`iwr_psd_offdiag`). -/
theorem abs_apply_le_apply_self_add_apply_self {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.PosSemidef) (i j : m) : |M i j| ≤ M i i + M j j := by
  have hs : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  by_cases hij : i = j
  · subst hij
    have := hM.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Matrix.mulVec_single, single_dotProduct,
    hs] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-! ### Off-diagonal Schur complement -/

/-- **Off-diagonal entry of the inverse Gram matrix (Schur complement).** Let `G` have rows
indexed by `Fin (n + 1)`, let `H` be `G` with row `i` removed and `g = G i`. If `H Hᵀ` is
invertible, then for every `a`, `(G Gᵀ)⁻¹ᵢ,ₛ₍ₐ₎ = -cₐ (G Gᵀ)⁻¹ᵢᵢ` with `s = i.succAbove` and
`c = (H Hᵀ)⁻¹ H g` the least-squares coefficients of `g` on the rows of `H`.

Helper for Tropp–Webber 2023, Lemma B.2 (second moments of the inverse Wishart matrix);
companion of `inv_self_mul_transpose_apply_self`. Atlas: `inverse-wishart-frob-moment`
(helper). Ported from Prove2me solution `GaussianMatrix.schur_offdiag_inv` (adjugate
computation). -/
theorem inv_self_mul_transpose_apply_succAbove {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ)
    (i : Fin (n + 1)) (a : Fin n)
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i (i.succAbove a) =
      -(((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)) a) * (G * Gᵀ)⁻¹ i i := by
  set H : Matrix (Fin n) (Fin k) ℝ := G.submatrix i.succAbove id with hHdef
  set g : Fin k → ℝ := G i with hg
  set M : Matrix (Fin n) (Fin n) ℝ := H * Hᵀ with hM
  set c : Fin n → ℝ := M⁻¹ *ᵥ (H *ᵥ g) with hc
  set s : ℝ := g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c with hs
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := G * Gᵀ with hA
  set w : Fin k → ℝ := g - Hᵀ *ᵥ c with hw
  set x : Fin (n + 1) → ℝ := Fin.insertNth i (1 : ℝ) (-c) with hx
  have hHw : H *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH), Matrix.one_mulVec, sub_self]
  have hgw : g ⬝ᵥ w = s := by
    rw [hw, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hGx : Gᵀ *ᵥ x = w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, hx, Pi.sub_apply, hg,
      hHdef, Matrix.submatrix_apply, id]
    rw [Fin.sum_univ_succAbove _ i]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  have hGw : G *ᵥ w = Pi.single i s := by
    funext b
    induction b using Fin.succAboveCases i with
    | x =>
      simp only [Pi.single_eq_same]
      rw [← hgw]; rfl
    | p a =>
      rw [Pi.single_eq_of_ne (Fin.succAbove_ne i a)]
      have := congrFun hHw a
      simpa [Matrix.mulVec, hHdef] using this
  have hAx : A *ᵥ x = Pi.single i s := by
    rw [hA, ← Matrix.mulVec_mulVec, hGx, hGw]
  have hadj : A.adjugate i i = M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have : A.submatrix i.succAbove i.succAbove = M := by
      ext a b
      simp [hA, hM, hHdef, Matrix.mul_apply]
    rw [this, ← two_mul, pow_mul]
    norm_num
  have hdetA : A.det = s * M.det := by
    have h1 : A.adjugate *ᵥ (A *ᵥ x) = A.det • x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hAx] at h1
    have h2 := congrFun h1 i
    have h3 : (A.adjugate *ᵥ Pi.single i s) i = A.adjugate i i * s := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul, hx, Fin.insertNth_apply_same, mul_one, hadj] at h2
    rw [← h2, mul_comm]
  have hAt : Aᵀ = A := by rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hsymm : A⁻¹ i (i.succAbove a) = A⁻¹ (i.succAbove a) i := by
    have : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hAt]
    rw [← this, Matrix.transpose_apply, this]
  by_cases hs0 : s = 0
  · have hA0 : A⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hdetA, hs0, zero_mul]; exact not_isUnit_zero
    show A⁻¹ i (i.succAbove a) = -c a * A⁻¹ i i
    rw [hA0]; simp
  · have hdetU : IsUnit A.det := by
      rw [hdetA]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero hs0 hH)
    have hcol : A⁻¹ *ᵥ Pi.single i s = x := by
      rw [← hAx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
    have hcol' : ∀ b, A⁻¹ b i * s = x b := by
      intro b
      have := congrFun hcol b
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hii : A⁻¹ i i * s = 1 := by
      rw [hcol' i, hx, Fin.insertNth_apply_same]
    have hai : A⁻¹ (i.succAbove a) i * s = -c a := by
      rw [hcol' (i.succAbove a), hx, Fin.insertNth_apply_succAbove, Pi.neg_apply]
    show A⁻¹ i (i.succAbove a) = -c a * A⁻¹ i i
    rw [hsymm]
    have hsinv : A⁻¹ i i = s⁻¹ := by
      field_simp; linarith
    rw [hsinv]
    field_simp
    linarith

/-! ### Independence of the regression and the residual -/

private lemma inner_eq_ofLp_dotProduct' {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- A square real matrix of full rank `n` has nonzero determinant.

Helper (linear algebra) for the inverse-Wishart computations. Atlas: `inverse-wishart-mean`
(helper). Ported from the Prove2me solutions of the inverse Wishart series
(`rri_det_ne_zero_of_rank`). -/
theorem det_ne_zero_of_rank_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  have h1 : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.rank] at h
  simp only [Module.finrank_fin_fun] at h2
  omega

/-- An orthonormal basis `V` of `ker H` (for `H` of full row rank `n`) writes the squared
distance from `g` to the row space of `H` as `‖Vᵀ g‖²`; the columns of `V` are killed by `H`. -/
private lemma exists_orthonormal_ker_sq_dist_rowSpace {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    ∃ V : Matrix (Fin k) (Fin (k - n)) ℝ, Vᵀ * V = 1 ∧
      (∀ j : Fin (k - n), H *ᵥ (fun l => V l j) = 0) ∧ ∀ g : Fin k → ℝ,
      g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) = ∑ j, (Vᵀ *ᵥ g) j ^ 2 := by
  set E := EuclideanSpace ℝ (Fin k)
  set T : E →ₗ[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin H).comp (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap with hT
  set K : Submodule ℝ E := LinearMap.ker T with hK
  have hrange : LinearMap.range T = ⊤ := by
    rw [hT, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hH
  have hfin : Module.finrank ℝ K = k - n := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_euclideanSpace_fin] at h
    rw [hK]; omega
  set b : OrthonormalBasis (Fin (k - n)) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hfin)
  set V : Matrix (Fin k) (Fin (k - n)) ℝ := Matrix.of fun l j => ((b j : K) : E).ofLp l with hV
  have hbK : ∀ j, H *ᵥ ((b j : K) : E).ofLp = 0 := by
    intro j
    have : T ((b j : K) : E) = 0 := LinearMap.mem_ker.mp (b j).2
    exact this
  have hVcol : ∀ (j : Fin (k - n)) (g : Fin k → ℝ), (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ g := by
    intro j g; simp [hV, Matrix.mulVec, dotProduct]
  refine ⟨V, ?_, fun j => hbK j, ?_⟩
  · ext j j'
    have h1 : (Vᵀ * V) j j' = inner ℝ ((b j : K) : E) ((b j' : K) : E) := by
      rw [inner_eq_ofLp_dotProduct']; simp [hV, Matrix.mul_apply, dotProduct]
    rw [h1, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]
  · intro g
    set M := H * Hᵀ with hM
    have hdet : IsUnit M.det := by
      refine isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq _ ?_)
      rw [hM, Matrix.rank_self_mul_transpose, hH]
    set c := M⁻¹ *ᵥ (H *ᵥ g) with hc
    set p := Hᵀ *ᵥ c with hp
    set r := g - p with hr
    have hHr : H *ᵥ r = 0 := by
      rw [hr, Matrix.mulVec_sub, hp, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
    have hq : g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c = r ⬝ᵥ r := by
      have h1 : r ⬝ᵥ p = 0 := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hHr, zero_dotProduct]
      have h2 : g ⬝ᵥ p = (H *ᵥ g) ⬝ᵥ c := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      have h3 : r ⬝ᵥ r = r ⬝ᵥ g - r ⬝ᵥ p := by
        rw [← dotProduct_sub]
      rw [h3, h1, hr, sub_dotProduct, dotProduct_comm p g, h2, sub_zero]
    have hcoord : ∀ j, (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j
      rw [hVcol, hr, dotProduct_sub, hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        hbK, zero_dotProduct, sub_zero]
    have hrK : (WithLp.toLp 2 r : E) ∈ K := by
      simpa [hK, hT] using hHr
    set rK : K := ⟨WithLp.toLp 2 r, hrK⟩
    have hpars := b.sum_inner_mul_inner rK rK
    rw [hq]
    simp_rw [hcoord]
    have hrr : inner ℝ rK rK = r ⬝ᵥ r := by
      rw [Submodule.coe_inner, inner_eq_ofLp_dotProduct']
    have hbj : ∀ j, inner ℝ (b j) rK = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j; rw [Submodule.coe_inner, inner_eq_ofLp_dotProduct']
    rw [← hrr, ← hpars]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, hbj, sq]

open scoped RealInnerProductSpace in
/-- **Independence of Gaussian regression and residual.** Let `H` be a fixed `n × k` matrix of
full row rank and `g` a standard Gaussian vector in `ℝᵏ`. Then `H g` and the squared distance
`‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g)` from `g` to the row space of `H` are independent.

Helper for Tropp–Webber 2023, Lemma B.2 (off-diagonal second moments of `(G Gᵀ)⁻¹`); the
classical independence of the least-squares fit and the residual sum of squares. Atlas:
`inverse-wishart-frob-moment` (helper); the proof uses Gaussian independence from zero
covariance. Ported from Prove2me solution `GaussianMatrix.regression_residual_indep`. -/
theorem indepFun_mulVec_sq_dist_rowSpace {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    IndepFun (fun g : Fin k → ℝ => H *ᵥ g)
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hP
  set E := EuclideanSpace ℝ (Fin k)
  obtain ⟨V, hV, hHV, hq⟩ := exists_orthonormal_ker_sq_dist_rowSpace H hH
  set hrow : Fin n → E := fun a => WithLp.toLp 2 (H a) with hhrow
  set vcol : Fin (k - n) → E := fun j => WithLp.toLp 2 (fun l => V l j) with hvcol
  have : IsGaussian (P.map (WithLp.toLp 2 : (Fin k → ℝ) → E)) := by
    rw [hP, map_pi_eq_stdGaussian]; infer_instance
  have hlaw : HasGaussianLaw (WithLp.toLp 2 : (Fin k → ℝ) → E) P := IsGaussian.hasGaussianLaw
  set L : E →L[ℝ] (Fin n → ℝ) × (Fin (k - n) → ℝ) :=
    (ContinuousLinearMap.pi fun a => innerSL ℝ (hrow a)).prod
      (ContinuousLinearMap.pi fun j => innerSL ℝ (vcol j)) with hL
  have hpair : HasGaussianLaw (fun g : Fin k → ℝ =>
      ((fun a => ⟪hrow a, WithLp.toLp 2 g⟫), (fun j => ⟪vcol j, WithLp.toLp 2 g⟫))) P := by
    have := hlaw.map_fun L
    simpa [hL] using this
  have hcov : ∀ a j, cov[fun g : Fin k → ℝ => ⟪hrow a, WithLp.toLp 2 g⟫,
      fun g => ⟪vcol j, WithLp.toLp 2 g⟫; P] = 0 := by
    intro a j
    have hm : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → E) := by fun_prop
    have h1 := covariance_map_fun (μ := P) (X := fun x : E => ⟪hrow a, x⟫)
      (Y := fun x : E => ⟪vcol j, x⟫) (by fun_prop) (by fun_prop) hm.aemeasurable
    rw [← h1, hP, map_pi_eq_stdGaussian, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, innerSL_apply_apply, inner_eq_ofLp_dotProduct']
    have := congrFun (hHV j) a
    simpa [hhrow, hvcol, Matrix.mulVec, dotProduct] using this
  have hind := hpair.indepFun_of_covariance_eval hcov
  have h1 : (fun g : Fin k → ℝ => fun a => ⟪hrow a, WithLp.toLp 2 g⟫) = fun g => H *ᵥ g := by
    funext g a
    rw [inner_eq_ofLp_dotProduct']; rfl
  have h2 : (fun g : Fin k → ℝ => fun j => ⟪vcol j, WithLp.toLp 2 g⟫) = fun g => Vᵀ *ᵥ g := by
    funext g j
    rw [inner_eq_ofLp_dotProduct']; rfl
  rw [h1, h2] at hind
  have hS : Measurable (fun y : Fin (k - n) → ℝ => ∑ j, y j ^ 2) := by fun_prop
  have := hind.comp measurable_id hS
  have h3 : (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      = (fun y : Fin (k - n) → ℝ => ∑ j, y j ^ 2) ∘ (fun g => Vᵀ *ᵥ g) := funext hq
  rw [h3]
  exact this

end NLAlib
