import NLAlib.Matrix.Spectral
import NLAlib.Matrix.QuadraticProbe
import NLAlib.Matrix.QuadForm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Moments.SubGaussian

/-!
# ε-nets of the sphere and the spectral norm

Deterministic net lemmas (Vershynin 2012, Lem 5.3–5.4; Vershynin 2018, Ex 4.4.3), stated with
`dotProduct` so that the Euclidean geometry is explicit (`ι → ℝ` carries the sup norm):

* `specNorm_le_of_forall_sqrt_le`: `‖A‖ ≤ K` from `‖Ay‖ ≤ K` on unit vectors;
* `specNorm_le_div_of_net`: `‖A‖ ≤ M/(1-ε)` from `‖Ax‖ ≤ M` on an ε-net;
* `specNorm_le_div_of_net_bilinear`: `‖A‖ ≤ M/(1-2ε)` from `yᵀAx ≤ M` on two ε-nets;
* `specNorm_le_div_of_net_quadForm`: `‖B‖ ≤ M/(1-2ε)` from `|xᵀBx| ≤ M` on an ε-net, `B`
  symmetric;
* `exists_finset_sphere_net`: the unit sphere of `ℝ^ι` has an ε-net of at most
  `(1 + 2/ε)^{card ι}` unit vectors (volumetric argument; Vershynin 2018, Cor 4.2.13);
* `exists_finset_net_specNorm_le`: the full `epsilon-net-norm` statement;
* `measure_lt_specNorm_le_of_hasSubgaussianMGF`: tail of `‖A‖₂` for a random matrix with
  sub-Gaussian bilinear marginals (Vershynin 2018, Thm 4.4.5, explicit constants).

Atlas `epsilon-net-norm`, `subgaussian-spec-norm` (new). Audit G1 C8, A1, B1, B2.
-/

open MeasureTheory Metric ProbabilityTheory
open scoped NNReal
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Euclidean-norm bridges -/

omit [DecidableEq n] in
private lemma norm_toLp_eq_sqrt (v : n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ n)‖ = √(v ⬝ᵥ v) := by
  rw [norm_eq_sqrt_dotProduct]

private lemma norm_toLp_mulVec_le (A : Matrix m n ℝ) (x : n → ℝ) :
    ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ m)‖ ≤
      specNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  simpa [specNorm_eq_norm] using A.l2_opNorm_mulVec (WithLp.toLp 2 x)

/-- `‖A y‖₂ ≤ ‖A‖₂ ‖y‖₂`, written with `dotProduct`. Atlas `norms-frob-spec`. -/
theorem sqrt_mulVec_dotProduct_le (A : Matrix m n ℝ) (y : n → ℝ) :
    √((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ specNorm A * √(y ⬝ᵥ y) := by
  rw [← norm_toLp_eq_sqrt, ← norm_toLp_eq_sqrt]
  exact norm_toLp_mulVec_le A y

/-- `|uᵀ A x| ≤ ‖u‖₂ ‖A‖₂ ‖x‖₂`. Atlas `norms-frob-spec`. -/
theorem abs_dotProduct_mulVec_le (A : Matrix m n ℝ) (u : m → ℝ) (x : n → ℝ) :
    |u ⬝ᵥ (A *ᵥ x)| ≤ √(u ⬝ᵥ u) * (specNorm A * √(x ⬝ᵥ x)) := by
  have hcs := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ m)
    (WithLp.toLp 2 (A *ᵥ x))
  have hi : inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ m) (WithLp.toLp 2 (A *ᵥ x)) =
      u ⬝ᵥ (A *ᵥ x) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hi] at hcs
  calc |u ⬝ᵥ (A *ᵥ x)| ≤ _ := hcs
    _ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ m)‖ *
          (specNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖) := by
        gcongr
        exact norm_toLp_mulVec_le A x
    _ = _ := by rw [norm_toLp_eq_sqrt, norm_toLp_eq_sqrt]

/-- The spectral norm is at most `K ≥ 0` as soon as `‖A y‖₂ ≤ K` for every unit vector `y`.
Atlas `epsilon-net-norm` (helper). -/
theorem specNorm_le_of_forall_sqrt_le (A : Matrix m n ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ y : n → ℝ, y ⬝ᵥ y = 1 → √((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ K) : specNorm A ≤ K := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  let y : n → ℝ := ‖x‖⁻¹ • x.ofLp
  have hy : y ⬝ᵥ y = 1 := by
    have h1 : √(x.ofLp ⬝ᵥ x.ofLp) = ‖x‖ := (norm_eq_sqrt_dotProduct x).symm
    have h2 : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
      rw [← h1, Real.sq_sqrt (dotProduct_self_nonneg _)]
    simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul, h2]
    field_simp
  have hAy := h y hy
  rw [← norm_toLp_eq_sqrt] at hAy
  have hscale : (WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ m) =
      ‖x‖⁻¹ • (WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ m) := by
    simp only [y, Matrix.mulVec_smul]
    rfl
  rw [hscale, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hxn] at hAy
  linarith [mul_comm K ‖x‖]

/-- A symmetric matrix on a nonempty index type has a unit vector `v` (an eigenvector of the
eigenvalue of largest modulus) with `|vᵀ B v| = ‖B‖₂`. Horn–Johnson Thm 4.2.2 (Rayleigh);
atlas `epsilon-net-norm` (helper). -/
theorem exists_unit_abs_quadForm_eq_specNorm [Nonempty n] {B : Matrix n n ℝ} (hB : B.IsSymm) :
    ∃ v : n → ℝ, v ⬝ᵥ v = 1 ∧ |quadForm B v| = specNorm B := by
  have hH : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hH.eigenvalues).1
  dsimp only at hi
  let v : n → ℝ := (hH.eigenvectorBasis i).ofLp
  have hv : v ⬝ᵥ v = 1 := by
    have hn := hH.eigenvectorBasis.orthonormal.1 i
    have hs := congrArg (fun t : ℝ => t ^ 2) hn
    rw [norm_eq_sqrt_dotProduct, Real.sq_sqrt (dotProduct_self_nonneg _), one_pow] at hs
    exact hs
  refine ⟨v, hv, ?_⟩
  have hBv : B *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
  rw [quadForm, hBv, dotProduct_smul, hv, smul_eq_mul, mul_one, specNorm_eq_norm_eigenvalues hH,
    ← hi, Real.norm_eq_abs]

/-! ### Deterministic net lemmas -/

/-- **Spectral norm from a net (operator form).** If `N` is an `ε`-net of the unit sphere
(`∀ y` unit, `∃ x ∈ N`, `‖x - y‖₂ ≤ ε`) with `0 ≤ ε < 1`, and `‖Ax‖₂ ≤ M` for every `x ∈ N`
(`M ≥ 0`), then `‖A‖₂ ≤ M/(1-ε)`. The net points need not be unit vectors. `hM0` is needed:
for an empty index type `N` may be empty and `M` negative.
Vershynin 2012, Lem 5.3 (i); Vershynin 2018, Ex 4.4.3; audit G1 C8. Atlas `epsilon-net-norm`
(deterministic half).
atlas: epsilon-net-norm -/
theorem specNorm_le_div_of_net (A : Matrix m n ℝ) (N : Finset (n → ℝ)) {ε M : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hM0 : 0 ≤ M)
    (hN : ∀ y : n → ℝ, y ⬝ᵥ y = 1 → ∃ x ∈ N, (x - y) ⬝ᵥ (x - y) ≤ ε ^ 2)
    (hM : ∀ x ∈ N, √((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤ M) :
    specNorm A ≤ M / (1 - ε) := by
  have hB := specNorm_nonneg A
  have key : specNorm A ≤ M + specNorm A * ε := by
    refine specNorm_le_of_forall_sqrt_le A (by positivity) fun y hy => ?_
    obtain ⟨x, hxN, hxy⟩ := hN y hy
    have hd : √((x - y) ⬝ᵥ (x - y)) ≤ ε := by
      rw [Real.sqrt_le_left hε0]; exact hxy
    rw [← norm_toLp_eq_sqrt]
    have hsplit : (WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ m) =
        WithLp.toLp 2 (A *ᵥ x) - WithLp.toLp 2 (A *ᵥ (x - y)) := by
      rw [Matrix.mulVec_sub, ← WithLp.toLp_sub, sub_sub_cancel]
    rw [hsplit]
    calc _ ≤ ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ m)‖ +
          ‖(WithLp.toLp 2 (A *ᵥ (x - y)) : EuclideanSpace ℝ m)‖ := norm_sub_le _ _
      _ ≤ M + specNorm A * ε := by
        gcongr
        · rw [norm_toLp_eq_sqrt]; exact hM x hxN
        · calc _ ≤ specNorm A * ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ n)‖ :=
                norm_toLp_mulVec_le A _
            _ ≤ specNorm A * ε := by rw [norm_toLp_eq_sqrt]; gcongr
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Spectral norm from two nets (bilinear form).** If `N` and `N'` are `ε`-nets of the unit
spheres of `ℝⁿ` and `ℝᵐ`, the points of `N'` being unit vectors, `0 ≤ ε < 1/2`, and `yᵀ A x ≤ M` for all
`x ∈ N`, `y ∈ N'` (`M ≥ 0`), then `‖A‖₂ ≤ M/(1-2ε)`.
Vershynin 2012, Lem 5.4 (bilinear form); Vershynin 2018, Ex 4.4.3 (b); audit G1 C8.
Atlas `epsilon-net-norm` (deterministic half).
atlas: epsilon-net-norm -/
theorem specNorm_le_div_of_net_bilinear (A : Matrix m n ℝ) (N : Finset (n → ℝ))
    (N' : Finset (m → ℝ)) {ε M : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (hM0 : 0 ≤ M)
    (hN'unit : ∀ y ∈ N', y ⬝ᵥ y = 1)
    (hN : ∀ x : n → ℝ, x ⬝ᵥ x = 1 → ∃ x₀ ∈ N, (x₀ - x) ⬝ᵥ (x₀ - x) ≤ ε ^ 2)
    (hN' : ∀ y : m → ℝ, y ⬝ᵥ y = 1 → ∃ y₀ ∈ N', (y₀ - y) ⬝ᵥ (y₀ - y) ≤ ε ^ 2)
    (hM : ∀ x ∈ N, ∀ y ∈ N', y ⬝ᵥ (A *ᵥ x) ≤ M) :
    specNorm A ≤ M / (1 - 2 * ε) := by
  have hB := specNorm_nonneg A
  -- every unit pair satisfies `yᵀ A x ≤ M + 2 ε ‖A‖`
  have hpair : ∀ x : n → ℝ, x ⬝ᵥ x = 1 → ∀ y : m → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (A *ᵥ x) ≤ M + 2 * ε * specNorm A := by
    intro x hx y hy
    obtain ⟨x₀, hx₀N, hx₀⟩ := hN x hx
    obtain ⟨y₀, hy₀N, hy₀⟩ := hN' y hy
    have hdx : √((x₀ - x) ⬝ᵥ (x₀ - x)) ≤ ε := by rw [Real.sqrt_le_left hε0]; exact hx₀
    have hdy : √((y₀ - y) ⬝ᵥ (y₀ - y)) ≤ ε := by rw [Real.sqrt_le_left hε0]; exact hy₀
    have hsplit : y ⬝ᵥ (A *ᵥ x) = y₀ ⬝ᵥ (A *ᵥ x₀) - (y₀ - y) ⬝ᵥ (A *ᵥ x) -
        y₀ ⬝ᵥ (A *ᵥ (x₀ - x)) := by
      simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
      ring
    have h1 := abs_dotProduct_mulVec_le A (y₀ - y) x
    have h2 := abs_dotProduct_mulVec_le A y₀ (x₀ - x)
    rw [hx, Real.sqrt_one, mul_one] at h1
    rw [hN'unit y₀ hy₀N, Real.sqrt_one, one_mul] at h2
    have h1' : |(y₀ - y) ⬝ᵥ (A *ᵥ x)| ≤ ε * specNorm A :=
      h1.trans (by nlinarith)
    have h2' : |y₀ ⬝ᵥ (A *ᵥ (x₀ - x))| ≤ ε * specNorm A :=
      h2.trans (by nlinarith)
    rw [hsplit]
    have := hM x₀ hx₀N y₀ hy₀N
    linarith [neg_abs_le ((y₀ - y) ⬝ᵥ (A *ᵥ x)), neg_abs_le (y₀ ⬝ᵥ (A *ᵥ (x₀ - x)))]
  have key : specNorm A ≤ M + 2 * ε * specNorm A := by
    refine specNorm_le_of_forall_sqrt_le A (by positivity) fun x hx => ?_
    set v := A *ᵥ x
    rcases (dotProduct_self_nonneg v).eq_or_lt with h0 | hpos
    · rw [← h0, Real.sqrt_zero]; positivity
    have hs : 0 < √(v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
    let y : m → ℝ := (√(v ⬝ᵥ v))⁻¹ • v
    have hy : y ⬝ᵥ y = 1 := by
      simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    have hyv : y ⬝ᵥ v = √(v ⬝ᵥ v) := by
      simp only [y, smul_dotProduct, smul_eq_mul]
      rw [inv_mul_eq_div, div_eq_iff hs.ne', Real.mul_self_sqrt hpos.le]
    rw [← hyv]
    exact hpair x hx y hy
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Spectral norm of a symmetric matrix from a net (quadratic form).** If `B` is symmetric,
`N` is an `ε`-net of the unit sphere made of unit vectors, `0 ≤ ε < 1/2`, and
`|xᵀ B x| ≤ M` for every `x ∈ N`, then `‖B‖₂ ≤ M/(1-2ε)`.
Vershynin 2012, Lem 5.4; Vershynin 2018, Ex 4.4.3 (c); audit G1 C8. Atlas `epsilon-net-norm`
(deterministic half).
atlas: epsilon-net-norm -/
theorem specNorm_le_div_of_net_quadForm {B : Matrix n n ℝ} (hB : B.IsSymm)
    (N : Finset (n → ℝ)) {ε M : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (hM0 : 0 ≤ M)
    (hNunit : ∀ x ∈ N, x ⬝ᵥ x = 1)
    (hN : ∀ y : n → ℝ, y ⬝ᵥ y = 1 → ∃ x ∈ N, (x - y) ⬝ᵥ (x - y) ≤ ε ^ 2)
    (hM : ∀ x ∈ N, |quadForm B x| ≤ M) :
    specNorm B ≤ M / (1 - 2 * ε) := by
  have hBn := specNorm_nonneg B
  have hunit : ∀ y : n → ℝ, y ⬝ᵥ y = 1 → |quadForm B y| ≤ M + 2 * ε * specNorm B := by
    intro y hy
    obtain ⟨x, hxN, hxy⟩ := hN y hy
    have hd : √((x - y) ⬝ᵥ (x - y)) ≤ ε := by rw [Real.sqrt_le_left hε0]; exact hxy
    have hsplit : quadForm B y = quadForm B x - (x - y) ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ (x - y)) := by
      simp only [quadForm, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
      ring
    have h1 := abs_dotProduct_mulVec_le B (x - y) x
    have h2 := abs_dotProduct_mulVec_le B y (x - y)
    rw [hNunit x hxN, Real.sqrt_one, mul_one] at h1
    rw [hy, Real.sqrt_one, one_mul] at h2
    have h1' : |(x - y) ⬝ᵥ (B *ᵥ x)| ≤ ε * specNorm B := h1.trans (by nlinarith)
    have h2' : |y ⬝ᵥ (B *ᵥ (x - y))| ≤ ε * specNorm B := h2.trans (by nlinarith)
    rw [hsplit]
    have := hM x hxN
    have := abs_sub (quadForm B x - (x - y) ⬝ᵥ (B *ᵥ x)) (y ⬝ᵥ (B *ᵥ (x - y)))
    have := abs_sub (quadForm B x) ((x - y) ⬝ᵥ (B *ᵥ x))
    linarith
  have key : specNorm B ≤ M + 2 * ε * specNorm B := by
    rcases isEmpty_or_nonempty n with hn | hn
    · have : B = 0 := Subsingleton.elim _ _
      rw [this, specNorm_eq_norm, norm_zero]; positivity
    obtain ⟨v, hv, heig⟩ := exists_unit_abs_quadForm_eq_specNorm hB
    exact heig.symm.le.trans (hunit v hv)
  rw [le_div_iff₀ (by linarith)]
  linarith

/-! ### Volumetric ε-net of the sphere -/

/-- Volumetric packing bound: an `ε`-separated finite subset of the unit sphere of
`EuclideanSpace ℝ ι` has at most `(1 + 2/ε)^{card ι}` points (the disjoint balls of radius `ε/2`
fit in the ball of radius `1 + ε/2`). -/
private theorem card_le_of_separated {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : Finset (EuclideanSpace ℝ ι)) {ε : ℝ} (hε : 0 < ε) (hS : ∀ x ∈ S, ‖x‖ = 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) :
    (S.card : ℝ) ≤ (1 + 2 / ε) ^ Fintype.card ι := by
  set d := Fintype.card ι
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ ι) = d := finrank_euclideanSpace
  set V := (volume : Measure (EuclideanSpace ℝ ι)) (ball 0 1)
  have hV0 : V ≠ 0 := (measure_ball_pos volume (0 : EuclideanSpace ℝ ι) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hdisj : (S : Set (EuclideanSpace ℝ ι)).PairwiseDisjoint fun x => ball x (ε / 2) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ x ∈ S, ball x (ε / 2)) ⊆ ball (0 : EuclideanSpace ℝ ι) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball] at hz
    calc ‖z‖ ≤ ‖x‖ + dist z x := by
          rw [dist_eq_norm]; linarith [norm_le_insert' z x, norm_sub_rev z x]
      _ < 1 + ε / 2 := by rw [hS x hx]; linarith
  have hmeas := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ ι))) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hmeas
  simp only [Measure.addHaar_ball _ _ (by positivity : (0 : ℝ) ≤ ε / 2),
    Measure.addHaar_ball _ _ (by positivity : (0 : ℝ) ≤ 1 + ε / 2), hfin,
    Finset.sum_const, nsmul_eq_mul] at hmeas
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hpos : (0 : ℝ) < (ε / 2) ^ d := by positivity
  rw [← le_div_iff₀ hpos, ← div_pow] at h2
  calc (S.card : ℝ) ≤ ((1 + ε / 2) / (ε / 2)) ^ d := h2
    _ = (1 + 2 / ε) ^ d := by congr 1; field_simp; ring

/-- **Volumetric ε-net of the sphere.** For `ε > 0`, the unit sphere of `ℝ^ι` (Euclidean) has an
`ε`-net contained in the sphere with at most `(1 + 2/ε)^{card ι}` points:
`∀ y` with `yᵀy = 1`, `∃ x ∈ N`, `(x - y)ᵀ(x - y) ≤ ε²`. For an empty index type the sphere is
empty and `N = ∅`. Proof: a maximal `ε`-separated subset of the sphere is an `ε`-net, and the
volumetric packing bound caps the size of every separated subset.
Vershynin 2012, Lem 5.2; Vershynin 2018, Cor 4.2.13; audit G1 A1. Atlas `epsilon-net-norm`
(covering half). Deviation: index type any `[Fintype ι]` (audit: `Fin n`).
atlas: epsilon-net-norm -/
theorem exists_finset_sphere_net (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset (ι → ℝ), (∀ x ∈ N, x ⬝ᵥ x = 1) ∧
      (N.card : ℝ) ≤ (1 + 2 / ε) ^ Fintype.card ι ∧
      ∀ y : ι → ℝ, y ⬝ᵥ y = 1 → ∃ x ∈ N, (x - y) ⬝ᵥ (x - y) ≤ ε ^ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨∅, by simp, by simp, fun y hy => ?_⟩
    simp [dotProduct] at hy
  -- a separated subset of the sphere that is also a cover
  have hcov : ∃ S : Finset (EuclideanSpace ℝ ι), (∀ x ∈ S, ‖x‖ = 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) ∧
      ∀ y : EuclideanSpace ℝ ι, ‖y‖ = 1 → ∃ x ∈ S, dist x y ≤ ε := by
    by_contra hne
    push Not at hne
    have hall : ∀ k : ℕ, ∃ S : Finset (EuclideanSpace ℝ ι), (∀ x ∈ S, ‖x‖ = 1) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) ∧ S.card = k := by
      intro k
      induction k with
      | zero => exact ⟨∅, by simp, by simp, rfl⟩
      | succ k ih =>
        obtain ⟨S, hS1, hS2, hS3⟩ := ih
        obtain ⟨y, hy1, hy2⟩ := hne S hS1 hS2
        have hyS : y ∉ S := fun hyS => by
          have := hy2 y hyS
          rw [dist_self] at this
          linarith
        refine ⟨insert y S, ?_, ?_, by rw [Finset.card_insert_of_notMem hyS, hS3]⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hy1
          · exact hS1 x hx
        · intro a ha b hb hab
          rcases Finset.mem_insert.1 ha with rfl | ha' <;>
            rcases Finset.mem_insert.1 hb with rfl | hb'
          · exact absurd rfl hab
          · rw [dist_comm]; exact hy2 b hb'
          · exact hy2 a ha'
          · exact hS2 a ha' b hb' hab
    obtain ⟨S, hS1, hS2, hS3⟩ := hall (⌊(1 + 2 / ε) ^ Fintype.card ι⌋₊ + 1)
    have hb := card_le_of_separated S hε hS1 hS2
    rw [hS3] at hb
    have := Nat.lt_floor_add_one ((1 + 2 / ε) ^ Fintype.card ι)
    push_cast at hb
    linarith
  obtain ⟨S, hS1, hS2, hS3⟩ := hcov
  have hnorm : ∀ v : ι → ℝ, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := by
    intro v
    rw [norm_eq_sqrt_dotProduct, Real.sq_sqrt (dotProduct_self_nonneg _)]
  refine ⟨S.image WithLp.ofLp, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
    rw [← hnorm, WithLp.toLp_ofLp, hS1 z hz, one_pow]
  · exact (Nat.cast_le.2 Finset.card_image_le).trans (card_le_of_separated S hε hS1 hS2)
  · intro y hy
    have hy1 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖ = 1 := by
      have := hnorm y
      rw [hy] at this
      nlinarith [norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℝ ι)]
    obtain ⟨x, hx, hxy⟩ := hS3 _ hy1
    refine ⟨x.ofLp, Finset.mem_image_of_mem _ hx, ?_⟩
    rw [← hnorm, WithLp.toLp_sub, WithLp.toLp_ofLp, ← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg hxy 2

/-! ### The ε-net bound for the spectral norm and sub-Gaussian matrices -/

/-- **ε-net bound for the spectral norm.** For `0 < ε < 1` there is a set `N` of at most
`(1 + 2/ε)^{card n}` unit vectors of `ℝ^n` such that for every real matrix `A` with `n` columns
and every `M ≥ 0`, `‖Ax‖₂ ≤ M` on `N` implies `‖A‖₂ ≤ M/(1-ε)`.
Vershynin 2012, Lem 5.2–5.3; Vershynin 2018, Cor 4.2.13 and Ex 4.4.3; audit G1 B1.
Atlas `epsilon-net-norm`. Deviation: the atlas states `(1-2ε)⁻¹`; the standard (and stronger)
operator form `(1-ε)⁻¹` is used here, the `(1-2ε)⁻¹` forms being
`specNorm_le_div_of_net_bilinear` and `specNorm_le_div_of_net_quadForm`.
atlas: epsilon-net-norm -/
theorem exists_finset_net_specNorm_le (n : Type*) [Fintype n] [DecidableEq n] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N : Finset (n → ℝ), (∀ x ∈ N, x ⬝ᵥ x = 1) ∧
      (N.card : ℝ) ≤ (1 + 2 / ε) ^ Fintype.card n ∧
      ∀ (m : Type*) [Fintype m] [DecidableEq m] (A : Matrix m n ℝ) (M : ℝ), 0 ≤ M →
        (∀ x ∈ N, √((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤ M) → specNorm A ≤ M / (1 - ε) := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_finset_sphere_net n hε0
  exact ⟨N, hN1, hN2, fun m _ _ A M hM0 hM =>
    specNorm_le_div_of_net A N hε0.le hε1 hM0 hN3 hM⟩

/-- **Spectral norm of a matrix with sub-Gaussian bilinear marginals.** If
`yᵀ A x` is sub-Gaussian with proxy `c` for all unit `x ∈ ℝⁿ`, `y ∈ ℝᵐ` (no independence is
assumed), then for `t ≥ 0`,
`P(‖A‖₂ > 2(√(2 log 9 · (m + n) c) + √c t)) ≤ e^{-t²/2}`.
The inequality is strict: with `≤` the statement fails for `c = 0`.
Vershynin 2018, Thm 4.4.5 (with explicit constants: 1/4-nets of size `9ⁿ`, `9ᵐ`, the bilinear
net lemma and a union bound); audit G1 B2. Atlas `subgaussian-spec-norm` (new). No
measurability hypothesis is needed (outer measure).
atlas: subgaussian-spec-norm -/
theorem measure_lt_specNorm_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Ω → Matrix m n ℝ) (c : ℝ≥0)
    (hA : ∀ (x : n → ℝ) (y : m → ℝ), x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
      HasSubgaussianMGF (fun ω => y ⬝ᵥ (A ω *ᵥ x)) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 2 * (√(2 * Real.log 9 * (Fintype.card m + Fintype.card n) * c) + √c * t) <
        specNorm (A ω)} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  classical
  set a := √(2 * Real.log 9 * (Fintype.card m + Fintype.card n) * c) with ha
  set u := a + √c * t with hu
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_finset_sphere_net n (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨N', hN'1, hN'2, hN'3⟩ := exists_finset_sphere_net m (show (0 : ℝ) < 1 / 4 by norm_num)
  have h9 : (1 + 2 / (1 / 4 : ℝ)) = 9 := by norm_num
  rw [h9] at hN2 hN'2
  -- the event is covered by the union of the bilinear events over the nets
  have hsub : {ω | 2 * u < specNorm (A ω)} ⊆
      ⋃ x ∈ N, ⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    have := specNorm_le_div_of_net_bilinear (A ω) N N' (by norm_num) (by norm_num) hu0 hN'1
      hN3 hN'3 fun x hx y hy => hnot x hx y hy
    rw [Set.mem_ofPred_eq] at hω
    have h2 : u / (1 - 2 * (1 / 4 : ℝ)) = 2 * u := by ring
    linarith
  have hunion : μ {ω | 2 * u < specNorm (A ω)} ≤
      ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} :=
    calc μ {ω | 2 * u < specNorm (A ω)}
        ≤ μ (⋃ x ∈ N, ⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)}) := measure_mono hsub
      _ ≤ ∑ x ∈ N, μ (⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} :=
          Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
  refine hunion.trans ?_
  rcases eq_or_ne c 0 with hc | hc
  · -- `c = 0`: every bilinear marginal vanishes a.s.
    subst hc
    have hzero : ∀ x ∈ N, ∀ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} = 0 := by
      intro x hx y hy
      have h0 := (hA x y (hN1 x hx) (hN'1 y hy)).ae_eq_zero_of_hasSubgaussianMGF_zero
      have hu' : u = 0 := by simp [hu, ha]
      apply measure_mono_null (t := {ω | (fun ω => y ⬝ᵥ (A ω *ᵥ x)) ω ≠ (0 : Ω → ℝ) ω})
      · intro ω hω h
        simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hω h
        linarith
      · exact ae_iff.1 h0
    rw [Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => hzero x hx y hy]
    exact zero_le
  have hc0 : (0 : ℝ) < c := lt_of_le_of_ne c.2 (by exact_mod_cast hc.symm)
  have hterm : ∀ x ∈ N, ∀ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} ≤
      ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * c))) := by
    intro x hx y hy
    have hsg := hA x y (hN1 x hx) (hN'1 y hy)
    calc μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} ≤ μ {ω | u ≤ y ⬝ᵥ (A ω *ᵥ x)} :=
          measure_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω ⊢; exact hω.le
      _ = ENNReal.ofReal (μ.real {ω | u ≤ y ⬝ᵥ (A ω *ᵥ x)}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsg.measure_ge_le hu0)
  -- the union bound
  set k : ℕ := Fintype.card m + Fintype.card n with hk
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have ha2 : a ^ 2 = 2 * Real.log 9 * k * c := by
    rw [ha, Real.sq_sqrt (by positivity), hk]; push_cast; ring
  have hsc : √(c : ℝ) ^ 2 = c := Real.sq_sqrt c.2
  have hu2 : 2 * Real.log 9 * k * c + c * t ^ 2 ≤ u ^ 2 := by
    have : u ^ 2 = a ^ 2 + 2 * a * (√c * t) + √(c : ℝ) ^ 2 * t ^ 2 := by rw [hu]; ring
    rw [this, ha2, hsc]
    nlinarith [mul_nonneg (mul_nonneg ha0 (Real.sqrt_nonneg (c : ℝ))) ht]
  have hexp : Real.exp (-u ^ 2 / (2 * c)) ≤
      Real.exp (-(k * Real.log 9)) * Real.exp (-t ^ 2 / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcard : (N.card : ℝ) * N'.card ≤ Real.exp (k * Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num), hk, pow_add, mul_comm]
    exact mul_le_mul hN'2 hN2 (by positivity) (by positivity)
  have hrhs : (N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c)) ≤ Real.exp (-t ^ 2 / 2) := by
    calc (N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c))
        ≤ Real.exp (k * Real.log 9) * (Real.exp (-(k * Real.log 9)) * Real.exp (-t ^ 2 / 2)) :=
          mul_le_mul hcard hexp (by positivity) (by positivity)
      _ = Real.exp (-t ^ 2 / 2) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  calc ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)}
      ≤ ∑ x ∈ N, ∑ y ∈ N', ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * c))) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
    _ = ENNReal.ofReal ((N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrhs

end NLAlib
