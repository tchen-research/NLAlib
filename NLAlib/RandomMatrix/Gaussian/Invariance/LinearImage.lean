import NLAlib.RandomMatrix.Gaussian.Invariance.Invariance
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import Mathlib.Probability.Moments.SubGaussian

/-!
# Linear images of a standard Gaussian matrix

Laws of `Gᵀ`, `G U` and `G x` for a standard Gaussian matrix `G` (`NLAlib.gaussianMatrix`):

* `hasLaw_gaussianMatrix_transpose`: `Gᵀ` is a standard Gaussian matrix (transposition permutes
  the coordinates of an i.i.d. product);
* `hasLaw_gaussianMatrix_mul_right`: for `U` with orthonormal columns, `G U` is a standard
  Gaussian matrix (the right-hand counterpart of `hasLaw_gaussianMatrix_block`, via
  `G U = (Uᵀ Gᵀ)ᵀ`); both with `_of_hasLaw` forms for a random matrix;
* `gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one`: for a unit vector `x`, `G x` is a
  standard Gaussian vector;
* `gaussianMatrix_map_mulVec`: for any `x`, `G x ∼ N(0, ‖x‖² I)`;
* `hasSubgaussianMGF_mulVec_apply_gaussianMatrix`: each coordinate of `G x` is sub-Gaussian with
  proxy `‖x‖²` (from `hasSubgaussianMGF_id_gaussianReal`, `NLAlib.Probability.Gaussian.Basic.StandardGaussian`).

Atlas: `rotation-invariance` (corollaries), `gaussian-matrix-mulVec-law` (new, audit G1 C3 /
G2 C10), `gaussian-matrix-def` (sub-Gaussian API, audit G1 C9).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Transpose of a standard Gaussian matrix.** If `G` is a `p × m` standard Gaussian matrix,
then `Gᵀ` is an `m × p` standard Gaussian matrix.

HMT 2011, §10.1 (an instance of the coordinate invariance of an i.i.d. product law). Atlas:
`rotation-invariance` (corollary; audit G2 C10).
atlas: gaussian-matrix-mulvec-law -/
theorem hasLaw_gaussianMatrix_transpose (p m : ℕ) :
    HasLaw (fun G : Matrix (Fin p) (Fin m) ℝ => Gᵀ) (gaussianMatrix (Fin m) (Fin p))
      (gaussianMatrix (Fin p) (Fin m)) := by
  refine ⟨Matrix.measurable_transpose.aemeasurable, ?_⟩
  rw [gaussianMatrix_eq_map_curry,
    Measure.map_map Matrix.measurable_transpose (MeasurableEquiv.measurable _)]
  have hfun : (fun G : Matrix (Fin p) (Fin m) ℝ => Gᵀ) ∘
        ((MeasurableEquiv.curry (Fin p) (Fin m) ℝ).trans Matrix.ofMeasurableEquiv)
      = ((MeasurableEquiv.curry (Fin m) (Fin p) ℝ).trans Matrix.ofMeasurableEquiv) ∘
        (fun x : Fin p × Fin m → ℝ => fun ji : Fin m × Fin p => x ji.swap) := by
    funext x; rfl
  have hswap : Measurable fun x : Fin p × Fin m → ℝ => fun ji : Fin m × Fin p => x ji.swap :=
    measurable_pi_lambda _ fun ji => measurable_pi_apply _
  rw [hfun, ← Measure.map_map (MeasurableEquiv.measurable _) hswap,
    map_comp_injective_pi _ Prod.swap Prod.swap_injective, ← gaussianMatrix_eq_map_curry]

/-- `hasLaw_gaussianMatrix_transpose` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ`. Atlas: `rotation-invariance`. -/
theorem hasLaw_gaussianMatrix_transpose_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p m : ℕ} {X : Ω → Matrix (Fin p) (Fin m) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ) :
    HasLaw (fun ω => (X ω)ᵀ) (gaussianMatrix (Fin m) (Fin p)) μ :=
  (hasLaw_gaussianMatrix_transpose p m).comp hX

/-- **Right multiplication by orthonormal columns.** If `G` is a `k × m` standard Gaussian
matrix and `U` (`m × d`) has orthonormal columns, then `G U` is a `k × d` standard Gaussian
matrix.

HMT 2011, §10.1–10.2 (rotational invariance applied on the right). Atlas: `rotation-invariance`
(corollary; audit G2 C10). Proof: `G U = (Uᵀ Gᵀ)ᵀ`, `hasLaw_gaussianMatrix_transpose` and the
block law `hasLaw_gaussianMatrix_block`.
atlas: gaussian-matrix-mulvec-law -/
theorem hasLaw_gaussianMatrix_mul_right {k m d : ℕ} (U : Matrix (Fin m) (Fin d) ℝ)
    (hU : HasOrthonormalCols U) :
    HasLaw (fun G : Matrix (Fin k) (Fin m) ℝ => G * U) (gaussianMatrix (Fin k) (Fin d))
      (gaussianMatrix (Fin k) (Fin m)) := by
  have hfun : (fun G : Matrix (Fin k) (Fin m) ℝ => G * U)
      = (fun G : Matrix (Fin d) (Fin k) ℝ => Gᵀ) ∘
        (fun H : Matrix (Fin m) (Fin k) ℝ => Uᵀ * H) ∘
        (fun G : Matrix (Fin k) (Fin m) ℝ => Gᵀ) := by
    funext G
    simp [Matrix.transpose_mul]
  rw [hfun]
  exact (hasLaw_gaussianMatrix_transpose d k).comp
    ((hasLaw_gaussianMatrix_block U hU).comp (hasLaw_gaussianMatrix_transpose k m))

/-- `hasLaw_gaussianMatrix_mul_right` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin k) (Fin m)) μ`. Atlas: `rotation-invariance`. -/
theorem hasLaw_gaussianMatrix_mul_right_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {k m d : ℕ} {X : Ω → Matrix (Fin k) (Fin m) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin k) (Fin m)) μ) (U : Matrix (Fin m) (Fin d) ℝ)
    (hU : HasOrthonormalCols U) :
    HasLaw (fun ω => X ω * U) (gaussianMatrix (Fin k) (Fin d)) μ :=
  (hasLaw_gaussianMatrix_mul_right U hU).comp hX

/-- **Law of `G x` for a unit vector.** If `G` is a `k × n` standard Gaussian matrix and
`x ⬝ᵥ x = 1`, then `G x` is a standard Gaussian vector in `ℝᵏ`.

HMT 2011, §10.1; Dasgupta–Gupta 2003, proof of Lem 2.2 (`‖G x‖² ∼ χ²_k`). Atlas:
`gaussian-matrix-mulVec-law` (audit G1 C3 / G2 C1(d)). Proof: `hasLaw_gaussianMatrix_mul_right`
with the one-column matrix `x`.
atlas: gaussian-matrix-mulvec-law -/
theorem gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one {k n : ℕ} (x : Fin n → ℝ)
    (hx : x ⬝ᵥ x = 1) :
    (gaussianMatrix (Fin k) (Fin n)).map (fun G => G *ᵥ x)
      = Measure.pi fun _ : Fin k => gaussianReal 0 1 := by
  set U : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ => x i with hU_def
  have hU : HasOrthonormalCols U := by
    show Uᵀ * U = 1
    ext a b
    fin_cases a; fin_cases b
    simpa [U, Matrix.mul_apply, dotProduct] using hx
  have hM : Measurable fun G : Matrix (Fin k) (Fin n) ℝ => G * U :=
    measurable_id.matrix_mul measurable_const
  have hE : Measurable fun H : Matrix (Fin k) (Fin 1) ℝ => fun i => H i 0 :=
    measurable_pi_lambda _ fun i => Matrix.measurable_entry i 0
  have hfun : (fun G : Matrix (Fin k) (Fin n) ℝ => G *ᵥ x)
      = (fun H : Matrix (Fin k) (Fin 1) ℝ => fun i => H i 0) ∘
        (fun G : Matrix (Fin k) (Fin n) ℝ => G * U) := by
    funext G i
    simp [U, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hfun, ← Measure.map_map hE hM, (hasLaw_gaussianMatrix_mul_right U hU).map_eq]
  exact ((measurePreserving_pi (fun _ : Fin k => Measure.pi fun _ : Fin 1 => gaussianReal 0 1)
    (fun _ : Fin k => gaussianReal 0 1)
    (fun _ => measurePreserving_eval (fun _ : Fin 1 => gaussianReal (0 : ℝ) 1) 0)).comp
    measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm).map_eq

/-- **Law of `G x`.** If `G` is a `k × n` standard Gaussian matrix and `x ∈ ℝⁿ`, then the
coordinates of `G x` are i.i.d. `N(0, ‖x‖²)`.

HMT 2011, §10.1. Atlas: `gaussian-matrix-mulVec-law` (audit G1 C3). The variance is written
`(x ⬝ᵥ x).toNNReal`; for `x = 0` both sides are the Dirac mass at `0`. Proof: the unit-vector case
`gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one` and Mathlib `gaussianReal_map_const_mul`.
atlas: gaussian-matrix-mulvec-law -/
theorem gaussianMatrix_map_mulVec {k n : ℕ} (x : Fin n → ℝ) :
    (gaussianMatrix (Fin k) (Fin n)).map (fun G => G *ᵥ x)
      = Measure.pi fun _ : Fin k => gaussianReal 0 (x ⬝ᵥ x).toNNReal := by
  by_cases hx0 : x ⬝ᵥ x = 0
  · have hx : x = 0 := dotProduct_self_eq_zero.mp hx0
    subst hx
    have h0 : ∀ i : Fin k, MeasurePreserving (fun _ : ℝ => (0 : ℝ)) (gaussianReal 0 1)
        (Measure.dirac 0) :=
      fun _ => ⟨measurable_const, by rw [Measure.map_const, measure_univ, one_smul]⟩
    have hR := (measurePreserving_pi (fun _ : Fin k => gaussianReal 0 1)
      (fun _ : Fin k => Measure.dirac (0 : ℝ)) h0).map_eq
    rw [Measure.map_const, measure_univ, one_smul] at hR
    simp only [hx0, Real.toNNReal_zero, gaussianReal_zero_var, Matrix.mulVec_zero]
    rw [← hR, Measure.map_const, measure_univ, one_smul]
    rfl
  · have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dotProduct_self_star_nonneg x) (Ne.symm hx0)
    set r := Real.sqrt (x ⬝ᵥ x) with hr_def
    have hr : 0 < r := Real.sqrt_pos.2 hpos
    set u := r⁻¹ • x with hu_def
    have hu : u ⬝ᵥ u = 1 := by
      rw [hu_def, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← sq, inv_pow, hr_def, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hx0]
    have hxu : x = r • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hmu : Measurable fun G : Matrix (Fin k) (Fin n) ℝ => G *ᵥ u := by
      refine measurable_pi_lambda _ fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.measurable_sum _ fun j _ => (Matrix.measurable_entry i j).mul_const _
    have hS : Measurable fun y : Fin k → ℝ => fun i => r * y i := by fun_prop
    have hfun : (fun G : Matrix (Fin k) (Fin n) ℝ => G *ᵥ x)
        = (fun y : Fin k → ℝ => fun i => r * y i) ∘ (fun G => G *ᵥ u) := by
      funext G i
      simp [hxu, Matrix.mulVec_smul]
    rw [hfun, ← Measure.map_map hS hmu, gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one u hu]
    have hvar : NNReal.mk (r ^ 2) (sq_nonneg _) * 1 = (x ⬝ᵥ x).toNNReal := by
      ext
      simp [hr_def, Real.sq_sqrt hpos.le, hpos.le]
    have hmp : ∀ i : Fin k, MeasurePreserving (fun y : ℝ => r * y) (gaussianReal 0 1)
        (gaussianReal 0 (x ⬝ᵥ x).toNNReal) := fun _ =>
      ⟨measurable_const_mul r, by rw [gaussianReal_map_const_mul, mul_zero]; congr 1⟩
    exact (measurePreserving_pi _ _ hmp).map_eq

/-! ### Sub-Gaussian moment generating functions -/

/-- **Coordinates of `G x` are sub-Gaussian**: for a `k × n` standard Gaussian matrix `G`, each
coordinate `(G x)ᵢ` has `HasSubgaussianMGF` with proxy `‖x‖² = x ⬝ᵥ x`.

HMT 2011, §10.1 with Vershynin 2018, §2.5. Atlas: `gaussian-matrix-mulVec-law` (corollary).
Proof: the law `gaussianMatrix_map_mulVec` and `hasSubgaussianMGF_id_gaussianReal`.
atlas: gaussian-matrix-mulvec-law -/
theorem hasSubgaussianMGF_mulVec_apply_gaussianMatrix {k n : ℕ} (x : Fin n → ℝ) (i : Fin k) :
    HasSubgaussianMGF (fun G : Matrix (Fin k) (Fin n) ℝ => (G *ᵥ x) i) (x ⬝ᵥ x).toNNReal
      (gaussianMatrix (Fin k) (Fin n)) := by
  have hm : Measurable fun G : Matrix (Fin k) (Fin n) ℝ => G *ᵥ x := by
    refine measurable_pi_lambda _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun j _ => (Matrix.measurable_entry i j).mul_const _
  have hlaw : (gaussianMatrix (Fin k) (Fin n)).map (fun G : Matrix (Fin k) (Fin n) ℝ => (G *ᵥ x) i)
      = gaussianReal 0 (x ⬝ᵥ x).toNNReal := by
    rw [show (fun G : Matrix (Fin k) (Fin n) ℝ => (G *ᵥ x) i)
        = (fun y : Fin k → ℝ => y i) ∘ (fun G => G *ᵥ x) from rfl,
      ← Measure.map_map (measurable_pi_apply i) hm, gaussianMatrix_map_mulVec]
    exact (measurePreserving_eval _ i).map_eq
  have hX : AEMeasurable (fun G : Matrix (Fin k) (Fin n) ℝ => (G *ᵥ x) i)
      (gaussianMatrix (Fin k) (Fin n)) := ((measurable_pi_apply i).comp hm).aemeasurable
  refine (HasSubgaussianMGF.id_map_iff hX).1 ?_
  rw [hlaw]
  exact hasSubgaussianMGF_id_gaussianReal _

end NLAlib
