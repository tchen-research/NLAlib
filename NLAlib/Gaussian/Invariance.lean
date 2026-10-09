/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_rotation_invariance`, `Sol_GaussianMatrix_block_law`,
`Sol_GaussianMatrix_block_indep`).
-/
import NLAlib.Gaussian.Basic
import NLAlib.Matrix.Projections
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Orthogonal invariance of the standard Gaussian matrix

* `NLAlib.gaussianMatrix_map_orthogonal`: for orthogonal `U`, `V`, the law of `U G V` is the law
  of `G` (HMT 2011 §10.1, atlas `rotation-invariance`).
* `NLAlib.gaussianMatrix_map_block`: for `V₁` with orthonormal columns, `V₁ᵀ G` is a standard
  Gaussian matrix (HMT 2011 §10.2, atlas `block-law-indep`).
* `NLAlib.gaussianMatrix_indepFun_block`: if moreover `V₂` has orthonormal columns and
  `V₁ᵀ V₂ = 0`, then `V₁ᵀ G` and `V₂ᵀ G` are independent (HMT 2011 §10.2, atlas
  `block-law-indep`).

The orthonormality hypotheses are written `Vᵀ * V = 1`, which is `NLAlib.HasOrthonormalCols V`
unfolded.

Proof source: Prove2me workspace, Gaussian Random Matrices series (rotation invariance, block
law, block independence), ported without change of statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Flattening to `EuclideanSpace` and the rotation isometry -/

/-- Flatten a `p × m` array into a vector of `EuclideanSpace ℝ (Fin p × Fin m)`. -/
private def flat (p m : ℕ) (G : Fin p → Fin m → ℝ) : EuclideanSpace ℝ (Fin p × Fin m) :=
  WithLp.toLp 2 (fun ij => G ij.1 ij.2)

private lemma measurable_flat (p m : ℕ) : Measurable (flat p m) := by
  unfold flat
  exact (WithLp.measurable_toLp 2 _).comp (by fun_prop)

/-- `flat` as a measurable equivalence. -/
private def flatEquiv (p m : ℕ) :
    (Fin p → Fin m → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin p × Fin m) :=
  (MeasurableEquiv.curry (Fin p) (Fin m) ℝ).symm.trans (MeasurableEquiv.toLp 2 _)

/-- The Gaussian matrix law, flattened, is the standard Gaussian on `EuclideanSpace`. -/
private lemma map_flat_gaussianMatrix (p m : ℕ) :
    (gaussianMatrix p m).map (flat p m) = stdGaussian (EuclideanSpace ℝ (Fin p × Fin m)) := by
  have h1 : gaussianMatrix p m =
      (Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1).map
        (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) := by
    have := Measure.infinitePi_map_curry (fun (_ : Fin p) (_ : Fin m) => gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at this
    rw [this]; rfl
  rw [h1, Measure.map_map (measurable_flat p m) (MeasurableEquiv.measurable _)]
  have h2 : flat p m ∘ (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) = WithLp.toLp 2 := by
    funext x; rfl
  rw [h2, map_pi_eq_stdGaussian]

private lemma sum_sq_eq_trace {p m : ℕ} (A : Matrix (Fin p) (Fin m) ℝ) :
    ∑ i, ∑ j, A i j ^ 2 = Matrix.trace (A * Aᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

private lemma sum_sq_mul_orth {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (X : Matrix (Fin p) (Fin m) ℝ) :
    ∑ i, ∑ j, (U * X * V) i j ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  rw [sum_sq_eq_trace, sum_sq_eq_trace]
  simp only [Matrix.transpose_mul]
  calc Matrix.trace (U * X * V * (Vᵀ * (Xᵀ * Uᵀ)))
      = Matrix.trace (U * (X * (V * Vᵀ) * Xᵀ) * Uᵀ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Uᵀ * U * (X * (V * Vᵀ) * Xᵀ)) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace (X * Xᵀ) := by rw [hU, hV', Matrix.one_mul, Matrix.mul_one]

/-- Unflatten a vector into a matrix. -/
private def unflat {p m : ℕ} (x : EuclideanSpace ℝ (Fin p × Fin m)) :
    Matrix (Fin p) (Fin m) ℝ :=
  Matrix.of fun i j => x (i, j)

/-- The linear map `X ↦ U X V` on flattened matrices. -/
private def rotLin {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin p × Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p × Fin m) where
  toFun x := flat p m (Matrix.of.symm (U * unflat x * V))
  map_add' x y := by
    have : unflat (x + y) = unflat x + unflat y := by ext i j; simp [unflat]
    rw [this, Matrix.mul_add, Matrix.add_mul]
    ext ij; simp [flat]
  map_smul' c x := by
    have : unflat (c • x) = c • unflat x := by ext i j; simp [unflat]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    ext ij; simp [flat]

private lemma norm_rotLin {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (x : EuclideanSpace ℝ (Fin p × Fin m)) :
    ‖rotLin U V x‖ = ‖x‖ := by
  have h : ‖rotLin U V x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    have := sum_sq_mul_orth U V hU hV (unflat x)
    simpa [rotLin, flat, unflat] using this
  have h1 := norm_nonneg (rotLin U V x)
  have h2 := norm_nonneg x
  nlinarith [sq_nonneg (‖rotLin U V x‖ - ‖x‖), sq_nonneg (‖rotLin U V x‖ + ‖x‖)]

/-- The isometry `X ↦ U X V` of the Frobenius space. -/
private def rotIso {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    EuclideanSpace ℝ (Fin p × Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin p × Fin m) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := rotLin U V, norm_map' := norm_rotLin U V hU hV } rfl

private lemma rotIso_flat {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (G : Fin p → Fin m → ℝ) :
    rotIso U V hU hV (flat p m G) = flat p m (Matrix.of.symm (U * Matrix.of G * V)) := by
  rfl

/-- **Orthogonal invariance of the standard Gaussian matrix.** For orthogonal `U` (`p × p`) and
`V` (`m × m`), the law of `U G V` is the law of `G` when `G` is a `p × m` standard Gaussian
matrix.

HMT 2011 (Halko–Martinsson–Tropp), §10.1 (rotational invariance of the standard Gaussian
matrix). Atlas: `rotation-invariance`. The law is the pushforward of
`gaussianMatrix p m` (a measure on `Fin p → Fin m → ℝ`), so the map is written with
`Matrix.of.symm`. Ported from the Prove2me workspace, Gaussian Random Matrices series. -/
theorem gaussianMatrix_map_orthogonal {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Measure.map (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V))
      (gaussianMatrix p m) = gaussianMatrix p m := by
  have hmeas : Measurable
      (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) := by
    have hc : Continuous
        (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
    exact hc.measurable
  have key : ((gaussianMatrix p m).map
      (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V))).map (flat p m) =
      (gaussianMatrix p m).map (flat p m) := by
    rw [Measure.map_map (measurable_flat p m) hmeas]
    have : flat p m ∘ (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) =
        rotIso U V hU hV ∘ flat p m := by
      funext G; exact (rotIso_flat U V hU hV G).symm
    rw [this, ← Measure.map_map (rotIso U V hU hV).continuous.measurable (measurable_flat p m),
      map_flat_gaussianMatrix, stdGaussian_map]
  have hfe : ⇑(flatEquiv p m) = flat p m := rfl
  rw [← hfe] at key
  exact (flatEquiv p m).map_measurableEquiv_injective key

/-! ### Orthogonal completion and coordinate restriction -/

/-- Restricting the coordinates of an i.i.d. product measure along an injection gives the
product measure on the smaller index set. -/
theorem map_comp_injective_pi {ι κ β : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (e : ι → κ) (he : Function.Injective e) :
    Measure.map (fun x : κ → β => fun j => x (e j)) (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : ι => ν := by
  have hind : iIndepFun (fun (i : κ) (x : κ → β) => x i) (Measure.pi fun _ : κ => ν) :=
    iIndepFun_pi (X := fun _ (y : β) => y) (fun _ => aemeasurable_id)
  have hind' := hind.precomp he
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)]
    at hind'
  rw [hind']
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : κ => ν) (e j)).map_eq

/-! ### Block law and block independence -/

/-- **Law of a Gaussian block.** If `V₁` (`n × k`) has orthonormal columns and `G` is an
`n × t` standard Gaussian matrix, then `V₁ᵀ G` is a `k × t` standard Gaussian matrix.

HMT 2011 (Halko–Martinsson–Tropp), §10.2 (with `G = Ω` and `V₁` the leading right singular
vectors: `Ω₁ = V₁ᵀ Ω` is standard Gaussian). Atlas: `block-law-indep`. Ported from the Prove2me
workspace, Gaussian Random Matrices series. -/
theorem gaussianMatrix_map_block {n k t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) :
    Measure.map (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (gaussianMatrix n t) = gaussianMatrix k t := by
  classical
  have hk : Fintype.card (Fin k) ≤ Fintype.card (Fin n) := by
    simpa using card_le_of_transpose_mul_self_eq_one V₁ hV₁
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_orthogonal_completion V₁ hV₁ e
  let H : (Fin n → Fin t → ℝ) → (Fin n → Fin t → ℝ) :=
    fun G => Matrix.of.symm (Wᵀ * Matrix.of G * (1 : Matrix (Fin t) (Fin t) ℝ))
  have hHm : Measurable H := by
    have : H = fun G a l => ∑ i, W i a * G i l := by
      funext G a l; simp [H, Matrix.mul_apply, Matrix.mul_one]
    rw [this]; fun_prop
  have hH : Measure.map H (gaussianMatrix n t) = gaussianMatrix n t :=
    gaussianMatrix_map_orthogonal Wᵀ 1
      (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW) (by simp)
  have hfun : (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G)) =
      (fun X : Fin n → Fin t → ℝ => fun j => X (e j)) ∘ H := by
    funext G j l
    simp [H, Matrix.mul_apply, hWe]
  rw [hfun, ← Measure.map_map (by fun_prop) hHm, hH]
  exact map_comp_injective_pi _ e e.injective

/-- **Independence of Gaussian blocks.** If `V₁` (`n × k`) and `V₂` (`n × r`) have orthonormal
columns and `V₁ᵀ V₂ = 0`, and `G` is an `n × t` standard Gaussian matrix, then `V₁ᵀ G` and
`V₂ᵀ G` are independent.

HMT 2011 (Halko–Martinsson–Tropp), §10.2 (`Ω₁ = V₁ᵀ Ω` and `Ω₂ = V₂ᵀ Ω` are independent).
Atlas: `block-law-indep`. Ported from the Prove2me workspace, Gaussian Random Matrices
series. -/
theorem gaussianMatrix_indepFun_block {n k r t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1)
    (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₂ᵀ * Matrix.of G))
      (gaussianMatrix n t) := by
  classical
  -- the concatenated matrix `[V₁ V₂]` has orthonormal columns
  let V : Matrix (Fin n) (Fin k ⊕ Fin r) ℝ := Matrix.fromCols V₁ V₂
  have hV₂₁ : V₂ᵀ * V₁ = 0 := by
    rw [← Matrix.transpose_transpose V₁, ← Matrix.transpose_mul, hV₁₂, Matrix.transpose_zero]
  have hV : Vᵀ * V = 1 := by
    simp only [V, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hV₁, hV₂, hV₁₂,
      hV₂₁, Matrix.fromBlocks_one]
  have hk : Fintype.card (Fin k ⊕ Fin r) ≤ Fintype.card (Fin n) := by
    simpa using card_le_of_transpose_mul_self_eq_one V hV
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_orthogonal_completion V hV e
  let H : (Fin n → Fin t → ℝ) → (Fin n → Fin t → ℝ) :=
    fun G => Matrix.of.symm (Wᵀ * Matrix.of G * (1 : Matrix (Fin t) (Fin t) ℝ))
  have hHm : Measurable H := by
    have : H = fun G a l => ∑ i, W i a * G i l := by
      funext G a l; simp [H, Matrix.mul_apply, Matrix.mul_one]
    rw [this]; fun_prop
  have hH : Measure.map H (gaussianMatrix n t) = gaussianMatrix n t :=
    gaussianMatrix_map_orthogonal Wᵀ 1
      (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW) (by simp)
  -- the rows of `H G` are independent under the Gaussian law
  have hmeas : ∀ a, Measurable fun G => H G a := fun a => (measurable_pi_apply a).comp hHm
  have hind : iIndepFun (fun (a : Fin n) G => H G a) (gaussianMatrix n t) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => (hmeas a).aemeasurable)]
    have h1 : ∀ a, Measure.map (fun G => H G a) (gaussianMatrix n t) =
        Measure.pi fun _ : Fin t => gaussianReal 0 1 := by
      intro a
      rw [show (fun G => H G a) = (fun f => f a) ∘ H from rfl,
        ← Measure.map_map (measurable_pi_apply a) hHm, hH]
      exact (measurePreserving_eval
        (fun _ : Fin n => Measure.pi fun _ : Fin t => gaussianReal 0 1) a).map_eq
    simp_rw [h1]
    exact hH
  let S : Finset (Fin n) := Finset.univ.map (Function.Embedding.inl.trans e)
  let T : Finset (Fin n) := Finset.univ.map (Function.Embedding.inr.trans e)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [S, T, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, hj⟩ := hb
    exact absurd (e.injective hj) (by simp)
  have hpair := hind.indepFun_finset S T hST hmeas
  have hS : ∀ j : Fin k, e (Sum.inl j) ∈ S := fun j => by simp [S]
  have hT : ∀ j : Fin r, e (Sum.inr j) ∈ T := fun j => by simp [T]
  let φ : (S → Fin t → ℝ) → (Fin k → Fin t → ℝ) := fun y j => y ⟨e (Sum.inl j), hS j⟩
  let ψ : (T → Fin t → ℝ) → (Fin r → Fin t → ℝ) := fun y j => y ⟨e (Sum.inr j), hT j⟩
  have hφ : Measurable φ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hψ : Measurable ψ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have h := hpair.comp hφ hψ
  convert h using 1
  · funext G j l
    simp [φ, H, Matrix.mul_apply, hWe, V]
  · funext G j l
    simp [ψ, H, Matrix.mul_apply, hWe, V]

end NLAlib
