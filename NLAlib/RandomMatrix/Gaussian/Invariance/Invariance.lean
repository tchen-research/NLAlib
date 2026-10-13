/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_rotation_invariance`, `Sol_GaussianMatrix_block_law`,
`Sol_GaussianMatrix_block_indep`).
-/
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.Matrix.Subspaces.Projections
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Orthogonal invariance of the standard Gaussian matrix

* `NLAlib.hasLaw_gaussianMatrix_orthogonal`: for orthogonal `U`, `V`, the law of `U G V` is the
  law of `G` (HMT 2011 §10.1, atlas `rotation-invariance`);
* `NLAlib.measurePreserving_orthonormalBasis_repr_pi_gaussianReal`: the coordinates of a
  standard Gaussian vector in an orthonormal basis are i.i.d. standard Gaussian;
* `NLAlib.hasLaw_gaussianMatrix_block`: for `V₁` with orthonormal columns, `V₁ᵀ G` is a standard
  Gaussian matrix (HMT 2011 §10.2, atlas `block-law-indep`);
* `NLAlib.gaussianMatrix_indepFun_block`: if moreover `V₂` has orthonormal columns and
  `V₁ᵀ V₂ = 0`, then `V₁ᵀ G` and `V₂ᵀ G` are independent (HMT 2011 §10.2, atlas
  `block-law-indep`).

Each is stated for the identity random variable under `gaussianMatrix`, with a `_of_hasLaw`
corollary for a random matrix `X` with `HasLaw X (gaussianMatrix _ _) μ`.

Proof source: Prove2me workspace, Gaussian Random Matrices series (rotation invariance, block
law, block independence), ported without change of statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Flattening to `EuclideanSpace` and the rotation isometry -/

/-- Flatten a `p × m` matrix into a vector of `EuclideanSpace ℝ (p × m)`. -/
private def flat (p m : Type*) [Fintype p] [Fintype m] (G : Matrix p m ℝ) :
    EuclideanSpace ℝ (p × m) :=
  WithLp.toLp 2 (fun ij => G ij.1 ij.2)

private lemma measurable_uncurry (p m : Type*) [Fintype p] [Fintype m] :
    Measurable fun G : Matrix p m ℝ => fun ij : p × m => G ij.1 ij.2 :=
  measurable_pi_lambda _ fun ij => Matrix.measurable_entry ij.1 ij.2

private lemma measurable_flat (p m : Type*) [Fintype p] [Fintype m] : Measurable (flat p m) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_uncurry p m)

/-- `flat` as a measurable equivalence. -/
private def flatEquiv (p m : Type*) [Fintype p] [Fintype m] :
    Matrix p m ℝ ≃ᵐ EuclideanSpace ℝ (p × m) :=
  Matrix.ofMeasurableEquiv.symm.trans
    ((MeasurableEquiv.curry p m ℝ).symm.trans (MeasurableEquiv.toLp 2 _))

/-- The Gaussian matrix law, flattened, is the standard Gaussian on `EuclideanSpace`. -/
private lemma map_flat_gaussianMatrix (p m : Type*) [Fintype p] [Fintype m] :
    (gaussianMatrix p m).map (flat p m) =
      stdGaussian (EuclideanSpace ℝ (p × m)) := by
  rw [show flat p m = WithLp.toLp 2 ∘ fun G : Matrix p m ℝ => fun ij => G ij.1 ij.2
      from rfl, ← Measure.map_map (WithLp.measurable_toLp 2 _) (measurable_uncurry p m),
    gaussianMatrix_map_uncurry, map_pi_eq_stdGaussian]

private lemma sum_sq_eq_trace {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (A : Matrix p m ℝ) :
    ∑ i, ∑ j, A i j ^ 2 = Matrix.trace (A * Aᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

private lemma sum_sq_mul_orth {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (U : Matrix p p ℝ)
    (V : Matrix m m ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (X : Matrix p m ℝ) :
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
private def unflat {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (x : EuclideanSpace ℝ (p × m)) :
    Matrix p m ℝ :=
  Matrix.of fun i j => x (i, j)

/-- The linear map `X ↦ U X V` on flattened matrices. -/
private def rotLin {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (U : Matrix p p ℝ) (V : Matrix m m ℝ) :
    EuclideanSpace ℝ (p × m) →ₗ[ℝ] EuclideanSpace ℝ (p × m) where
  toFun x := flat p m (U * unflat x * V)
  map_add' x y := by
    have : unflat (x + y) = unflat x + unflat y := by ext i j; simp [unflat]
    rw [this, Matrix.mul_add, Matrix.add_mul]
    ext ij; simp [flat]
  map_smul' c x := by
    have : unflat (c • x) = c • unflat x := by ext i j; simp [unflat]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    ext ij; simp [flat]

private lemma norm_rotLin {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (U : Matrix p p ℝ)
    (V : Matrix m m ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (x : EuclideanSpace ℝ (p × m)) :
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
private def rotIso {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (U : Matrix p p ℝ) (V : Matrix m m ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    EuclideanSpace ℝ (p × m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (p × m) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := rotLin U V, norm_map' := norm_rotLin U V hU hV } rfl

private lemma rotIso_flat {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (U : Matrix p p ℝ)
    (V : Matrix m m ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (G : Matrix p m ℝ) :
    rotIso U V hU hV (flat p m G) = flat p m (U * G * V) := by
  rfl

/-- **Orthogonal invariance of the standard Gaussian matrix.** For orthogonal `U` (`p × p`) and
`V` (`m × m`), the law of `U G V` is the law of `G` when `G` is a `p × m` standard Gaussian
matrix.

HMT 2011 (Halko–Martinsson–Tropp), §10.1 (rotational invariance of the standard Gaussian
matrix). Atlas: `rotation-invariance`. Ported from the Prove2me workspace, Gaussian Random
Matrices series.
atlas: rotation-invariance -/
theorem hasLaw_gaussianMatrix_orthogonal {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p]
    [DecidableEq m] (U : Matrix p p ℝ)
    (V : Matrix m m ℝ) (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    HasLaw (fun G : Matrix p m ℝ => U * G * V) (gaussianMatrix p m)
      (gaussianMatrix p m) := by
  have hU' : Uᵀ * U = 1 := hU
  have hV' : Vᵀ * V = 1 := hV
  have hmeas : Measurable (fun G : Matrix p m ℝ => U * G * V) :=
    (measurable_const.matrix_mul measurable_id).matrix_mul measurable_const
  refine ⟨hmeas.aemeasurable, ?_⟩
  have key : ((gaussianMatrix p m).map
      (fun G : Matrix p m ℝ => U * G * V)).map (flat p m) =
      (gaussianMatrix p m).map (flat p m) := by
    rw [Measure.map_map (measurable_flat p m) hmeas]
    have : flat p m ∘ (fun G : Matrix p m ℝ => U * G * V) =
        rotIso U V hU' hV' ∘ flat p m := by
      funext G; exact (rotIso_flat U V hU' hV' G).symm
    rw [this, ← Measure.map_map (rotIso U V hU' hV').continuous.measurable (measurable_flat p m),
      map_flat_gaussianMatrix, stdGaussian_map]
  have hfe : ⇑(flatEquiv p m) = flat p m := rfl
  rw [← hfe] at key
  exact (flatEquiv p m).map_measurableEquiv_injective key

/-- `hasLaw_gaussianMatrix_orthogonal` for a random matrix: if `X` is a `p × m` standard Gaussian
matrix under `μ` and `U`, `V` are orthogonal, so is `U X V`. Atlas: `rotation-invariance`. -/
theorem hasLaw_gaussianMatrix_orthogonal_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    {X : Ω → Matrix p m ℝ}
    (hX : HasLaw X (gaussianMatrix p m) μ) (U : Matrix p p ℝ)
    (V : Matrix m m ℝ) (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => U * X ω * V) (gaussianMatrix p m) μ :=
  (hasLaw_gaussianMatrix_orthogonal U V hU hV).comp hX

/-! ### Rotation invariance of a standard Gaussian vector -/

/-- **Rotation invariance in coordinates.** For an orthonormal basis `b` of `ℝᴺ` indexed by `ι`,
the coordinates `(⟪b i, g⟫)ᵢ` of a standard Gaussian vector `g` are i.i.d. standard Gaussian.
Atlas: `smin-small-ball` (helper; an instance of `gaussian-rotation-invariance`). Ported from
Prove2me solution `GaussianMatrix.gaussian_dist_colspace_small_ball`. -/
theorem measurePreserving_orthonormalBasis_repr_pi_gaussianReal {N : ℕ} {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin N))) :
    MeasurePreserving (fun g : Fin N → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 g)))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hm1 : Measurable (fun g : Fin N → ℝ => WithLp.toLp 2 g) := by fun_prop
  have hm2 : Measurable (fun x : EuclideanSpace ℝ (Fin N) => b.repr x) :=
    b.repr.continuous.measurable
  have hm3 : Measurable (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) := by fun_prop
  refine ⟨hm3.comp (hm2.comp hm1), ?_⟩
  have h := map_pi_eq_stdGaussian (ι := Fin N)
  have h' := map_pi_eq_stdGaussian (ι := ι)
  have hfun : (fun g : Fin N → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 g)))
      = (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) ∘ ((fun x => b.repr x) ∘
          (fun g : Fin N → ℝ => WithLp.toLp 2 g)) := rfl
  rw [hfun, ← Measure.map_map hm3 (hm2.comp hm1), ← Measure.map_map hm2 hm1, h]
  rw [show (fun x : EuclideanSpace ℝ (Fin N) => b.repr x) = ⇑b.repr from rfl, stdGaussian_map,
    ← h', Measure.map_map hm3 (by fun_prop)]
  exact Measure.map_id

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
workspace, Gaussian Random Matrices series.
atlas: block-law-indep -/
theorem hasLaw_gaussianMatrix_block {n : ℕ} {k t : Type*} [Fintype k] [Fintype t]
    [DecidableEq k] (V₁ : Matrix (Fin n) k ℝ)
    (hV₁ : HasOrthonormalCols V₁) :
    HasLaw (fun G : Matrix (Fin n) t ℝ => V₁ᵀ * G) (gaussianMatrix k t)
      (gaussianMatrix (Fin n) t) := by
  classical
  have hk : Fintype.card k ≤ Fintype.card (Fin n) := by
    simpa using card_le_card_of_hasOrthonormalCols (Q := V₁) hV₁
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_unitary_completion V₁ hV₁ e
  let H : Matrix (Fin n) t ℝ → Matrix (Fin n) t ℝ :=
    fun G => Wᵀ * G * (1 : Matrix t t ℝ)
  have hH : HasLaw H (gaussianMatrix (Fin n) t) (gaussianMatrix (Fin n) t) :=
    hasLaw_gaussianMatrix_orthogonal Wᵀ 1
      (by
        show Wᵀᵀ * Wᵀ = 1
        rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW) (by simp [HasOrthonormalCols])
  have hR : HasLaw (fun X : Matrix (Fin n) t ℝ => Matrix.of fun j => X (e j))
      (gaussianMatrix k t) (gaussianMatrix (Fin n) t) := by
    have hRm : Measurable fun X : Matrix (Fin n) t ℝ => Matrix.of fun j => X (e j) :=
      Matrix.measurable_iff_entries.mpr fun j l => Matrix.measurable_entry (e j) l
    refine ⟨hRm.aemeasurable, ?_⟩
    rw [gaussianMatrix, Measure.map_map hRm Matrix.ofMeasurableEquiv.measurable, gaussianMatrix,
      ← map_comp_injective_pi _ e e.injective,
      Measure.map_map Matrix.ofMeasurableEquiv.measurable (by fun_prop)]
    rfl
  have hfun : (fun G : Matrix (Fin n) t ℝ => V₁ᵀ * G) =
      (fun X : Matrix (Fin n) t ℝ => Matrix.of fun j => X (e j)) ∘ H := by
    funext G j l
    simp [H, Matrix.mul_apply, hWe]
  rw [hfun]
  exact hR.comp hH

/-- `hasLaw_gaussianMatrix_block` for a random matrix: if `X` is an `n × t` standard Gaussian
matrix under `μ` and `V₁` has orthonormal columns, `V₁ᵀ X` is a `k × t` standard Gaussian
matrix. Atlas: `block-law-indep`. -/
theorem hasLaw_gaussianMatrix_block_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {k t : Type*} [Fintype k] [Fintype t] [DecidableEq k]
    {X : Ω → Matrix (Fin n) t ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin n) t) μ) (V₁ : Matrix (Fin n) k ℝ)
    (hV₁ : HasOrthonormalCols V₁) :
    HasLaw (fun ω => V₁ᵀ * X ω) (gaussianMatrix k t) μ :=
  (hasLaw_gaussianMatrix_block V₁ hV₁).comp hX

/-- **Independence of Gaussian blocks.** If `V₁` (`n × k`) and `V₂` (`n × r`) have orthonormal
columns and `V₁ᵀ V₂ = 0`, and `G` is an `n × t` standard Gaussian matrix, then `V₁ᵀ G` and
`V₂ᵀ G` are independent.

HMT 2011 (Halko–Martinsson–Tropp), §10.2 (`Ω₁ = V₁ᵀ Ω` and `Ω₂ = V₂ᵀ Ω` are independent).
Atlas: `block-law-indep`. Ported from the Prove2me workspace, Gaussian Random Matrices
series.
atlas: block-law-indep -/
theorem gaussianMatrix_indepFun_block {n : ℕ} {k r t : Type*} [Fintype k] [Fintype r]
    [Fintype t] [DecidableEq k] [DecidableEq r] (V₁ : Matrix (Fin n) k ℝ)
    (V₂ : Matrix (Fin n) r ℝ) (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun G : Matrix (Fin n) t ℝ => V₁ᵀ * G)
      (fun G : Matrix (Fin n) t ℝ => V₂ᵀ * G)
      (gaussianMatrix (Fin n) t) := by
  classical
  have hV₁' : V₁ᵀ * V₁ = 1 := hV₁
  have hV₂' : V₂ᵀ * V₂ = 1 := hV₂
  -- the concatenated matrix `[V₁ V₂]` has orthonormal columns
  let V : Matrix (Fin n) (k ⊕ r) ℝ := Matrix.fromCols V₁ V₂
  have hV₂₁ : V₂ᵀ * V₁ = 0 := by
    rw [← Matrix.transpose_transpose V₁, ← Matrix.transpose_mul, hV₁₂, Matrix.transpose_zero]
  have hV : Vᵀ * V = 1 := by
    simp only [V, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hV₁', hV₂', hV₁₂,
      hV₂₁, Matrix.fromBlocks_one]
  have hk : Fintype.card (k ⊕ r) ≤ Fintype.card (Fin n) := by
    simpa using card_le_card_of_hasOrthonormalCols (Q := V) hV
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_unitary_completion V hV e
  let H : Matrix (Fin n) t ℝ → Matrix (Fin n) t ℝ :=
    fun G => Wᵀ * G * (1 : Matrix t t ℝ)
  have hH : HasLaw H (gaussianMatrix (Fin n) t) (gaussianMatrix (Fin n) t) :=
    hasLaw_gaussianMatrix_orthogonal Wᵀ 1
      (by
        show Wᵀᵀ * Wᵀ = 1
        rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW) (by simp [HasOrthonormalCols])
  have hHm : Measurable H := (measurable_const.matrix_mul measurable_id).matrix_mul measurable_const
  -- the rows of `H G` are independent under the Gaussian law
  have hrowm : ∀ a, Measurable fun G : Matrix (Fin n) t ℝ => G a := fun a =>
    measurable_pi_lambda _ fun j => Matrix.measurable_entry a j
  have hmeas : ∀ a, Measurable fun G => H G a := fun a => (hrowm a).comp hHm
  -- the rows of a Gaussian matrix are i.i.d. standard Gaussian vectors
  have hrows : iIndepFun (fun (a : Fin n) (G : Matrix (Fin n) t ℝ) => G a)
      (gaussianMatrix (Fin n) t) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => (hrowm a).aemeasurable)]
    have h1 : ∀ a, Measure.map (fun G : Matrix (Fin n) t ℝ => G a)
        (gaussianMatrix (Fin n) t) = Measure.pi fun _ : t => gaussianReal 0 1 :=
      fun a => ((measurePreserving_eval
        (fun _ : Fin n => Measure.pi fun _ : t => gaussianReal 0 1) a).comp
        measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm).map_eq
    simp_rw [h1]
    exact (measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm).map_eq
  have hind : iIndepFun (fun (a : Fin n) G => H G a) (gaussianMatrix (Fin n) t) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => (hrowm a).aemeasurable)] at hrows
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => (hmeas a).aemeasurable),
      show (fun G (a : Fin n) => H G a) = (fun G (a : Fin n) => G a) ∘ H from rfl,
      ← Measure.map_map (measurable_pi_lambda _ hrowm) hHm, hH.map_eq, hrows]
    congr 1
    funext a
    rw [show (fun G => H G a) = (fun G : Matrix (Fin n) t ℝ => G a) ∘ H from rfl,
      ← Measure.map_map (hrowm a) hHm, hH.map_eq]
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
  have hS : ∀ j : k, e (Sum.inl j) ∈ S := fun j => by simp [S]
  have hT : ∀ j : r, e (Sum.inr j) ∈ T := fun j => by simp [T]
  let φ : (S → t → ℝ) → Matrix k t ℝ :=
    fun y => Matrix.of fun j => y ⟨e (Sum.inl j), hS j⟩
  let ψ : (T → t → ℝ) → Matrix r t ℝ :=
    fun y => Matrix.of fun j => y ⟨e (Sum.inr j), hT j⟩
  have hφ : Measurable φ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hψ : Measurable ψ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have h := hpair.comp hφ hψ
  convert h using 1
  · funext G j l
    simp [φ, H, Matrix.mul_apply, hWe, V]
  · funext G j l
    simp [ψ, H, Matrix.mul_apply, hWe, V]

/-- `gaussianMatrix_indepFun_block` for a random matrix: if `X` is an `n × t` standard Gaussian
matrix under `μ`, `V₁`, `V₂` have orthonormal columns and `V₁ᵀ V₂ = 0`, then `V₁ᵀ X` and `V₂ᵀ X`
are independent. Atlas: `block-law-indep`. -/
theorem gaussianMatrix_indepFun_block_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {k r t : Type*} [Fintype k] [Fintype r] [Fintype t]
    [DecidableEq k] [DecidableEq r] {X : Ω → Matrix (Fin n) t ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin n) t) μ) (V₁ : Matrix (Fin n) k ℝ)
    (V₂ : Matrix (Fin n) r ℝ) (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun ω => V₁ᵀ * X ω) (fun ω => V₂ᵀ * X ω) μ := by
  have := hX.isProbabilityMeasure
  have hXm := hX.aemeasurable
  have hind := gaussianMatrix_indepFun_block (t := t) V₁ V₂ hV₁ hV₂ hV₁₂
  have hm₁ := measurable_block (t := t) V₁
  have hm₂ := measurable_block (t := t) V₂
  rw [← hX.map_eq, indepFun_iff_map_prod_eq_prod_map_map hm₁.aemeasurable hm₂.aemeasurable] at hind
  show IndepFun ((fun G : Matrix (Fin n) t ℝ => V₁ᵀ * G) ∘ X)
    ((fun G : Matrix (Fin n) t ℝ => V₂ᵀ * G) ∘ X) μ
  rw [indepFun_iff_map_prod_eq_prod_map_map (hm₁.comp_aemeasurable hXm)
    (hm₂.comp_aemeasurable hXm), ← AEMeasurable.map_map_of_aemeasurable hm₁.aemeasurable hXm,
    ← AEMeasurable.map_map_of_aemeasurable hm₂.aemeasurable hXm, ← hind,
    AEMeasurable.map_map_of_aemeasurable (hm₁.prodMk hm₂).aemeasurable hXm]
  rfl

end NLAlib
