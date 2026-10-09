import NLAlib.Gaussian.Moments
import NLAlib.Matrix.Gram
import NLAlib.Matrix.PolarFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Rank of a fixed matrix times a Gaussian sketch

The proof uses deterministic basis witnesses and nonzero determinant polynomials.
No inverse-Wishart moment or density bound is used. Atlas `gaussian-full-rank-ae`,
`gn-expected-error`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Whenever `t≤rank A`, a deterministic right sketch can select `t` independent
vectors in the range of `A`. Atlas `gn-expected-error` (Gaussian rank witness). -/
theorem exists_right_sketch_rank_eq_of_le_rank {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (ht : t ≤ A.rank) :
    ∃ Z : Matrix (Fin n) (Fin t) ℝ, (A * Z).rank = t := by
  classical
  let b : Module.Basis (Fin A.rank) ℝ (LinearMap.range A.mulVecLin) :=
    Module.finBasis ℝ (LinearMap.range A.mulVecLin)
  let e : Fin t ↪ Fin A.rank := Fin.castLEEmb ht
  have hpre : ∀ i : Fin A.rank, ∃ z : Fin n → ℝ, A *ᵥ z = (b i : Fin m → ℝ) :=
    fun i => (b i).property
  choose z hz using hpre
  let Z : Matrix (Fin n) (Fin t) ℝ := fun i j => z (e j) i
  have hli : LinearIndependent ℝ (fun j : Fin t => (b (e j) : Fin m → ℝ)) :=
    (b.linearIndependent.map' (LinearMap.range A.mulVecLin).subtype
      (Submodule.ker_subtype _)).comp e e.injective
  have hrow : ((A * Z)ᵀ).row = fun j => A *ᵥ z (e j) := rfl
  have hliRow : LinearIndependent ℝ ((A * Z)ᵀ).row := by
    rw [hrow]
    simpa only [hz] using hli
  refine ⟨Z, ?_⟩
  have hRank := hliRow.rank_matrix
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hRank

/-- A Gaussian right sketch has full column rank after multiplication by `A` whenever
the number of sketch columns is at most `rank A`. The determinant polynomial has a
nonzero deterministic basis witness, so no density or inverse-moment assumption is
required. HMT 2011, Proposition A.5; atlas `gaussian-full-rank-ae`, `gn-expected-error`. -/
theorem gaussianMatrix_ae_isUnit_gram_mul_of_le_rank {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (ht : t ≤ A.rank) :
    ∀ᵐ G ∂gaussianMatrix n t, IsUnit ((A * Matrix.of G)ᵀ * (A * Matrix.of G)) := by
  classical
  obtain ⟨Z, hZ⟩ := exists_right_sketch_rank_eq_of_le_rank A ht
  let X : Matrix (Fin n) (Fin t) (MvPolynomial (Fin n × Fin t) ℝ) :=
    Matrix.mvPolynomialX (Fin n) (Fin t) ℝ
  let Y := A.map MvPolynomial.C * X
  let p := (Yᵀ * Y).det
  have hEval (G : Fin n → Fin t → ℝ) :
      MvPolynomial.eval (fun ab => G ab.1 ab.2) p =
        ((A * Matrix.of G)ᵀ * (A * Matrix.of G)).det := by
    dsimp [p, Y]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    simp only [Matrix.map_mul, Matrix.transpose_map]
    have hAmap : (A.map MvPolynomial.C).map
        (MvPolynomial.eval fun ab : Fin n × Fin t => G ab.1 ab.2) = A := by
      ext i j
      simp
    have hXmap : X.map (MvPolynomial.eval fun ab : Fin n × Fin t => G ab.1 ab.2) = Matrix.of G := by
      ext i j
      simp [X]
    rw [hAmap, hXmap]
  have hdetZ : ((A * Z)ᵀ * (A * Z)).det ≠ 0 :=
    det_ne_zero_of_rank_eq _ (by rw [Matrix.rank_transpose_mul_self, hZ, Fintype.card_fin])
  have hp : p ≠ 0 := by
    intro hzero
    have he := hEval (Matrix.of.symm Z)
    rw [hzero, map_zero] at he
    exact hdetZ he.symm
  filter_upwards [gaussianMatrix_ae_eval_ne_zero n t p hp] with G hG
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  rw [← hEval G]
  exact hG

/-- Selecting the first `q` columns of an `n×t` standard Gaussian matrix gives the
`n×q` standard Gaussian law. HMT 2011, §10.2; atlas `gaussian-matrix-def`,
`gn-expected-error` (rank-deficient first-sketch helper). -/
theorem gaussianMatrix_map_first_cols (n : ℕ) {q t : ℕ} (hqt : q ≤ t) :
    (gaussianMatrix n t).map (fun G i j => G i (Fin.castLE hqt j)) = gaussianMatrix n q := by
  let νt : Measure (Fin t → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let νq : Measure (Fin q → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e : Fin q ↪ Fin t := Fin.castLEEmb hqt
  have hAll : iIndepFun (fun i (x : Fin t → ℝ) => x i) νt :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  have hSub : iIndepFun (fun i (x : Fin t → ℝ) => x (e i)) νt :=
    iIndepFun.precomp e.injective hAll
  have hMap : νt.map (fun x i => x (e i)) = νq := by
    have h := iIndepFun.map_fun_eq_pi_map
      (fun i => (measurable_pi_apply (e i)).aemeasurable) hSub
    have hCoord : ∀ i : Fin q, νt.map (fun x => x (e i)) = gaussianReal 0 1 :=
      fun i => (measurePreserving_eval (fun _ : Fin t => gaussianReal 0 1) (e i)).map_eq
    simpa only [hCoord] using h
  have hRow : MeasurePreserving (fun x : Fin t → ℝ => fun i => x (e i)) νt νq :=
    ⟨measurable_pi_lambda _ fun i => measurable_pi_apply (e i), hMap⟩
  have hFull := measurePreserving_pi (fun _ : Fin n => νt) (fun _ : Fin n => νq)
    (fun _ => hRow)
  exact hFull.map_eq

/-- **Exact rank of a Gaussian right sketch.** Every fixed real matrix satisfies
`rank(AΩ)=min(rank A,t)` almost surely for an `n×t` standard Gaussian right sketch.
Rank-deficient matrices and empty dimensions are included. HMT 2011, Proposition A.5;
atlas `gaussian-full-rank-ae`, `gn-expected-error`. -/
theorem gaussianMatrix_ae_rank_mul_eq_min {m n t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∀ᵐ G ∂gaussianMatrix n t, (A * Matrix.of G).rank = min A.rank t := by
  let q := min A.rank t
  have hqr : q ≤ A.rank := min_le_left _ _
  have hqt : q ≤ t := min_le_right _ _
  have hSmall := gaussianMatrix_ae_isUnit_gram_mul_of_le_rank A hqr
  rw [← gaussianMatrix_map_first_cols n hqt] at hSmall
  have hPrefixMeas : Measurable (fun G : Fin n → Fin t → ℝ =>
      fun (i : Fin n) (j : Fin q) => G i (Fin.castLE hqt j)) := by fun_prop
  have hAE : ∀ᵐ G ∂gaussianMatrix n t,
      IsUnit ((A * Matrix.of (fun i j => G i (Fin.castLE hqt j)))ᵀ *
        (A * Matrix.of (fun i j => G i (Fin.castLE hqt j)))) :=
    ae_of_ae_map hPrefixMeas.aemeasurable hSmall
  filter_upwards [hAE] with G hG
  have hRankSmall : (A * Matrix.of (fun i j => G i (Fin.castLE hqt j))).rank = q := by
    rw [← Matrix.rank_transpose_mul_self (A * Matrix.of (fun i j => G i (Fin.castLE hqt j))),
      Matrix.rank_of_isUnit _ hG, Fintype.card_fin]
  have hEq : A * Matrix.of (fun i j => G i (Fin.castLE hqt j)) =
      (A * Matrix.of G).submatrix id (Fin.castLE hqt) := rfl
  apply Nat.le_antisymm
  · exact le_min (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)
  · change q ≤ (A * Matrix.of G).rank
    rw [← hRankSmall, hEq]
    exact Matrix.rank_submatrix_le _ _ _

/-- The Gaussian sketch rank identity transported to an arbitrary probability space
through the actual array law. No rank or moment certificate is assumed.
HMT 2011, Proposition A.5; atlas `gn-expected-error`. -/
theorem ae_rank_mul_gaussian_eq_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m n t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Fin n → Fin t → ℝ)
    (hG : μ.map G = gaussianMatrix n t) :
    ∀ᵐ ω ∂μ, (A * Matrix.of (G ω)).rank = min A.rank t := by
  have h := gaussianMatrix_ae_rank_mul_eq_min A (t := t)
  rw [← hG] at h
  exact ae_of_ae_map (aemeasurable_of_map_eq_gaussianMatrix hG) h

/-- A matrix whose range is contained in `range A` and has the same rank as `A`
spans exactly that range. This is the deterministic exact-range step, not merely
the range-containment property used by normalized RSVD bounds.
Atlas `gn-expected-error` (exact-range helper). -/
theorem range_mulVecLin_mul_eq_of_rank_eq {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin t) ℝ)
    (hRank : (A * Z).rank = A.rank) :
    LinearMap.range (A * Z).mulVecLin = LinearMap.range A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨Z *ᵥ x, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  · exact hRank

/-- Every fixed real matrix has an orthonormal frame of exactly `rank A` columns
whose projector reproduces `A`. The frame may be chosen once for that fixed input;
no measurable choice as `A` varies is claimed. Zero-rank matrices are included.
Horn–Johnson §7.3; atlas `gn-expected-error` (rank-deficient sketch branch). -/
theorem exists_orthonormal_frame_reproducing_matrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q : Matrix (Fin m) (Fin A.rank) ℝ,
      HasOrthonormalCols Q ∧ Q * (Qᵀ * A) = A := by
  classical
  obtain ⟨Z, hZ⟩ := exists_right_sketch_rank_eq_of_le_rank A (le_refl A.rank)
  let Y := A * Z
  have hUnit : IsUnit (Yᵀ * Y) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    apply isUnit_iff_ne_zero.mpr
    apply det_ne_zero_of_rank_eq
    rw [Matrix.rank_transpose_mul_self]
    simpa only [Y, Fintype.card_fin] using hZ
  let Q := polarFrame Y
  have hOrth : HasOrthonormalCols Q := hasOrthonormalCols_polarFrame Y hUnit
  have hprojY : Q * (Qᵀ * Y) = Y := polarFrame_mul_transpose_mul_eq Y hUnit
  have hRange : LinearMap.range Y.mulVecLin = LinearMap.range A.mulVecLin :=
    range_mulVecLin_mul_eq_of_rank_eq A Z hZ
  have hCoeff : ∀ j : Fin n, ∃ v : Fin A.rank → ℝ, Y *ᵥ v = A.col j := by
    intro j
    have hmem : A.col j ∈ LinearMap.range A.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      simp [Matrix.mulVec_single]
    rw [← hRange] at hmem
    exact hmem
  choose v hv using hCoeff
  let C : Matrix (Fin A.rank) (Fin n) ℝ := fun i j => v j i
  have hFactor : Y * C = A := by
    ext i j
    exact congrFun (hv j) i
  refine ⟨Q, hOrth, ?_⟩
  calc
    Q * (Qᵀ * A) = Q * (Qᵀ * (Y * C)) :=
      congrArg (fun B : Matrix (Fin m) (Fin n) ℝ => Q * (Qᵀ * B)) hFactor.symm
    _ = (Q * (Qᵀ * Y)) * C := by simp only [Matrix.mul_assoc]
    _ = Y * C := by rw [hprojY]
    _ = A := hFactor

set_option backward.isDefEq.respectTransparency false in
/-- A fixed matrix and Gaussian sketch width admit a constructed entrywise measurable
orthonormal range frame of `min(rank A,t)` columns almost surely. The full-column branch
uses the polar map; the rank-deficient branch uses a fixed frame of `range A`. Thus no
measurable-frame certificate has to be assumed in normalized Gaussian algorithms.
HMT 2011, §10.2; atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem exists_measurable_gaussian_range_frame {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℕ) :
    ∃ Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin (min A.rank t)) ℝ,
      (∀ i j, Measurable fun G => Qf G i j) ∧
      (∀ᵐ G ∂gaussianMatrix n t, HasOrthonormalCols (Qf G)) ∧
      ∀ᵐ G ∂gaussianMatrix n t,
        Qf G * ((Qf G)ᵀ * (A * Matrix.of G)) = A * Matrix.of G := by
  by_cases hrt : A.rank ≤ t
  · rw [min_eq_left hrt]
    obtain ⟨Q, hQo, hQA⟩ := exists_orthonormal_frame_reproducing_matrix A
    refine ⟨fun _ => Q, fun _ _ => measurable_const, ae_of_all _ fun _ => hQo, ?_⟩
    apply ae_of_all
    intro G
    calc
      Q * (Qᵀ * (A * Matrix.of G)) = (Q * (Qᵀ * A)) * Matrix.of G := by
        simp only [Matrix.mul_assoc]
      _ = A * Matrix.of G := by rw [hQA]
  · have htr : t ≤ A.rank := (not_le.mp hrt).le
    rw [min_eq_right htr]
    let Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin t) ℝ :=
      fun G => polarFrame (A * Matrix.of G)
    have hQf : ∀ i j, Measurable fun G => Qf G i j := by
      have hY : ∀ a b, Measurable fun G : Fin n → Fin t → ℝ => (A * Matrix.of G) a b :=
        measurable_mul_entry_of (fun _ _ => measurable_const)
          (fun _ _ => by simp only [Matrix.of_apply]; fun_prop)
      have hArray : Measurable fun G : Fin n → Fin t → ℝ => Matrix.of.symm (A * Matrix.of G) :=
        measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hY a b
      intro i j
      exact (measurable_polarFrame_entry i j).comp hArray
    have hGood := gaussianMatrix_ae_isUnit_gram_mul_of_le_rank A htr
    refine ⟨Qf, hQf, ?_, ?_⟩
    · filter_upwards [hGood] with G hG
      exact hasOrthonormalCols_polarFrame (A * Matrix.of G) hG
    · filter_upwards [hGood] with G hG
      exact polarFrame_mul_transpose_mul_eq (A * Matrix.of G) hG

/-- A fixed choice of the constructed measurable Gaussian range frame. It is an
orthonormal exact-range frame almost surely and has `min(rank A,t)` columns.
No claim of joint measurability as the fixed input matrix `A` varies is needed.
HMT 2011, §10.2; atlas `rsvd-expected-error`, `gn-expected-error`. -/
def gaussianRangeFrame {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (t : ℕ) :
    (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin (min A.rank t)) ℝ :=
  (exists_measurable_gaussian_range_frame A t).choose

/-- The constructed Gaussian range frame is entrywise measurable.
Atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem measurable_gaussianRangeFrame_entry {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℕ) (i : Fin m) (j : Fin (min A.rank t)) :
    Measurable fun G => gaussianRangeFrame A t G i j :=
  (exists_measurable_gaussian_range_frame A t).choose_spec.1 i j

/-- The constructed Gaussian range frame has orthonormal columns almost surely.
Atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem gaussianMatrix_ae_hasOrthonormalCols_gaussianRangeFrame {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℕ) :
    ∀ᵐ G ∂gaussianMatrix n t, HasOrthonormalCols (gaussianRangeFrame A t G) :=
  (exists_measurable_gaussian_range_frame A t).choose_spec.2.1

/-- The projector of the constructed Gaussian range frame reproduces the first
sketch almost surely. Combined with the proved Gaussian rank identity, this is exact
range equality. Atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem gaussianMatrix_ae_project_gaussianRangeFrame {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℕ) :
    ∀ᵐ G ∂gaussianMatrix n t, gaussianRangeFrame A t G *
      ((gaussianRangeFrame A t G)ᵀ * (A * Matrix.of G)) = A * Matrix.of G :=
  (exists_measurable_gaussian_range_frame A t).choose_spec.2.2

/-- Transport the constructed frame's orthonormality through an actual Gaussian array
law on an abstract probability space. No frame certificate is supplied.
Atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Fin n → Fin t → ℝ)
    (hG : μ.map G = gaussianMatrix n t) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (gaussianRangeFrame A t (G ω)) := by
  have h := gaussianMatrix_ae_hasOrthonormalCols_gaussianRangeFrame A t
  rw [← hG] at h
  exact ae_of_ae_map (aemeasurable_of_map_eq_gaussianMatrix hG) h

/-- Transport the constructed frame's range property through an actual Gaussian array
law on an abstract probability space. No range certificate is supplied.
Atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem ae_project_gaussianRangeFrame_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Fin n → Fin t → ℝ)
    (hG : μ.map G = gaussianMatrix n t) :
    ∀ᵐ ω ∂μ, gaussianRangeFrame A t (G ω) *
      ((gaussianRangeFrame A t (G ω))ᵀ * (A * Matrix.of (G ω))) = A * Matrix.of (G ω) := by
  have h := gaussianMatrix_ae_project_gaussianRangeFrame A t
  rw [← hG] at h
  exact ae_of_ae_map (aemeasurable_of_map_eq_gaussianMatrix hG) h

end NLAlib
