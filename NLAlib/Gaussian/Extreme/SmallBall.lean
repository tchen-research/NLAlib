import NLAlib.Matrix.Spectral
import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.Extreme.ChiSquare
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Small-ball estimate for the smallest singular value of a Gaussian matrix

For an `N × n` standard Gaussian matrix `A` with `n ≤ N`,
`P(σ_min(A) ≤ s) ≤ n (e n s² / (N - n + 1))^{(N - n + 1)/2}` whenever `n s² ≤ N - n + 1`.

The argument (Davidson–Szarek 2001, Thm II.13; Vershynin 2012, §5.2 / Rudelson–Vershynin
2009) has three steps:

* `exists_iInf_sqrt_mulVec_le_of_sigmaMin_le` (deterministic): if `σ_min(A) ≤ s` then some
  column `j` is within `√n · s` of the span of the others, written as
  `inf { ‖A x‖₂ : x_j = 1 }`;
* `measure_sq_dist_colSpace_le_le_gaussianReal`: the squared distance from a standard Gaussian
  vector to a fixed subspace of codimension at least `d` is stochastically larger than `χ²_d`,
  so it obeys the chi-square lower tail `(e u / d)^{d/2}`;
* `measure_sq_dist_col_span_le_le_gaussianMatrix`: by resampling column `j` independently, the
  distance from column `j` to the span of the others satisfies the same bound with
  `d = N - n + 1`;

and `measure_sigmaMin_le_le_gaussianMatrix` is the union bound over the columns.

Helpers of general use: `measurePreserving_orthonormalBasis_repr_pi_gaussianReal` (coordinates
of a standard Gaussian vector in an orthonormal basis are i.i.d. standard Gaussian),
`measurePreserving_update_pi_gaussianReal` and `measurePreserving_updateCol_gaussianMatrix`
(resampling a coordinate / a column).

Atlas: `smin-small-ball`. Proofs ported from the Prove2me Gaussian series (solutions
`sMin_le_imp_dist_le`, `gaussian_dist_colspace_small_ball`, `dist_col_span_small_ball`,
`sMin_small_ball`). The deterministic step is generalised from `Fin N × Fin n` to arbitrary
finite index types.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace NLAlib

/-! ### Deterministic step -/

/-- `‖A (c • x)‖₂ = |c| ‖A x‖₂` in the `√(v ⬝ v)` form. Atlas: `smin-small-ball` (helper).
Ported from Prove2me solution `GaussianMatrix.sMin_le_imp_dist_le`. -/
theorem sqrt_mulVec_smul_dotProduct {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (c : ℝ) (x : n → ℝ) :
    Real.sqrt ((A *ᵥ (c • x)) ⬝ᵥ (A *ᵥ (c • x))) = |c| * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- For a unit vector `x`, some column `j` satisfies `inf { ‖A y‖₂ : y_j = 1 } ≤ √n ‖A x‖₂`
(take `j` maximising `|x_j|`, so `|x_j| ≥ 1/√n`, and `y = x / x_j`). -/
private lemma exists_iInf_sqrt_mulVec_le_of_dotProduct_self_eq_one {m n : Type*} [Fintype m]
    [Fintype n] [Nonempty n] (A : Matrix m n ℝ) (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    ∃ j : n, (⨅ y : {y : n → ℝ // y j = 1}, Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1)))
      ≤ Real.sqrt (Fintype.card n) * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  -- `1 ≤ n * x_j²`
  have hsum : (1 : ℝ) ≤ Fintype.card n * x j ^ 2 := by
    have h1 : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
    have h2 : ∑ i, x i ^ 2 ≤ ∑ _i : n, x j ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hj i (Finset.mem_univ _)
      rw [← sq_abs (x i), ← sq_abs (x j)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    linarith
  have hxj : x j ≠ 0 := by
    intro h; rw [h] at hsum; norm_num at hsum
  have hxa : 0 < |x j| := abs_pos.2 hxj
  -- `1 ≤ √n |x_j|`
  have hsq : 1 ≤ Real.sqrt (Fintype.card n) * |x j| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.one_le_sqrt.2 hsum
  set y : n → ℝ := (x j)⁻¹ • x with hy
  have hyj : y j = 1 := by simp [hy, hxj]
  have hbdd : BddBelow (Set.range fun y : {y : n → ℝ // y j = 1} =>
      Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1))) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd ⟨y, hyj⟩).trans ?_
  show Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ _
  rw [hy, sqrt_mulVec_smul_dotProduct, abs_inv]
  set F := Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  rw [inv_mul_le_iff₀ hxa]
  nlinarith

/-- **Small `σ_min` forces a column close to the span of the others.** For `A : Matrix m n ℝ`
with `n` nonempty, if `σ_min(A) ≤ s` then for some column `j`,
`inf { ‖A x‖₂ : x_j = 1 } ≤ √|n| · s`; the left side is the distance from column `j` to the
span of the other columns.

Davidson–Szarek 2001, proof of Thm II.13; Rudelson–Vershynin 2008, Lemma 3.5 (the
"invertibility via distance" step). Atlas: `smin-small-ball`. Generalised from
`Fin N × Fin n` (with `1 ≤ n`) to arbitrary finite index types with `n` nonempty. Ported from
Prove2me solution `GaussianMatrix.sMin_le_imp_dist_le`. -/
theorem exists_iInf_sqrt_mulVec_le_of_sigmaMin_le {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty n] (A : Matrix m n ℝ) (s : ℝ) (hs : sigmaMin A ≤ s) :
    ∃ j : n, (⨅ x : {x : n → ℝ // x j = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)))
      ≤ Real.sqrt (Fintype.card n) * s := by
  set D : n → ℝ := fun j =>
    ⨅ x : {x : n → ℝ // x j = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) with hD
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ D Finset.univ_nonempty
  refine ⟨j₀, ?_⟩
  have hn0 : 0 < Real.sqrt (Fintype.card n) :=
    Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  -- `D j₀ / √n ≤ σ_min(A)`
  have hlow : D j₀ / Real.sqrt (Fintype.card n) ≤ sigmaMin A := by
    refine le_sigmaMin A fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_iInf_sqrt_mulVec_le_of_dotProduct_self_eq_one A x hx
    rw [div_le_iff₀ hn0]
    calc D j₀ ≤ D j := hj₀ j (Finset.mem_univ _)
      _ ≤ _ := by rw [mul_comm]; exact hj
  have := (div_le_iff₀ hn0).1 (hlow.trans hs)
  linarith

/-! ### Distance from a Gaussian vector to a fixed subspace -/

/-- **Rotation invariance in coordinates.** For an orthonormal basis `b` of `ℝᴺ` indexed by `ι`,
the coordinates `(⟪b i, g⟫)ᵢ` of a standard Gaussian vector `g` are i.i.d. standard Gaussian.
Atlas: `smin-small-ball` (helper; an instance of `gaussian-rotation-invariance`). Ported from
Prove2me solution `GaussianMatrix.gaussian_dist_colspace_small_ball`. -/
theorem measurePreserving_orthonormalBasis_repr_pi_gaussianReal {N : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin N))) :
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

/-- **Small ball for the distance to a subspace.** Let `B : Matrix (Fin N) (Fin p) ℝ` have
`rank B + d ≤ N` with `d ≥ 1`. For a standard Gaussian vector `g ∈ ℝᴺ` and `0 ≤ u ≤ d`,
`P(dist(g, range B)² ≤ u) ≤ (e u / d)^{d/2}`, with `dist(g, range B) = inf_c ‖g - B c‖₂`.

The squared distance dominates the sum of squares of `d` coordinates of `g` in an orthonormal
basis of `(range B)ᗮ` (Bessel), which is `χ²_d` by rotation invariance; then the chi-square lower
tail. Davidson–Szarek 2001, proof of Thm II.13; Vershynin 2012, §5.2.
Atlas: `smin-small-ball` (step). Ported from Prove2me solution
`GaussianMatrix.gaussian_dist_colspace_small_ball`. -/
theorem measure_sq_dist_colSpace_le_le_gaussianReal {N p d : ℕ} (B : Matrix (Fin N) (Fin p) ℝ)
    (hd : 1 ≤ d) (hrank : B.rank + d ≤ N) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ d) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      {g | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by
  /- Geometry: the column space `V` of `B`, an orthonormal family `w` of `d` vectors in `Vᗮ`,
  and an orthonormal basis `b` of `ℝᴺ` (indexed by `Fin d ⊕ Fin (N - d)`) extending `w`. -/
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap
      (LinearMap.range B.mulVecLin)
  have hV : Module.finrank ℝ V = B.rank := by
    rw [Matrix.rank]; exact LinearEquiv.finrank_map_eq _ _
  have hmemV : ∀ c : Fin p → ℝ, WithLp.toLp 2 (B *ᵥ c) ∈ V := fun c =>
    Submodule.mem_map.2 ⟨B *ᵥ c, ⟨c, rfl⟩, rfl⟩
  have hW : d ≤ Module.finrank ℝ Vᗮ := by
    have := Submodule.finrank_add_finrank_orthogonal V
    rw [finrank_euclideanSpace_fin] at this; omega
  let bW := stdOrthonormalBasis ℝ Vᗮ
  let w : Fin d → EuclideanSpace ℝ (Fin N) := fun k => (bW (Fin.castLE hW k) : _)
  have hw : Orthonormal ℝ w :=
    (bW.orthonormal.comp _ (Fin.castLE_injective hW)).comp_linearIsometry Vᗮ.subtypeₗᵢ
  have hwV : ∀ k, w k ∈ Vᗮ := fun k => (bW (Fin.castLE hW k)).2
  let v : Fin d ⊕ Fin (N - d) → EuclideanSpace ℝ (Fin N) := Sum.elim w 0
  have hv : Orthonormal ℝ
      ((Set.range (Sum.inl : Fin d → Fin d ⊕ Fin (N - d))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, ⟨k, rfl⟩⟩ ⟨_, ⟨l, rfl⟩⟩
    have h1 := (orthonormal_iff_ite.1 hw) k l
    by_cases hkl : k = l
    · subst hkl; simpa [Set.domRestrict_apply, v] using h1
    · rw [if_neg (fun h => hkl (Sum.inl_injective (congrArg Subtype.val h)))]
      simpa [Set.domRestrict_apply, v, hkl] using h1
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        omega)
  have hbk : ∀ k, b (Sum.inl k) = w k := fun k => hb _ ⟨k, rfl⟩
  /- Bessel: the squared distance to `V` dominates `∑ₖ ⟪w k, g⟫²`. -/
  have hbessel : ∀ g : Fin N → ℝ,
      ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2
        ≤ (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 := by
    intro g
    have hS0 : 0 ≤ ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2 := by positivity
    have hc : ∀ c : Fin p → ℝ, Real.sqrt (∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2)
        ≤ Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c)) := by
      intro c
      refine Real.sqrt_le_sqrt ?_
      have h1 : ∀ k, ⟪w k, WithLp.toLp 2 g⟫ = ⟪w k, WithLp.toLp 2 (g - B *ᵥ c)⟫ := by
        intro k
        rw [WithLp.toLp_sub, inner_sub_right,
          Submodule.inner_left_of_mem_orthogonal (hmemV c) (hwV k), sub_zero]
      have h2 := hw.sum_inner_products_le (x := WithLp.toLp 2 (g - B *ᵥ c))
        (s := Finset.univ)
      rw [EuclideanSpace.real_norm_sq_eq] at h2
      simp only [Real.norm_eq_abs, sq_abs] at h2
      simp_rw [h1]
      refine h2.trans (le_of_eq ?_)
      simp [dotProduct, sq]
    have hle := le_ciInf hc
    calc ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2
        = Real.sqrt (∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2) ^ 2 := (Real.sq_sqrt hS0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  /- Probability: rotate and take the marginal on the first `d` coordinates. -/
  set T : (Fin N → ℝ) → (Fin d ⊕ Fin (N - d) → ℝ) :=
    fun g => WithLp.ofLp (b.repr (WithLp.toLp 2 g)) with hT_def
  have hT := measurePreserving_orthonormalBasis_repr_pi_gaussianReal b
  set C' : Set (Fin d ⊕ Fin (N - d) → ℝ) := {h | ∑ k : Fin d, h (Sum.inl k) ^ 2 ≤ u} with hC'
  have hC'm : MeasurableSet C' := by
    refine measurableSet_le ?_ measurable_const
    exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).pow_const 2
  have hsub : {g : Fin N → ℝ |
      (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u} ⊆ T ⁻¹' C' := by
    intro g hg
    simp only [Set.mem_preimage, hC', Set.mem_ofPred_eq, hT_def] at hg ⊢
    refine le_trans (le_of_eq ?_) ((hbessel g).trans hg)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthonormalBasis.repr_apply_apply, hbk]
  have hmarg : (Measure.pi fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1) C'
      = (Measure.pi fun _ : Fin d => gaussianReal 0 1) {g | ∑ i, g i ^ 2 ≤ u} := by
    have he := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1)
    have hpre : C' = (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ Fin (N - d) => ℝ) ⁻¹'
        ({g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ u} ×ˢ Set.univ) := by
      ext h; simp [hC', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
    have hC0 : MeasurableSet {g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ u} := by
      refine measurableSet_le ?_ measurable_const
      exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).pow_const 2
    rw [hpre, he.measure_preimage (hC0.prod MeasurableSet.univ).nullMeasurableSet,
      Measure.prod_prod, measure_univ, mul_one]
  calc (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        {g | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ≤ (Measure.pi fun _ : Fin N => gaussianReal 0 1) (T ⁻¹' C') := measure_mono hsub
    _ = (Measure.pi fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1) C' :=
        hT.measure_preimage hC'm.nullMeasurableSet
    _ = _ := hmarg
    _ ≤ _ := measure_sum_sq_le_le_gaussianReal hd u hu hud

/-! ### Distance from a Gaussian column to the span of the others -/

/-- **Resampling one coordinate.** `(a, g) ↦ update a j g` pushes `γⁿ ⊗ γ` forward to `γⁿ`,
where `γ = N(0,1)`. Atlas: `smin-small-ball` (helper). Ported from Prove2me solution
`GaussianMatrix.dist_col_span_small_ball`. -/
theorem measurePreserving_update_pi_gaussianReal {n : ℕ} (j : Fin n) :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hmeas : Measurable (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2) := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s j Set.univ) ×ˢ s j := by
    ext ⟨a, g⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun l => ?_, by simpa using h j⟩
      by_cases hl : l = j
      · subst hl; simp
      · have := h l
        rw [Function.update_of_ne hl] at this
        rw [Function.update_of_ne hl]; exact this
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = j
      · subst hl; simpa using h2
      · have := h1 l
        rw [Function.update_of_ne hl] at this
        rw [Function.update_of_ne hl]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => gaussianReal 0 1 (s i)) (Finset.mem_univ j),
    Function.update_self, measure_univ, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- **Resampling one column of a Gaussian matrix.** Replacing column `j` of a standard Gaussian
matrix by an independent standard Gaussian vector leaves its law unchanged.
Atlas: `smin-small-ball` (helper). Ported from Prove2me solution
`GaussianMatrix.dist_col_span_small_ball` (`measurePreserving_updateCol`). -/
theorem measurePreserving_updateCol_gaussianMatrix (N n : ℕ) (j : Fin n) :
    MeasurePreserving
      (fun p : (Fin N → Fin n → ℝ) × (Fin N → ℝ) => fun i => Function.update (p.1 i) j (p.2 i))
      ((gaussianMatrix N n).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1))
      (gaussianMatrix N n) := by
  have h1 := MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ
    (Fin N) (fun _ => Measure.pi fun _ : Fin n => gaussianReal 0 1) (fun _ => gaussianReal 0 1))
  have h2 := measurePreserving_pi
    (fun _ : Fin N => (Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (fun _ => measurePreserving_update_pi_gaussianReal j)
  exact h2.comp h1

/-- The distance from column `j` to the span of the other columns is measurable (an infimum of
continuous functions, hence upper semicontinuous). -/
private lemma measurable_iInf_sqrt_mulVec {N n : ℕ} (j : Fin n) :
    Measurable (fun A : Fin N → Fin n → ℝ => ⨅ x : {x : Fin n → ℝ // x j = 1},
        Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) := by
  refine UpperSemicontinuous.measurable ?_
  refine upperSemicontinuous_ciInf (fun A => ⟨0, ?_⟩) fun x => ?_
  · rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _
  · refine Continuous.upperSemicontinuous ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop

/-- Zeroing one column leaves rank at most `n - 1`. -/
private lemma rank_update_col_zero_le {N n : ℕ} (A : Fin N → Fin n → ℝ) (j : Fin n) :
    (Matrix.of fun i l => Function.update (A i) j 0 l).rank ≤ n - 1 := by
  let B' : Matrix (Fin N) {l : Fin n // l ≠ j} ℝ := Matrix.of fun i l => A i l.1
  let E : Matrix {l : Fin n // l ≠ j} (Fin n) ℝ := Matrix.of fun l k => if k = l.1 then 1 else 0
  have hBE : (Matrix.of fun i l => Function.update (A i) j 0 l) = B' * E := by
    ext i k
    simp only [B', E, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg]; intro h; exact l.2 h.symm
    · rw [Function.update_of_ne hk, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro h; apply hb; exact Subtype.ext h.symm
      · simp
  rw [hBE]
  calc (B' * E).rank ≤ B'.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card {l : Fin n // l ≠ j} := Matrix.rank_le_card_width _
    _ = n - 1 := by simp [Fintype.card_subtype_compl]

/-- With `x j = 1`, `A' x = g - B (-x)` where `A'` is `A` with column `j` replaced by `g` and
`B` is `A` with column `j` zeroed. -/
private lemma updateCol_mulVec {N n : ℕ} (A : Fin N → Fin n → ℝ) (g : Fin N → ℝ) (j : Fin n)
    (x : Fin n → ℝ) (hx : x j = 1) :
    Matrix.of (fun i => Function.update (A i) j (g i)) *ᵥ x
      = g - (Matrix.of fun i l => Function.update (A i) j 0 l) *ᵥ (-x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.neg_apply,
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  have h : ∀ l, Function.update (A i) j (g i) l * x l
      = Function.update (A i) j 0 l * x l + (if l = j then g i * x l else 0) := by
    intro l
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), hx, mul_one, add_comm]

/-- **Small ball for the distance from a column to the span of the others.** For an `N × n`
standard Gaussian matrix `A` with `n ≤ N`, any column `j` and `0 ≤ u ≤ N - n + 1`,
`P(dist(A_j, span{A_l : l ≠ j})² ≤ u) ≤ (e u / (N - n + 1))^{(N - n + 1)/2}`, the distance
being written `inf { ‖A x‖₂ : x_j = 1 }`.

Condition on the other columns (resample column `j`) and apply the subspace small-ball bound
with `d = N - n + 1`. Davidson–Szarek 2001, proof of Thm II.13; Vershynin 2012, §5.2.
Atlas: `smin-small-ball` (step). Ported from Prove2me solution
`GaussianMatrix.dist_col_span_small_ball`. -/
theorem measure_sq_dist_col_span_le_le_gaussianMatrix {N n : ℕ} (hnN : n ≤ N) (j : Fin n)
    (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | (⨅ x : {x : Fin n → ℝ // x j = 1},
        Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
  have hS : MeasurableSet {A : Fin N → Fin n → ℝ | (⨅ x : {x : Fin n → ℝ // x j = 1},
      Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) ^ 2 ≤ u} :=
    measurableSet_le ((measurable_iInf_sqrt_mulVec j).pow_const 2) measurable_const
  have hΦ := measurePreserving_updateCol_gaussianMatrix N n j
  rw [← hΦ.measure_preimage hS.nullMeasurableSet, Measure.prod_apply (hΦ.measurable hS)]
  have hd : ((N - n + 1 : ℕ) : ℝ) = (N : ℝ) - n + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hnN, Nat.cast_one]
  set bound := ENNReal.ofReal ((Real.exp 1 * u / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2))
  calc ∫⁻ A, (Measure.pi fun _ : Fin N => gaussianReal 0 1) _ ∂(gaussianMatrix N n)
      ≤ ∫⁻ _, bound ∂(gaussianMatrix N n) := lintegral_mono fun A => ?_
    _ = bound := by rw [lintegral_const, measure_univ, mul_one]
  set B : Matrix (Fin N) (Fin n) ℝ := Matrix.of fun i l => Function.update (A i) j 0 l with hB
  have hrank : B.rank + (N - n + 1) ≤ N := by
    have : B.rank ≤ n - 1 := rank_update_col_zero_le A j
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact j.elim0)
    omega
  have key := measure_sq_dist_colSpace_le_le_gaussianReal B (d := N - n + 1) (by omega) hrank
    u hu (by rw [hd]; exact hud)
  rw [hd] at key
  refine le_trans (measure_mono ?_) key
  intro g hg
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hg ⊢
  refine le_trans (pow_le_pow_left₀ (Real.iInf_nonneg fun _ => Real.sqrt_nonneg _) ?_ 2) hg
  have hne : Nonempty {x : Fin n → ℝ // x j = 1} := ⟨⟨Pi.single j 1, by simp⟩⟩
  refine le_ciInf fun x => ?_
  have hbdd : BddBelow (Set.range fun c : Fin n → ℝ =>
      Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) :=
    ⟨0, by rintro _ ⟨c, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd (-x.1)).trans (le_of_eq ?_)
  rw [hB, ← updateCol_mulVec A g j x.1 x.2]

/-! ### Small ball for `σ_min` -/

/-- **Small-ball estimate for the smallest singular value of a Gaussian matrix.** For an
`N × n` standard Gaussian matrix `A` with `1 ≤ n ≤ N` and `n s² ≤ N - n + 1`,
`P(σ_min(A) ≤ s) ≤ n · (e n s² / (N - n + 1))^{(N - n + 1)/2}`. The source's hypothesis
`0 ≤ s` is not needed and is dropped.

Davidson–Szarek 2001, Thm II.13 (small-ball form); Vershynin 2012, §5.2 /
Rudelson–Vershynin 2009 (sharper `(C s √N)^{N-n+1}` form). Union bound over the columns of the
column-distance estimate. Atlas: `smin-small-ball`. Ported from Prove2me solution
`GaussianMatrix.sMin_small_ball`. -/
theorem measure_sigmaMin_le_le_gaussianMatrix {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (s : ℝ)
    (hsd : n * s ^ 2 ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | sigmaMin (Matrix.of A) ≤ s}
      ≤ ENNReal.ofReal
          (n * (Real.exp 1 * n * s ^ 2 / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set D : Fin n → (Fin N → Fin n → ℝ) → ℝ := fun j A =>
    ⨅ x : {x : Fin n → ℝ // x j = 1},
      Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1)) with hD
  have hD0 : ∀ j A, 0 ≤ D j A := fun j A =>
    Real.iInf_nonneg fun x => Real.sqrt_nonneg _
  have hsub : {A : Fin N → Fin n → ℝ | sigmaMin (Matrix.of A) ≤ s}
      ⊆ ⋃ j : Fin n, {A | D j A ^ 2 ≤ n * s ^ 2} := by
    intro A hA
    obtain ⟨j, hj⟩ := exists_iInf_sqrt_mulVec_le_of_sigmaMin_le (Matrix.of A) s hA
    rw [Fintype.card_fin] at hj
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    show D j A ^ 2 ≤ n * s ^ 2
    have h1 : D j A ^ 2 ≤ (Real.sqrt n * s) ^ 2 := pow_le_pow_left₀ (hD0 j A) hj 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at h1
  have hu0 : 0 ≤ (n : ℝ) * s ^ 2 := by positivity
  calc (gaussianMatrix N n) {A | sigmaMin (Matrix.of A) ≤ s}
      ≤ (gaussianMatrix N n) (⋃ j : Fin n, {A | D j A ^ 2 ≤ n * s ^ 2}) := measure_mono hsub
    _ ≤ ∑ j : Fin n, (gaussianMatrix N n) {A | D j A ^ 2 ≤ n * s ^ 2} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal
          ((Real.exp 1 * (n * s ^ 2) / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) :=
        Finset.sum_le_sum fun j _ =>
          measure_sq_dist_col_span_le_le_gaussianMatrix hnN j (n * s ^ 2) hu0 hsd
    _ = ENNReal.ofReal
          (n * (Real.exp 1 * n * s ^ 2 / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, mul_assoc]

end NLAlib
