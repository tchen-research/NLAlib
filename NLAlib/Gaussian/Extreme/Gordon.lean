import Mathlib.Algebra.Order.Archimedean.Real.Hom
import NLAlib.Matrix.Spectral
import NLAlib.Gaussian.Comparison.SudakovFernique
import NLAlib.Gaussian.Comparison.GordonMinimax
import NLAlib.Gaussian.Comparison.ExpectationNormDiff
import NLAlib.Gaussian.Extreme.LinearForms

/-!
# Gordon's bounds for the extreme singular values of a Gaussian matrix

For an `N × n` standard Gaussian matrix `G` (Vershynin 2012, Thm 5.32; Gordon 1985;
Davidson–Szarek 2001, Thm II.13):

* `integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt`: `𝔼 ‖G‖₂ ≤ √N + √n`;
* `sqrt_sub_sqrt_le_integral_sigmaMin_gaussianMatrix`: `√N - √n ≤ 𝔼 σ_min(G)` (`n ≥ 1`);
* `gordon_extreme_singular_values`: both, with integrability of `σ_min(G)` and `‖G‖₂` and
  `𝔼 σ_min(G) ≤ 𝔼 ‖G‖₂`, i.e. `√N - √n ≤ 𝔼 σ_min(G) ≤ 𝔼 σ_max(G) ≤ √N + √n`.

Here `σ_min(G) = NLAlib.sigmaMin G = inf_{‖x‖ = 1} ‖G x‖₂` (the tall convention; for `N < n` it is
`0` and the lower bound is trivial) and `σ_max(G) = NLAlib.specNorm G`.

Proofs: write `‖G‖₂ = max_{u,v} ⟨v, G u⟩` and `σ_min(G) = min_u max_v ⟨v, G u⟩` over unit vectors,
discretise with finite `ε`-nets (`one_sub_two_mul_mul_specNorm_le_iSup` for the norm), compare the
process `⟨v, G u⟩` with `⟨g, u⟩ + ⟨h, v⟩` (`g ∈ ℝⁿ`, `h ∈ ℝᴺ` independent standard Gaussian
vectors, realised as one Gaussian row of length `n + N`) by the Sudakov–Fernique inequality
(upper bound) and Gordon's minimax inequality (lower bound), use `𝔼‖g_k‖ ≤ √k` and
`√N - √n ≤ 𝔼‖h_N‖ - 𝔼‖g_n‖`, and let `ε → 0`.

Ported from the Prove2me solutions `GaussianMatrix.gordon_upper`, `GaussianMatrix.gordon_lower`
and `GaussianMatrix.gordon`.

Atlas: `gordon`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Deterministic comparison of increments -/

/-- Coefficient comparison for unit vectors:
`‖v uᵀ - v' u'ᵀ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`. -/
private theorem gu_coeff_ineq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2 ≤ ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
  have su' : ∑ j, u' j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu', one_pow]
  have sv : ∑ i, v i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv, one_pow]
  have sv' : ∑ i, v' i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv', one_pow]
  set α := ∑ j, u j * u' j with hαdef
  set β := ∑ i, v i * v' i with hβdef
  have hL : ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2
      = (∑ i, v i ^ 2) * (∑ j, u j ^ 2) - 2 * (β * α) + (∑ i, v' i ^ 2) * (∑ j, u' j ^ 2) := by
    rw [hαdef, hβdef, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRu : ∑ j, (u j - u' j) ^ 2 = ∑ j, u j ^ 2 - 2 * α + ∑ j, u' j ^ 2 := by
    rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRv : ∑ i, (v i - v' i) ^ 2 = ∑ i, v i ^ 2 - 2 * β + ∑ i, v' i ^ 2 := by
    rw [hβdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : α ≤ 1 := by
    have : 0 ≤ ∑ j, (u j - u' j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hβ : β ≤ 1 := by
    have : 0 ≤ ∑ i, (v i - v' i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hL, hRu, hRv, su, su', sv, sv']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

/-- Increments of the comparison process `⟨g, u⟩ + ⟨h, v⟩`, written with one Gaussian row
`H₀ ∈ ℝ^{n+N}`. -/
private theorem gu_coeffY_sq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N)) :
    ∑ _i : Fin 1, ∑ k : Fin (n + N),
      (Fin.append (fun j => u j) (fun i => v i) k - Fin.append (fun j => u' j) (fun i => v' i) k) ^ 2
      = ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

private theorem gu_Y_le {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (H : Fin 1 → Fin (n + N) → ℝ) :
    linForm (fun _ k => Fin.append (fun j => u j) (fun i => v i) k) H
      ≤ Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2) + Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) := by
  unfold linForm
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => u j) (fun j => H 0 (Fin.castAdd N j))
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => v i) (fun i => H 0 (Fin.natAdd n i))
  rw [← norm_eq_sqrt_sum_sq, hu, one_mul] at h1
  rw [← norm_eq_sqrt_sum_sq, hv, one_mul] at h2
  exact add_le_add h1 h2


/-! ### Upper bound -/


open scoped Matrix.Norms.L2Operator in
/-- The comparison bound for a fixed net scale: `(1 - 2ε) 𝔼‖G‖ ≤ √N + √n`. -/
private theorem gu_scaled_bound {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    (1 - 2 * ε) * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n)
      ≤ Real.sqrt N + Real.sqrt n := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).totallyBounded ε hε
  set I := hFufin.toFinset ×ˢ hFvfin.toFinset with hIdef
  have hI1 : ∀ t ∈ I, ‖t.1‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFuS ht.1
  have hI2 : ∀ t ∈ I, ‖t.2‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFvS ht.2
  have hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N)), ‖u‖ = 1 →
      ‖v‖ = 1 → ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε := by
    intro u v hu hv
    have hu' : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hu
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := by simpa using hv
    obtain ⟨y, hy, hyu⟩ := Set.mem_iUnion₂.1 (hFucov hu')
    obtain ⟨z, hz, hzv⟩ := Set.mem_iUnion₂.1 (hFvcov hv')
    refine ⟨(y, z), ?_, ?_, ?_⟩
    · rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact ⟨hy, hz⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hyu; exact hyu.le
    · rw [Metric.mem_ball, dist_eq_norm] at hzv; exact hzv.le
  have hne : Nonempty I := by
    obtain ⟨t, ht, -⟩ := hcov (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1)
      (EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1) (by simp) (by simp)
    exact ⟨⟨t, ht⟩⟩
  -- the two Gaussian processes indexed by the net
  set a : I → Fin N → Fin n → ℝ := fun t i j => t.1.2 i * t.1.1 j with ha
  set b : I → Fin 1 → Fin (n + N) → ℝ :=
    fun t _ k => Fin.append (fun j => t.1.1 j) (fun i => t.1.2 i) k with hb
  have hinc : ∀ s t : I,
      ∫ G, (linForm (a s) G - linForm (a t) G) ^ 2 ∂(gaussianMatrix N n)
        ≤ ∫ H, (linForm (b s) H - linForm (b t) H) ^ 2 ∂(gaussianMatrix 1 (n + N)) := by
    intro s t
    simp_rw [linForm_sub_linForm]
    rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
    simp only [ha, hb, Pi.sub_apply]
    rw [gu_coeffY_sq]
    exact gu_coeff_ineq _ _ _ _ (hI1 _ s.2) (hI1 _ t.2) (hI2 _ s.2) (hI2 _ t.2)
  have hSF := sudakov_fernique_inequality (fun t G => linForm (a t) G) (fun t H => linForm (b t) H)
    (hasGaussianLaw_linForm_gaussianMatrix a) (hasGaussianLaw_linForm_gaussianMatrix b) (fun t => integral_linForm_gaussianMatrix _)
    (fun t => integral_linForm_gaussianMatrix _) hinc
  -- integrability
  have hspec : Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A))
      (gaussianMatrix N n) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm (Matrix.of X) (Matrix.of Y)).1
  have hXsup := integrable_iSup_of_fintype (μ := gaussianMatrix N n) (fun t G => linForm (a t) G)
    (fun t => integrable_linForm_gaussianMatrix _) (fun t => (continuous_linForm _).measurable)
  have hYsup := integrable_iSup_of_fintype (μ := gaussianMatrix 1 (n + N)) (fun t H => linForm (b t) H)
    (fun t => integrable_linForm_gaussianMatrix _) (fun t => (continuous_linForm _).measurable)
  have hsq : ∀ {k : ℕ} (σ : Fin k → Fin (n + N)), Integrable
      (fun H : Fin 1 → Fin (n + N) → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 (n + N)) := by
    intro k σ
    have hQ : Integrable (fun H : Fin 1 → Fin (n + N) → ℝ => ∑ j, H 0 (σ j) ^ 2)
        (gaussianMatrix 1 (n + N)) :=
      integrable_finsetSum _ fun j _ => (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq
    refine Integrable.mono' ((integrable_const 1).add hQ) (by fun_prop : Continuous
      (fun H : Fin 1 → Fin (n + N) → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun H => ?_)
    have hQ0 : 0 ≤ ∑ j, H 0 (σ j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt hQ0
    have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]
  -- chain of inequalities
  calc (1 - 2 * ε) * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n)
      = ∫ A, (1 - 2 * ε) * specNorm (Matrix.of A) ∂(gaussianMatrix N n) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ G, (⨆ t, linForm (a t) G) ∂(gaussianMatrix N n) := by
        refine integral_mono (hspec.const_mul _) hXsup fun G => ?_
        refine (one_sub_two_mul_mul_specNorm_le_iSup (Matrix.of G) ε hε.le I hI2 hcov).trans (le_of_eq ?_)
        congr 1
        funext t
        simp only [linForm, ha, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∫ H, (⨆ t, linForm (b t) H) ∂(gaussianMatrix 1 (n + N)) := hSF
    _ ≤ ∫ H, (Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)
          + Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)) ∂(gaussianMatrix 1 (n + N)) := by
        refine integral_mono hYsup ((hsq _).add (hsq _)) fun H => ?_
        exact ciSup_le fun t => gu_Y_le t.1.1 t.1.2 (hI1 _ t.2) (hI2 _ t.2) H
    _ = ∫ H, Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2) ∂(gaussianMatrix 1 (n + N))
          + ∫ H, Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) ∂(gaussianMatrix 1 (n + N)) :=
        integral_add (hsq _) (hsq _)
    _ ≤ Real.sqrt n + Real.sqrt N :=
        add_le_add (integral_sqrt_sum_sq_gaussianMatrix_entry_le _) (integral_sqrt_sum_sq_gaussianMatrix_entry_le _)
    _ = Real.sqrt N + Real.sqrt n := add_comm _ _

/-- **Gordon's upper bound.** For an `N × n` standard Gaussian matrix,
`𝔼 ‖G‖₂ ≤ √N + √n`. Source: Vershynin 2012, Thm 5.32 (upper half); Gordon 1985;
Davidson–Szarek 2001, Thm II.13. Atlas: `gordon`. Ported from Prove2me solution
`GaussianMatrix.gordon_upper`. -/
theorem integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt {N n : ℕ} :
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by
  have hs : 0 ≤ Real.sqrt N + Real.sqrt n := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∀ A : Fin 0 → Fin n → ℝ, specNorm (Matrix.of A) = 0 := fun A => by
      rw [Subsingleton.elim (Matrix.of A) 0, specNorm_zero]
    simp only [h0, integral_zero]
    exact hs
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ A : Fin N → Fin 0 → ℝ, specNorm (Matrix.of A) = 0 := fun A => by
      rw [Subsingleton.elim (Matrix.of A) 0, specNorm_zero]
    simp only [h0, integral_zero]
    exact hs
  set E := ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) with hE
  set s := Real.sqrt N + Real.sqrt n
  by_contra hcon
  push Not at hcon
  have hEpos : 0 < E := lt_of_le_of_lt hs hcon
  have h := gu_scaled_bound hN hn ((E - s) / (4 * E)) (div_pos (by linarith) (by linarith))
  rw [← hE] at h
  have : (1 - 2 * ((E - s) / (4 * E))) * E = (E + s) / 2 := by
    field_simp; ring
  rw [this] at h
  linarith

/-! ### Lower bound -/

private theorem gl_mp_split (n N : ℕ) :
    MeasurePreserving
      (fun x : Fin (n + N) → ℝ => ((fun j : Fin n => x (Fin.castAdd N j)),
        (fun i : Fin N => x (Fin.natAdd n i))))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : Fin (n + N) => ℝ)
    (fun _ : Fin (n + N) => gaussianReal 0 1) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin N => ℝ)
    (fun _ => gaussianReal 0 1)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply]

private theorem gl_mp_row (n N : ℕ) :
    MeasurePreserving (fun H : Fin 1 → Fin (n + N) → ℝ => H 0) (gaussianMatrix 1 (n + N))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1) 0

private theorem gl_integral_castAdd (n N : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun j => H 0 (Fin.castAdd N j)) ∂(gaussianMatrix 1 (n + N))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp ((gl_mp_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

private theorem gl_integral_natAdd (n N : ℕ) (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun i => H 0 (Fin.natAdd n i)) ∂(gaussianMatrix 1 (n + N))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have h := (measurePreserving_snd (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp ((gl_mp_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl


/-! ### New for the lower bound -/

private theorem gl_norm_toLp {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ κ)‖ = Real.sqrt (∑ i, x i ^ 2) := by
  rw [norm_eq_sqrt_sum_sq]

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net bound for the matrix process: `min_{u ∈ U} max_{v ∈ T} ⟨A u, v⟩ ≤ σ_min(A) + ε ‖A‖`
whenever `U` is an `ε`-net of the unit sphere of `ℝⁿ` and `T` consists of unit vectors. -/
private theorem gl_matrix_side {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (ε : ℝ)
    (U : Finset (EuclideanSpace ℝ (Fin n))) (T : Finset (EuclideanSpace ℝ (Fin N)))
    (hT : ∀ v ∈ T, ‖v‖ = 1)
    (hcov : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → ∃ u ∈ U, ‖x - u‖ ≤ ε)
    (hn : Nonempty {x : Fin n → ℝ // x ⬝ᵥ x = 1}) :
    ⨅ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j ≤ sigmaMin A + ε * specNorm A := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  have key : ∀ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j ≤ ‖Φ u.1‖ := by
    intro u
    refine Real.iSup_le (fun v => ?_) (norm_nonneg _)
    rw [← inner_toEuclideanLin_eq_sum]
    refine (real_inner_le_norm _ _).trans ?_
    rw [hT _ v.2, one_mul]
  set L := ⨅ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j with hL
  have hx : ∀ x : {x : Fin n → ℝ // x ⬝ᵥ x = 1},
      L - ε * specNorm A ≤ Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) := by
    intro x
    set xe : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x.1 with hxe
    have hxe1 : ‖xe‖ = 1 := by
      rw [hxe, gl_norm_toLp]
      have : ∑ i, x.1 i ^ 2 = 1 := by
        have h2 := x.2
        simp only [dotProduct] at h2
        simpa [sq] using h2
      rw [this, Real.sqrt_one]
    obtain ⟨u, hu, hxu⟩ := hcov xe hxe1
    have hb : BddBelow (Set.range fun u : U => ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j) :=
      (Set.finite_range _).bddBelow
    have h1 : L ≤ ‖Φ u‖ := (ciInf_le hb ⟨u, hu⟩).trans (key ⟨u, hu⟩)
    have h2 : ‖Φ u‖ ≤ ‖Φ xe‖ + ‖Φ‖ * ε := by
      have hd : Φ u = Φ xe - Φ (xe - u) := by rw [map_sub]; abel
      rw [hd]
      refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
      exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxu (norm_nonneg _))
    have h3 : ‖Φ xe‖ = Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) := by
      have : Φ xe = WithLp.toLp 2 (A *ᵥ x.1) := rfl
      rw [this, gl_norm_toLp]
      simp [dotProduct, sq]
    rw [hM]
    linarith
  have := le_ciInf hx
  unfold sigmaMin
  linarith

/-- The comparison process `⟨g, u⟩ + ⟨h, v⟩` written with one Gaussian row. -/
private theorem gl_lin_append {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N))
    (H : Fin 1 → Fin (n + N) → ℝ) :
    linForm (fun _ k => Fin.append (fun j => u j) (fun i => v i) k) H
      = ∑ j, u j * H 0 (Fin.castAdd N j) + ∑ i, v i * H 0 (Fin.natAdd n i) := by
  unfold linForm
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

open scoped RealInnerProductSpace in
/-- Net bound for the comparison process:
`min_{u ∈ U} max_{v ∈ T} (⟨g,u⟩ + ⟨h,v⟩) ≥ (1 - ε)‖h‖ - ‖g‖`. -/
private theorem gl_gauss_side {N n : ℕ} (hN : 0 < N) (ε : ℝ)
    (U : Finset (EuclideanSpace ℝ (Fin n))) (T : Finset (EuclideanSpace ℝ (Fin N)))
    (hU : ∀ u ∈ U, ‖u‖ = 1) (hUne : Nonempty U)
    (hcov : ∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ = 1 → ∃ v ∈ T, ‖y - v‖ ≤ ε)
    (H : Fin 1 → Fin (n + N) → ℝ) :
    (1 - ε) * Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)
        - Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)
      ≤ ⨅ u : U, ⨆ v : T, linForm (fun _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k) H := by
  set h : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => H 0 (Fin.natAdd n i)) with hh
  have hhn : ‖h‖ = Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) := gl_norm_toLp _
  -- a unit vector aligned with `h`
  obtain ⟨y, hy1, hyh⟩ : ∃ y : EuclideanSpace ℝ (Fin N), ‖y‖ = 1 ∧ ⟪y, h⟫ = ‖h‖ := by
    by_cases h0 : h = 0
    · refine ⟨EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1, by simp, ?_⟩
      rw [h0]; simp
    · refine ⟨(‖h‖⁻¹ : ℝ) • h, norm_smul_inv_norm h0, ?_⟩
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      have : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 h0
      field_simp
  obtain ⟨v, hv, hyv⟩ := hcov y hy1
  have hvh : (1 - ε) * ‖h‖ ≤ ∑ i, v i * H 0 (Fin.natAdd n i) := by
    have e1 : ⟪v, h⟫ = ∑ i, v i * H 0 (Fin.natAdd n i) := by
      simp [hh, PiLp.inner_apply, mul_comm]
    have e2 : ⟪v, h⟫ = ⟪y, h⟫ - ⟪y - v, h⟫ := by rw [inner_sub_left]; ring
    have e3 : ⟪y - v, h⟫ ≤ ε * ‖h‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hyv (norm_nonneg _))
    rw [← e1, e2, hyh]
    linarith
  refine le_ciInf fun u => ?_
  have hb : BddAbove (Set.range fun v : T =>
      linForm (fun _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k) H) :=
    (Set.finite_range _).bddAbove
  refine le_trans ?_ (le_ciSup hb ⟨v, hv⟩)
  rw [gl_lin_append]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => u.1 j)
    (fun j => -H 0 (Fin.castAdd N j))
  rw [← norm_eq_sqrt_sum_sq, hU _ u.2, one_mul] at hcs
  simp only [neg_sq, mul_neg, Finset.sum_neg_distrib] at hcs
  rw [← hhn]
  linarith

private theorem gl_integrable_sqrt_sumsq {k m : ℕ} (σ : Fin k → Fin m) :
    Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 m) := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2)
      (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq
  refine Integrable.mono' ((integrable_const 1).add hQ) (by fun_prop : Continuous
    (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun H => ?_)
  have hQ0 : 0 ≤ ∑ j, H 0 (σ j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := Real.sq_sqrt hQ0
  have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]

/-- Same-`u` increments of the matrix process: `‖u vᵀ - u v'ᵀ‖_F² = ‖v - v'‖²` for a unit `u`. -/
private theorem gl_coeff_same {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u j) ^ 2 = ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ j, (v i * u j - v' i * u j) ^ 2 = (v i - v' i) ^ 2 * u j ^ 2 := fun j => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, su, mul_one]

/-- The comparison bound at a fixed net scale `ε`:
`(1 - ε) 𝔼‖h_N‖ - 𝔼‖g_n‖ ≤ 𝔼 σ_min(G) + ε 𝔼‖G‖`. -/
private theorem gl_scaled_bound {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    (1 - ε) * ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n)
        + ε * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).totallyBounded ε hε
  set U := hFufin.toFinset with hUdef
  set T := hFvfin.toFinset with hTdef
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hUdef, Set.Finite.mem_toFinset] at hu
    simpa using hFuS hu
  have hT1 : ∀ v ∈ T, ‖v‖ = 1 := by
    intro v hv
    rw [hTdef, Set.Finite.mem_toFinset] at hv
    simpa using hFvS hv
  have hcovU : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → ∃ u ∈ U, ‖x - u‖ ≤ ε := by
    intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.1 (hFucov hx')
    refine ⟨y, by rw [hUdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx.le
  have hcovT : ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖ = 1 → ∃ v ∈ T, ‖x - v‖ ≤ ε := by
    intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.1 (hFvcov hx')
    refine ⟨y, by rw [hTdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx.le
  have hUne : Nonempty U := by
    obtain ⟨u, hu, -⟩ := hcovU (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1) (by simp)
    exact ⟨⟨u, hu⟩⟩
  have hTne : Nonempty T := by
    obtain ⟨v, hv, -⟩ := hcovT (EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1) (by simp)
    exact ⟨⟨v, hv⟩⟩
  have hsub : Nonempty {x : Fin n → ℝ // x ⬝ᵥ x = 1} :=
    ⟨⟨Pi.single (⟨0, hn⟩ : Fin n) 1, by simp [dotProduct, Pi.single_apply]⟩⟩
  -- the two Gaussian processes indexed by the nets
  set b : U → T → Fin 1 → Fin (n + N) → ℝ :=
    fun u v _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k with hb
  set a : U → T → Fin N → Fin n → ℝ := fun u v i j => v.1 i * u.1 j with ha
  have hsame : ∀ (u : U) (t s : T),
      ∫ H, (linForm (b u t) H - linForm (b u s) H) ^ 2 ∂(gaussianMatrix 1 (n + N))
        ≤ ∫ G, (linForm (a u t) G - linForm (a u s) G) ^ 2 ∂(gaussianMatrix N n) := by
    intro u t s
    simp_rw [linForm_sub_linForm]
    rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
    simp only [ha, hb, Pi.sub_apply]
    rw [gu_coeffY_sq, gl_coeff_same _ _ _ (hU1 _ u.2)]
    simp
  have hdiff : ∀ (u v : U) (t s : T), u ≠ v →
      ∫ G, (linForm (a u t) G - linForm (a v s) G) ^ 2 ∂(gaussianMatrix N n)
        ≤ ∫ H, (linForm (b u t) H - linForm (b v s) H) ^ 2 ∂(gaussianMatrix 1 (n + N)) := by
    intro u v t s _
    simp_rw [linForm_sub_linForm]
    rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
    simp only [ha, hb, Pi.sub_apply]
    rw [gu_coeffY_sq]
    exact gu_coeff_ineq _ _ _ _ (hU1 _ u.2) (hU1 _ v.2) (hT1 _ t.2) (hT1 _ s.2)
  have hGM := gordon_minimax_inequality (fun u t H => linForm (b u t) H) (fun u t G => linForm (a u t) G)
    (hasGaussianLaw_linForm_gaussianMatrix (fun p : U × T => b p.1 p.2))
    (hasGaussianLaw_linForm_gaussianMatrix (fun p : U × T => a p.1 p.2))
    (fun u t => integral_linForm_gaussianMatrix _) (fun u t => integral_linForm_gaussianMatrix _) hsame hdiff
  -- integrability
  have hsMin : Integrable (fun A : Fin N → Fin n → ℝ => sigmaMin (Matrix.of A))
      (gaussianMatrix N n) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun A : Fin N → Fin n → ℝ => sigmaMin (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact abs_sigmaMin_sub_sigmaMin_le_frobNorm (Matrix.of X) (Matrix.of Y)).1
  have hspec : Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A))
      (gaussianMatrix N n) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm (Matrix.of X) (Matrix.of Y)).1
  have hXmm : Integrable (fun H => ⨅ u : U, ⨆ t : T, linForm (b u t) H)
      (gaussianMatrix 1 (n + N)) :=
    integrable_iInf_of_fintype (fun u H => ⨆ t : T, linForm (b u t) H)
      (fun u => integrable_iSup_of_fintype (fun t H => linForm (b u t) H) (fun t => integrable_linForm_gaussianMatrix _)
        (fun t => (continuous_linForm _).measurable))
      (fun u => Measurable.iSup fun t => (continuous_linForm _).measurable)
  have hYmm : Integrable (fun G => ⨅ u : U, ⨆ t : T, linForm (a u t) G)
      (gaussianMatrix N n) :=
    integrable_iInf_of_fintype (fun u G => ⨆ t : T, linForm (a u t) G)
      (fun u => integrable_iSup_of_fintype (fun t G => linForm (a u t) G) (fun t => integrable_linForm_gaussianMatrix _)
        (fun t => (continuous_linForm _).measurable))
      (fun u => Measurable.iSup fun t => (continuous_linForm _).measurable)
  have hg := gl_integrable_sqrt_sumsq (m := n + N) (fun j : Fin n => Fin.castAdd N j)
  have hh := gl_integrable_sqrt_sumsq (m := n + N) (fun i : Fin N => Fin.natAdd n i)
  have hEN := gl_integral_natAdd n N (fun x => Real.sqrt (∑ i, x i ^ 2)) (by fun_prop)
  have hEn := gl_integral_castAdd n N (fun x => Real.sqrt (∑ j, x j ^ 2)) (by fun_prop)
  -- chain of inequalities
  calc (1 - ε) * ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = ∫ H, ((1 - ε) * Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)
          - Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)) ∂(gaussianMatrix 1 (n + N)) := by
        rw [integral_sub (hh.const_mul _) hg, integral_const_mul]
        simp only at hEN hEn
        rw [hEN, hEn]
    _ ≤ ∫ H, (⨅ u : U, ⨆ t : T, linForm (b u t) H) ∂(gaussianMatrix 1 (n + N)) := by
        refine integral_mono ((hh.const_mul _).sub hg) hXmm fun H => ?_
        exact gl_gauss_side hN ε U T hU1 hUne hcovT H
    _ ≤ ∫ G, (⨅ u : U, ⨆ t : T, linForm (a u t) G) ∂(gaussianMatrix N n) := hGM
    _ ≤ ∫ A, (sigmaMin (Matrix.of A) + ε * specNorm (Matrix.of A)) ∂(gaussianMatrix N n) := by
        refine integral_mono hYmm (hsMin.add (hspec.const_mul ε)) fun G => ?_
        refine le_trans (le_of_eq ?_) (gl_matrix_side (Matrix.of G) ε U T hT1 hcovU hsub)
        congr 1; funext u; congr 1; funext t
        simp only [linForm, ha, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n)
          + ε * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) := by
        rw [integral_add hsMin (hspec.const_mul ε), integral_const_mul]

/-- **Gordon's lower bound.** For an `N × n` standard Gaussian matrix with `n ≥ 1`,
`√N - √n ≤ 𝔼 σ_min(G)` where `σ_min(G) = inf_{‖x‖₂ = 1} ‖G x‖₂` (`NLAlib.sigmaMin`). For `N ≤ n`
the left side is `≤ 0` and the bound is trivial. Source: Vershynin 2012, Thm 5.32 (lower half);
Gordon 1985; Davidson–Szarek 2001, Thm II.13. Atlas: `gordon`. Ported from Prove2me solution
`GaussianMatrix.gordon_lower`. -/
theorem sqrt_sub_sqrt_le_integral_sigmaMin_gaussianMatrix {N n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n) := by
  have hpos : 0 ≤ ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n) :=
    integral_nonneg fun A => Real.iInf_nonneg fun _ => Real.sqrt_nonneg _
  rcases le_or_gt N n with hNn | hNn
  · have : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hNn)
    linarith
  have hN : 0 < N := lt_of_lt_of_le (by omega) hNn
  set EN := ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
    with hENdef
  set En := ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
    with hEndef
  set E := ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n) with hE
  set Sp := ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) with hSp
  have hD : Real.sqrt N - Real.sqrt n ≤ EN - En :=
    sqrt_sub_sqrt_le_integral_sqrt_sum_sq_sub hn hNn.le
  have hEN0 : 0 ≤ EN := integral_nonneg fun _ => Real.sqrt_nonneg _
  have hSp0 : 0 ≤ Sp := integral_nonneg fun A => specNorm_nonneg (Matrix.of A)
  have key : ∀ ε : ℝ, 0 < ε → EN - En - ε * (EN + Sp) ≤ E := by
    intro ε hε
    have := gl_scaled_bound (N := N) (n := n) hN (by omega) ε hε
    linarith
  -- let `ε → 0`
  have hlim : EN - En ≤ E := by
    by_contra hcon
    push Not at hcon
    set δ := EN - En - E with hδ
    have hδ0 : 0 < δ := by linarith
    set C := EN + Sp + 1 with hC
    have hC0 : 0 < C := by linarith
    have h1 := key (δ / (2 * C)) (by positivity)
    have h2 : δ / (2 * C) * (EN + Sp) ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  linarith

/-! ### Gordon's theorem -/

/-- **Gordon's theorem for Gaussian matrices.** For an `N × n` standard Gaussian matrix `G`
with `n ≥ 1`, `σ_min(G)` and `‖G‖₂` are integrable and
`√N - √n ≤ 𝔼 σ_min(G) ≤ 𝔼 ‖G‖₂ ≤ √N + √n`. Source: Vershynin 2012, Thm 5.32; Gordon 1985;
Davidson–Szarek 2001, Thm II.13. Atlas: `gordon`. Ported from Prove2me solution
`GaussianMatrix.gordon`. -/
theorem gordon_extreme_singular_values {N n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun A : Fin N → Fin n → ℝ => sigmaMin (Matrix.of A)) (gaussianMatrix N n) ∧
    Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) (gaussianMatrix N n) ∧
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, sigmaMin (Matrix.of A) ∂(gaussianMatrix N n)
      ≤ ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by
  have hI1 := (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun A : Fin N → Fin n → ℝ => sigmaMin (Matrix.of A)) 1
    zero_le_one fun X Y => by
      rw [one_mul]; exact abs_sigmaMin_sub_sigmaMin_le_frobNorm (Matrix.of X) (Matrix.of Y)).1
  have hI2 := (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1
    zero_le_one fun X Y => by
      rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm (Matrix.of X) (Matrix.of Y)).1
  refine ⟨hI1, hI2, sqrt_sub_sqrt_le_integral_sigmaMin_gaussianMatrix hn, ?_, integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt⟩
  exact integral_mono hI1 hI2 fun A => by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact sigmaMin_le_specNorm (Matrix.of A)


end NLAlib
