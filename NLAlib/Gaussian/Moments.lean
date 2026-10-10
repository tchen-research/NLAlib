/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_frobenius_second_moment`, `Sol_GaussianMatrix_full_rank_ae`).
-/
import NLAlib.Gaussian.Basic
import NLAlib.Matrix.Norms
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Moments and almost-sure rank of the standard Gaussian matrix

* `NLAlib.integral_frobSq_mul_gaussianMatrix_mul`: `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`
  (HMT 2011 Prop 10.1, first identity; atlas `gaussian-frob-second-moment`).
* `NLAlib.ae_ne_zero_mvPolynomial`, `NLAlib.gaussianMatrix_ae_eval_ne_zero`: a nonzero polynomial
  in i.i.d. atomless coordinates (in particular in the entries of a Gaussian matrix) is a.s.
  nonzero.
* `NLAlib.gaussianMatrix_ae_rank_eq`: a standard Gaussian matrix has full rank almost surely,
  with the corollaries `gaussianMatrix_ae_isUnit_mul_transpose` (wide case, `G Gᵀ` invertible)
  and `gaussianMatrix_ae_isUnit_transpose_mul` (tall case) (HMT 2011 Prop A.5 / §10.2; atlas
  `gaussian-full-rank-ae`).

The entry-level facts (`integral_gaussianMatrix_entry_mul`, `gaussianMatrix_map_uncurry`) are in
`NLAlib.Gaussian.Basic`. Proof source: Prove2me workspace, Gaussian Random Matrices series
(Frobenius second moment, full rank a.s.).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### The sandwiched second moment -/

private lemma frobSq_expand {ι κ : Type*} [Fintype ι] [Fintype κ] {p m : ℕ}
    (S : Matrix ι (Fin p) ℝ) (T : Matrix (Fin m) κ ℝ) (G : Fin p → Fin m → ℝ) :
    frobSq (S * Matrix.of G * T) = ∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d,
      (S i k * T b j * S i c * T d j) * (G k b * G c d) := by
  rw [frobSq_eq_sum_sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : (S * Matrix.of G * T) i j = ∑ k, ∑ b, S i k * G k b * T b j := by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  ring

private lemma integral_quadratic {ι κ : Type*} [Fintype ι] [Fintype κ] {p m : ℕ}
    (w : ι → κ → Fin p → Fin p → Fin m → Fin m → ℝ) :
    ∫ G, (∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d, w i j k c b d * (G k b * G c d))
        ∂(gaussianMatrix p m)
      = ∑ i, ∑ j, ∑ k, ∑ b, w i j k k b b := by
  have hI : ∀ (k c : Fin p) (b : Fin m) (f : Fin m → ℝ),
      Integrable (fun G : Fin p → Fin m → ℝ => ∑ d, f d * (G k b * G c d))
        (gaussianMatrix p m) :=
    fun k c b f => integrable_finsetSum _ fun d _ =>
      integrable_const_mul_gaussianMatrix_entry_mul k c b d _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI k c b _]
  rw [Finset.sum_eq_single k]
  · rw [integral_finsetSum _ fun b _ => hI k k b _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_const_mul_gaussianMatrix_entry_mul k k b d _]
    simp [integral_const_mul, integral_gaussianMatrix_entry_mul]
  · intro c _ hck
    rw [integral_finsetSum _ fun b _ => hI k c b _]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_const_mul_gaussianMatrix_entry_mul k c b d _]
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [integral_const_mul, integral_gaussianMatrix_entry_mul, Ne.symm hck]
  · simp

/-- **Second Frobenius moment of a sandwiched Gaussian matrix.** For fixed `S` and `T` and a
`p × m` standard Gaussian matrix `G`, `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`.

HMT 2011 (Halko–Martinsson–Tropp), Prop 10.1, first identity (`E‖SGT‖_F² = ‖S‖_F² ‖T‖_F²`).
Atlas: `gaussian-frob-second-moment`. The outer dimensions are arbitrary finite index types
(the source and the Prove2me statement use `Fin a`, `Fin n`). Ported from the Prove2me
workspace, Gaussian Random Matrices series.
atlas: gaussian-frob-second-moment -/
theorem integral_frobSq_mul_gaussianMatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p m : ℕ} (S : Matrix ι (Fin p) ℝ) (T : Matrix (Fin m) κ ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ∂(gaussianMatrix p m) = frobSq S * frobSq T := by
  simp_rw [frobSq_expand]
  rw [integral_quadratic (fun i j k c b d => S i k * T b j * S i c * T d j)]
  rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Zero sets of polynomials and full rank -/

private theorem ae_ne_zero_mvPolynomial_fin (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f ≠ 0 →
      ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), MvPolynomial.eval x f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x hx => hf ?_
    apply MvPolynomial.funext
    intro y
    have : y = x := Subsingleton.elim _ _
    subst this
    simpa using hx
  | succ n ih =>
    intro f hf
    set g := MvPolynomial.finSuccEquiv ℝ n f with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hf
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by rw [← hg, h, map_zero])
    have hc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hih := ih g.leadingCoeff hc
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    let T : Set (ℝ × (Fin n → ℝ)) :=
      {q | MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → ℝ) f = 0}
    have hT : MeasurableSet T := by
      have hcont : Continuous fun q : ℝ × (Fin n → ℝ) =>
          MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → ℝ) f := by
        apply (MvPolynomial.continuous_eval f).comp
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
      exact hcont.measurable (measurableSet_singleton 0)
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 ⁻¹' T =
        {x | MvPolynomial.eval x f = 0} := by
      ext x
      have hx : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).1
          (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).2 : Fin (n+1) → ℝ) = x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [MeasurableEquiv.piFinSuccAbove_apply]
        · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      simp only [Set.mem_preimage, T, Set.mem_ofPred_eq]
      rw [hx]
    rw [← hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hih] with s hs
    have hpoly : Polynomial.map (MvPolynomial.eval s) g ≠ 0 := by
      intro h0
      apply hs
      have := congrArg (fun q => Polynomial.coeff q g.natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact this
    have hfin : ((fun y => (y, s)) ⁻¹' T).Finite := by
      refine (Polynomial.roots
        (Polynomial.map (MvPolynomial.eval s) g)).toFinset.finite_toSet.subset ?_
      intro y hy
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, T, MvPolynomial.eval_eq_eval_mv_eval']
        at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpoly,
        Polynomial.IsRoot.def]
      exact hy
    simpa using hfin.measure_zero μ

/-- **Zero sets of polynomials are null.** The zero set of a nonzero real polynomial in
finitely many variables is null for a product of copies of an atomless probability measure on
`ℝ`.

Helper for HMT 2011 Prop A.5; atlas `gaussian-full-rank-ae`. -/
theorem ae_ne_zero_mvPolynomial {ι : Type*} [Fintype ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (f : MvPolynomial ι ℝ) (hf : f ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => μ), MvPolynomial.eval x f ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hg : MvPolynomial.rename e f ≠ 0 := by
    intro h; apply hf
    exact MvPolynomial.rename_injective e e.injective (by rw [h, map_zero])
  have h := ae_ne_zero_mvPolynomial_fin μ _ _ hg
  let T : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y i => y (e i)
  have hT : Measurable T := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hmap : Measure.map T (Measure.pi fun _ => μ) = Measure.pi fun _ : ι => μ := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
    have hpre : T ⁻¹' Set.univ.pi s = Set.univ.pi fun k => s (e.symm k) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ_pi, T]
      constructor
      · intro hy k; simpa using hy (e.symm k)
      · intro hy i; simpa using hy (e i)
    rw [hpre, Measure.pi_pi]
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hmeas : MeasurableSet {x : ι → ℝ | MvPolynomial.eval x f ≠ 0} :=
    ((MvPolynomial.continuous_eval f).measurable (measurableSet_singleton 0)).compl
  rw [← hmap, ae_map_iff hT.aemeasurable hmeas]
  filter_upwards [h] with y hy
  rw [MvPolynomial.eval_rename] at hy
  exact hy

/-- A nonzero polynomial in the entries of a standard Gaussian matrix is almost surely nonzero.

Helper for HMT 2011 Prop A.5; atlas `gaussian-full-rank-ae`. -/
theorem gaussianMatrix_ae_eval_ne_zero (p m : ℕ) (f : MvPolynomial (Fin p × Fin m) ℝ)
    (hf : f ≠ 0) :
    ∀ᵐ G ∂(gaussianMatrix p m), MvPolynomial.eval (fun ab => G ab.1 ab.2) f ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h := ae_ne_zero_mvPolynomial (gaussianReal 0 1) f hf
  rw [← gaussianMatrix_map_uncurry] at h
  exact ae_of_ae_map (measurable_pi_lambda _ fun ab =>
    (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)).aemeasurable h

private theorem eval_det_gram (p m : ℕ) (G : Fin p → Fin m → ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ * (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ).det
      = (Matrix.of G * (Matrix.of G)ᵀ).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = Matrix.of G := by
    ext i j; simp
  rw [hX]

private theorem eval_det_gram_transpose (p m : ℕ) (G : Fin p → Fin m → ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      ((Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ * Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).det
      = ((Matrix.of G)ᵀ * Matrix.of G).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = Matrix.of G := by
    ext i j; simp
  rw [hX]

/-- **A wide Gaussian matrix has full row rank a.s.** If `k ≤ t` and `G` is a `k × t`
standard Gaussian matrix, then `G Gᵀ` is invertible almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 / §10.2 (`Ω₁` has full row rank with probability
one). Atlas: `gaussian-full-rank-ae`. Ported from the Prove2me workspace, Gaussian Random
Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_isUnit_mul_transpose {k t : ℕ} (h : k ≤ t) :
    ∀ᵐ G ∂(gaussianMatrix k t), IsUnit (Matrix.of G * (Matrix.of G)ᵀ) := by
  have hP : (Matrix.mvPolynomialX (Fin k) (Fin t) ℝ *
      (Matrix.mvPolynomialX (Fin k) (Fin t) ℝ)ᵀ).det ≠ 0 := by
    intro h0
    let G0 : Fin k → Fin t → ℝ := fun i j => if j = Fin.castLE h i then 1 else 0
    have hE : Matrix.of G0 * (Matrix.of G0)ᵀ = 1 := by
      ext i l
      simp [G0, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj, eq_comm]
    have := eval_det_gram k t G0
    rw [h0, map_zero, hE, Matrix.det_one] at this
    exact zero_ne_one this
  filter_upwards [gaussianMatrix_ae_eval_ne_zero k t _ hP] with G hG
  rw [eval_det_gram] at hG
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)

/-- **A tall Gaussian matrix has full column rank a.s.** If `t ≤ k` and `G` is a `k × t`
standard Gaussian matrix, then `Gᵀ G` is invertible almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 (transposed form). Atlas: `gaussian-full-rank-ae`.
Ported from the Prove2me workspace, Gaussian Random Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_isUnit_transpose_mul {k t : ℕ} (h : t ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix k t), IsUnit ((Matrix.of G)ᵀ * Matrix.of G) := by
  have hP : ((Matrix.mvPolynomialX (Fin k) (Fin t) ℝ)ᵀ *
      Matrix.mvPolynomialX (Fin k) (Fin t) ℝ).det ≠ 0 := by
    intro h0
    let G0 : Fin k → Fin t → ℝ := fun i j => if i = Fin.castLE h j then 1 else 0
    have hE : (Matrix.of G0)ᵀ * Matrix.of G0 = 1 := by
      ext i l
      simp [G0, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj, eq_comm]
    have := eval_det_gram_transpose k t G0
    rw [h0, map_zero, hE, Matrix.det_one] at this
    exact zero_ne_one this
  filter_upwards [gaussianMatrix_ae_eval_ne_zero k t _ hP] with G hG
  rw [eval_det_gram_transpose] at hG
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)

/-- **A Gaussian matrix has full rank a.s.** A `p × m` standard Gaussian matrix has rank
`min p m` almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 / §10.2. Atlas: `gaussian-full-rank-ae`. Ported
from the Prove2me workspace, Gaussian Random Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_rank_eq (p m : ℕ) :
    ∀ᵐ G ∂(gaussianMatrix p m), (Matrix.of G).rank = min p m := by
  rcases le_total p m with h | h
  · filter_upwards [gaussianMatrix_ae_isUnit_mul_transpose h] with G hu
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_left (Matrix.of G) (Matrix.of G)ᵀ
    have h3 := Matrix.rank_le_height (Matrix.of G)
    rw [Fintype.card_fin] at h1
    rw [min_eq_left h]; omega
  · filter_upwards [gaussianMatrix_ae_isUnit_transpose_mul h] with G hu
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Matrix.of G)ᵀ (Matrix.of G)
    have h3 := Matrix.rank_le_width (Matrix.of G)
    rw [Fintype.card_fin] at h1
    rw [min_eq_right h]; omega

end NLAlib
