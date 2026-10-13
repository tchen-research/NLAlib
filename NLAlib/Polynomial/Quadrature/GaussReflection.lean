import NLAlib.Polynomial.Quadrature.GeneralMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Reflection of the actual Lebesgue Gauss rule

Monic orthogonal-polynomial uniqueness proves reflection of the supplied Gauss
nodes. Interpolation uniqueness then proves reflection of their integrated weights.
-/
noncomputable section
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- A Lebesgue-orthogonal monic nodal polynomial has its degree's reflection parity.
Source: Trefethen, ATAP, Theorem 19.4; monic orthogonal-polynomial uniqueness. -/
theorem nodal_eq_neg_one_pow_mul_comp_neg_X_of_orthogonal
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (hv : InjOn v s)
    (hvI : ∀ i ∈ s, v i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ p : ℝ[X], p.degree < s.card →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal s v).eval x * p.eval x = 0) :
    Lagrange.nodal s v = C ((-1 : ℝ) ^ s.card) * (Lagrange.nodal s v).comp (-X) := by
  let q := Lagrange.nodal s v
  let r := C ((-1 : ℝ) ^ s.card) * q.comp (-X)
  have hq : q.Monic := Lagrange.nodal_monic
  have hr : r.Monic := by
    have h := hq.neg_one_pow_natDegree_mul_comp_neg_X
    simpa only [r, q, Lagrange.natDegree_nodal, C_pow, C_neg, C_1] using h
  have hdeg : r.degree = q.degree := by
    dsimp [r]
    rw [degree_C_mul (by positivity), degree_comp_neg_X]
  have hd : (q - r).degree < s.card := by
    have h := degree_sub_lt_left hdeg.symm hq.ne_zero (hq.trans hr.symm)
    simpa only [q, Lagrange.degree_nodal] using h
  have hrorth (p : ℝ[X]) (hp : p.degree < s.card) :
      ∫ x in (-1 : ℝ)..1, r.eval x * p.eval x = 0 := by
    have hP := horth (p.comp (-X)) (by simpa only [degree_comp_neg_X] using hp)
    have href := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
      (fun x => q.eval x * p.eval (-x))
    simp only [neg_neg, q] at href
    have hneg : (∫ x in (-1 : ℝ)..1, q.eval (-x) * p.eval x) = 0 := by
      rw [href]
      simpa only [eval_comp, eval_neg, eval_X] using hP
    dsimp [r]
    simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_X, mul_assoc]
    rw [intervalIntegral.integral_const_mul, hneg, mul_zero]
  have hz : (∫ x in (-1 : ℝ)..1, ((q - r).eval x) ^ 2) = 0 := by
    have h1 := horth (q - r) hd
    have h2 := hrorth (q - r) hd
    have heq : (fun x => ((q - r).eval x) ^ 2) =
        fun x => q.eval x * (q - r).eval x - r.eval x * (q - r).eval x := by
      funext x
      simp only [eval_sub]
      ring
    rw [heq, intervalIntegral.integral_sub
      (f := fun x => q.eval x * (q - r).eval x)
      (g := fun x => r.eval x * (q - r).eval x)
      ((q.continuous.mul (q - r).continuous).intervalIntegrable _ _)
      ((r.continuous.mul (q - r).continuous).intervalIntegrable _ _), h1, h2, sub_self]
  have heq : q - r = 0 := by
    by_contra hd0
    let μ := volume.restrict (Ioc (-1 : ℝ) 1)
    have hμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
      exact Ioc_subset_Icc_self hx
    have hsupp : ∀ i ∈ s, v i ∈ μ.support := by
      intro i hi
      apply Measure.interior_inter_support
      exact ⟨by rw [interior_Ioc]; exact hvI i hi, by rw [Measure.support_eq_univ]; trivial⟩
    have hpos := integral_sq_eval_pos_of_degree_lt hμ s hv hsupp hd hd0
    have hInt : (∫ x, ((q - r).eval x) ^ 2 ∂μ) =
        ∫ x in (-1 : ℝ)..1, ((q - r).eval x) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [hInt, hz] at hpos
    exact (lt_irrefl 0) hpos
  exact sub_eq_zero.mp heq

/-- Reflection permutes the actual Lebesgue Gauss nodes and preserves their
integrated cardinal weights. Source: Trefethen, ATAP, Theorem 19.4. -/
theorem exists_reflection_equiv_of_orthogonal_nodal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (hv : Function.Injective v)
    (hvI : ∀ i, v i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ p : ℝ[X], p.degree < Fintype.card ι →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ v).eval x * p.eval x = 0) :
    ∃ σ : ι ≃ ι, (∀ i, v (σ i) = -v i) ∧
      ∀ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v (σ i)).eval x) =
        ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x := by
  classical
  have hvS : InjOn v (univ : Finset ι) := fun i hi j hj h => hv h
  have hq := nodal_eq_neg_one_pow_mul_comp_neg_X_of_orthogonal univ v hvS
    (fun i hi => hvI i) (by simpa only [card_univ] using horth)
  have hroot (i : ι) : ∃ j, v j = -v i := by
    have h := congrArg (fun p : ℝ[X] => p.eval (-v i)) hq
    simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_neg,
      Lagrange.eval_nodal_at_node (mem_univ i), mul_zero] at h
    rw [Lagrange.eval_nodal, prod_eq_zero_iff] at h
    obtain ⟨j, hj, hzero⟩ := h
    exact ⟨j, (sub_eq_zero.mp hzero).symm⟩
  let τ : ι → ι := fun i => Classical.choose (hroot i)
  have hτ (i : ι) : v (τ i) = -v i := Classical.choose_spec (hroot i)
  have hτinj : Function.Injective τ := by
    intro i j h
    apply hv
    have he := congrArg v h
    rw [hτ, hτ] at he
    exact neg_injective he
  let σ := Equiv.ofBijective τ hτinj.bijective_of_finite
  have hσ (i : ι) : v (σ i) = -v i := hτ i
  refine ⟨σ, hσ, ?_⟩
  intro i
  have hpol : (Lagrange.basis univ v (σ i)).comp (-X) = Lagrange.basis univ v i := by
    have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    apply eq_of_degrees_lt_of_eval_index_eq univ hvS
    · rw [degree_comp_neg_X, Lagrange.degree_basis hvS (mem_univ _), card_univ]
      exact_mod_cast (show Fintype.card ι - 1 < Fintype.card ι by omega)
    · rw [Lagrange.degree_basis hvS (mem_univ _), card_univ]
      exact_mod_cast (show Fintype.card ι - 1 < Fintype.card ι by omega)
    · intro j hj
      rw [eval_comp, eval_neg, eval_X, ← hσ j]
      by_cases hij : i = j
      · subst j
        rw [Lagrange.eval_basis_self hvS (mem_univ _), Lagrange.eval_basis_self hvS (mem_univ _)]
      · rw [Lagrange.eval_basis_of_ne (fun h => hij (σ.injective h)) (mem_univ _),
          Lagrange.eval_basis_of_ne hij (mem_univ _)]
  have heval := congrArg (fun p : ℝ[X] => p.eval) hpol
  have href := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (Lagrange.basis univ v (σ i)).eval
  simp only [neg_neg] at href
  have hcomp : (fun x => (Lagrange.basis univ v (σ i)).eval (-x)) =
      (Lagrange.basis univ v i).eval := by
    funext x
    simpa only [eval_comp, eval_neg, eval_X] using congrFun heval x
  rw [hcomp] at href
  exact href.symm

end NLAlib
