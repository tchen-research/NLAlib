import NLAlib.Polynomial.Quadrature.GaussLebesgue
import NLAlib.Polynomial.Quadrature.ContinuousConvergence

/-! # Continuous convergence of the actual Lebesgue Gauss rule

Positivity of the integrated cardinal weights and polynomial exactness imply
convergence for every continuous function, with no coefficient assumptions.
-/
noncomputable section
open Set MeasureTheory Polynomial Finset Filter
open scoped Topology
namespace NLAlib

/-- Actual integrated Lebesgue Gauss cardinal rules converge on every continuous
function on `[-1,1]`. Each rule is supplied by distinct interior nodes whose nodal
polynomial is orthogonal to lower degrees; its weights are the actual cardinal
integrals. Source: Stieltjes' theorem, Trefethen, ATAP, Chapter 19.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem tendsto_gauss_lebesgue_of_continuousOn
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (hcard : ∀ n, Fintype.card (ι n) = n + 1)
    (v : ∀ n, ι n → ℝ) (hv : ∀ n, Function.Injective (v n))
    (hvI : ∀ n i, v n i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ n (p : ℝ[X]), p.degree < Fintype.card (ι n) →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ (v n)).eval x * p.eval x = 0)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun n => ∑ i, (∫ x in (-1 : ℝ)..1,
      (Lagrange.basis univ (v n) i).eval x) * f (v n i)) atTop
        (𝓝 (∫ x in (-1 : ℝ)..1, f x)) := by
  classical
  let w := fun n i => ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ (v n) i).eval x
  have hprops (n : ℕ) := gauss_lebesgue_quadrature_of_orthogonal_nodal
    (hcard n) (v n) (hv n) (hvI n) (horth n)
  let vn := fun n i => (⟨v n i, Ioo_subset_Icc_self (hvI n i)⟩ : Icc (-1 : ℝ) 1)
  let Q : ℕ → (C(Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ) := fun n =>
    { toFun := fun g => ∑ i, w n i * g (vn n i)
      map_add' := by
        intro g h
        simp only [ContinuousMap.add_apply, mul_add, sum_add_distrib]
      map_smul' := by
        intro c g
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        apply sum_congr rfl
        intro i hi
        ring }
  have hbound (n : ℕ) (g : C(Icc (-1 : ℝ) 1, ℝ)) : |Q n g| ≤ 2 * ‖g‖ := by
    change |∑ i, w n i * g (vn n i)| ≤ _
    calc
      _ ≤ ∑ i, |w n i * g (vn n i)| := abs_sum_le_sum_abs _ _
      _ = ∑ i, w n i * |g (vn n i)| := by
        apply sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg ((hprops n).1 i).le]
      _ ≤ ∑ i, w n i * ‖g‖ := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ ((hprops n).1 i).le
        simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm (vn n i)
      _ = 2 * ‖g‖ := by rw [← sum_mul, (hprops n).2.1]
  have hexact (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n) :
      Q n (p.toContinuousMapOn (Icc (-1 : ℝ) 1)) = ∫ x in (-1 : ℝ)..1, p.eval x := by
    have hp : p.degree ≤ (2 * n + 1 : ℕ) := p.degree_le_natDegree.trans (by
      exact_mod_cast (hn.trans (show n ≤ 2 * n + 1 by omega)))
    exact ((hprops n).2.2.1 p hp).symm
  let fc : C(Icc (-1 : ℝ) 1, ℝ) := ⟨fun x => f x, hf.domRestrict⟩
  have h := tendsto_quadrature_of_bound_and_polynomial_exact Q 2 (by norm_num) hbound hexact fc
  have hInt : unitIntervalIntegralLinearMap fc = ∫ x in (-1 : ℝ)..1, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    rw [IccExtend_of_mem _ _ hx]
    rfl
  rw [hInt] at h
  exact h

end NLAlib
