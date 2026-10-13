import NLAlib.Polynomial.BestApproximation.InterpolationPeakCharts
import NLAlib.Polynomial.BestApproximation.GapDirections

/-!
# Derivatives of actual interpolation gap peaks

The derivative of the critical point disappears from the peak derivative because
the spatial derivative vanishes there. Differentiated nodal equations then identify
the node-coordinate derivatives by the actual Lagrange cardinals.
-/

noncomputable section
open Polynomial Real Finset Set Filter
open scoped Topology ContDiff
namespace NLAlib

/-- Evaluation at a fixed spatial point is differentiable in the actual ordered
node coordinates.
Source: the rational cardinal formula; focused reroutes, peak Jacobian. -/
theorem differentiableAt_eval_interpolationGapPolynomial {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (x : ℝ) :
    DifferentiableAt ℝ (fun s => (interpolationGapPolynomial n s i).eval x) t := by
  have hinput : ContDiffAt ℝ 1 (fun s : Fin n → ℝ => (s, x)) t :=
    contDiffAt_id.prodMk contDiffAt_const
  exact ((contDiffAt_eval_interpolationGapPolynomial ht i x 1).comp t hinput).differentiableAt_one

/-- The derivative of the actual maximum is the node derivative of its polynomial
with the spatial critical point held fixed.
Source: the nondegenerate implicit chart and the vanishing spatial derivative;
focused reroutes, peak Jacobian. -/
theorem hasFDerivAt_interpolationGapPeak_fixed_criticalPoint {n : ℕ} (hn : 0 < n)
    {t : Fin n → ℝ} (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    HasFDerivAt (fun s => interpolationGapPeak n s i)
      (fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval (interpolationGapCriticalPoint n t i)) t) t := by
  obtain ⟨τ, hτdiff, hτgap, hτcrit, hevent⟩ := exists_contDiffAt_interpolationGapPeak_chart hn ht i
  have hτself : τ t = interpolationGapCriticalPoint n t i :=
    (interpolationGapCriticalPoint_spec hn ht i).2.2.2.2.2 (τ t) hτgap hτcrit
  let H : (Fin n → ℝ) × ℝ → ℝ := fun u => (interpolationGapPolynomial n u.1 i).eval u.2
  let D := fderiv ℝ H (t, τ t)
  have hH : HasFDerivAt H D (t, τ t) :=
    (contDiffAt_eval_interpolationGapPolynomial ht i (τ t) 1).differentiableAt_one.hasFDerivAt
  have hspace := hH.comp (τ t) (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (τ t))
  have hz : ∀ y : ℝ, D (0, y) = 0 := by
    have heq := hspace.unique ((interpolationGapPolynomial n t i).hasFDerivAt (τ t))
    intro y
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L y) heq
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, hτcrit, smul_zero] using h
  have hfix := hH.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (τ t))
  have hfixeq := hfix.fderiv
  have hinput := (hasFDerivAt_id (𝕜 := ℝ) t).prodMk hτdiff.differentiableAt_one.hasFDerivAt
  have hloc := hH.comp t hinput
  have heq : D ∘L (ContinuousLinearMap.id ℝ (Fin n → ℝ)).prod (fderiv ℝ τ t) =
      D ∘L ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ := by
    ext h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
    rw [show (h, fderiv ℝ τ t h) = (h, 0) + (0, fderiv ℝ τ t h) by ext <;> simp,
      map_add, hz, add_zero]
  rw [heq, ← hfixeq] at hloc
  have hpeak := hloc.congr_of_eventuallyEq (hevent.mono (fun s hs => hs.2.2.2))
  simpa only [hτself, H, Function.comp_def] using hpeak

/-- Differentiating the actual fixed nodal equations gives the corresponding
node functional derivative of the gap polynomial.
Source: the chain rule applied to the nodal interpolation equations;
focused reroutes, peak Jacobian. -/
theorem fderiv_eval_interpolationGapPolynomial_node_apply {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (j : Fin (n + 2)) (h : Fin n → ℝ) :
    fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval (canonicalIntervalNodes n t j)) t h =
      -(interpolationGapPolynomial n t i).derivative.eval (canonicalIntervalNodes n t j) *
        fderiv ℝ (fun s => canonicalIntervalNodes n s j) t h := by
  let v := canonicalIntervalNodes n t
  let H : (Fin n → ℝ) × ℝ → ℝ := fun u => (interpolationGapPolynomial n u.1 i).eval u.2
  let D := fderiv ℝ H (t, v j)
  let N := fderiv ℝ (fun s => canonicalIntervalNodes n s j) t
  have hH : HasFDerivAt H D (t, v j) :=
    (contDiffAt_eval_interpolationGapPolynomial ht i (v j) 1).differentiableAt_one.hasFDerivAt
  have hN : HasFDerivAt (fun s => canonicalIntervalNodes n s j) N t :=
    (contDiff_canonicalIntervalNodes n j 1).contDiffAt.differentiableAt_one.hasFDerivAt
  have hnodal := hH.comp t ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk hN)
  have hevent : (fun _ : Fin n → ℝ => interpolationGapSign n i j) =ᶠ[𝓝 t]
      (fun s => H (s, canonicalIntervalNodes n s j)) := by
    filter_upwards [(isOpen_interiorNodeSimplex n).mem_nhds ht] with s hs
    exact (eval_interpolationGapPolynomial_node hs i j).symm
  have hzero := (hnodal.congr_of_eventuallyEq hevent).unique
    (hasFDerivAt_const (𝕜 := ℝ) (interpolationGapSign n i j) t)
  have hspace := hH.comp (v j) (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (v j))
  have hspaceeq := hspace.unique ((interpolationGapPolynomial n t i).hasFDerivAt (v j))
  have hfix := hH.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (v j))
  have hfixeq := hfix.fderiv
  simp only [H, v, Function.comp_def] at hfixeq
  rw [hfixeq]
  change D (h, 0) = _
  have hn0 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L h) hzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at hn0
  have hnx := congrArg (fun L : ℝ →L[ℝ] ℝ => L (N h)) hspaceeq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] at hnx
  have hadd : D (h, N h) = D (h, 0) + D (0, N h) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  change D (h, 0) = -(interpolationGapPolynomial n t i).derivative.eval (v j) * N h
  nlinarith

/-- At a fixed grid, the node derivative of a gap polynomial is reconstructed
from its actual nodal derivatives by Lagrange cardinals.
Source: differentiating degree-bounded interpolation uniqueness;
focused reroutes, peak Jacobian. -/
theorem fderiv_eval_interpolationGapPolynomial_apply_eq_sum {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (x : ℝ) (h : Fin n → ℝ) :
    fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval x) t h =
      ∑ j : Fin (n + 2), (Lagrange.basis univ (canonicalIntervalNodes n t) j).eval x *
        fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval (canonicalIntervalNodes n t j)) t h := by
  let v := canonicalIntervalNodes n t
  have hevent : (fun s => (interpolationGapPolynomial n s i).eval x) =ᶠ[𝓝 t]
      (fun s => ∑ j : Fin (n + 2), (interpolationGapPolynomial n s i).eval (v j) *
        (Lagrange.basis univ v j).eval x) := by
    filter_upwards [(isOpen_interiorNodeSimplex n).mem_nhds ht] with s hs
    have hd : (interpolationGapPolynomial n s i).degree < (univ : Finset (Fin (n + 2))).card :=
      Lagrange.degree_interpolate_lt (s := univ) (interpolationGapSign n i) hs.injective.injOn
    have hp := Lagrange.eq_interpolate (v := v) ht.injective.injOn hd
    conv_lhs => rw [hp]
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    simp only [eval_mul, eval_C]
  have hsum := HasFDerivAt.fun_sum (u := (univ : Finset (Fin (n + 2)))) (fun j _ =>
    (differentiableAt_eval_interpolationGapPolynomial ht i (v j)).hasFDerivAt.mul_const
      ((Lagrange.basis univ v j).eval x))
  have hactual := hsum.congr_of_eventuallyEq hevent
  have heq := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L h) hactual.fderiv
  simpa only [v, _root_.sum_apply, smul_apply, smul_eq_mul] using heq

/-- The fixed left canonical endpoint has zero node derivative.
Source: endpoint-fixed parametrization; focused reroutes, peak Jacobian. -/
theorem fderiv_canonicalIntervalNodes_zero (n : ℕ) (t : Fin n → ℝ) :
    fderiv ℝ (fun s => canonicalIntervalNodes n s 0) t = 0 := by
  simp

/-- The fixed right canonical endpoint has zero node derivative.
Source: endpoint-fixed parametrization; focused reroutes, peak Jacobian. -/
theorem fderiv_canonicalIntervalNodes_last (n : ℕ) (t : Fin n → ℝ) :
    fderiv ℝ (fun s => canonicalIntervalNodes n s (Fin.last (n + 1))) t = 0 := by
  simp

/-- Each actual interior node has its coordinate projection as derivative.
Source: endpoint-fixed parametrization; focused reroutes, peak Jacobian. -/
theorem fderiv_canonicalIntervalNodes_interior (n : ℕ) (t : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (fun s => canonicalIntervalNodes n s j.castSucc.succ) t =
      ContinuousLinearMap.proj j := by
  simp only [canonicalIntervalNodes_interior]
  exact (hasFDerivAt_apply (𝕜 := ℝ) j t).fderiv

/-- The actual node derivative of the signed gap polynomial is the cardinal
reconstruction of the differentiated nodal equations, with endpoints fixed.
Source: interpolation uniqueness and the chain rule;
focused reroutes, the exact peak Jacobian. -/
theorem fderiv_eval_interpolationGapPolynomial_apply {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (x : ℝ) (h : Fin n → ℝ) :
    fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval x) t h =
      ∑ j : Fin n, (-(interpolationGapPolynomial n t i).derivative.eval (t j) *
        (Lagrange.basis univ (canonicalIntervalNodes n t) j.castSucc.succ).eval x) * h j := by
  rw [fderiv_eval_interpolationGapPolynomial_apply_eq_sum ht i x h]
  simp_rw [fderiv_eval_interpolationGapPolynomial_node_apply ht i]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp_rw [fderiv_canonicalIntervalNodes_interior]
  simp only [fderiv_canonicalIntervalNodes_zero,
    show (Fin.last n).succ = Fin.last (n + 1) by rfl,
    fderiv_canonicalIntervalNodes_last, zero_apply,
    ContinuousLinearMap.proj_apply, mul_zero, zero_add, add_zero, canonicalIntervalNodes_interior]
  apply sum_congr rfl
  intro j _
  ring

/-- The actual Lebesgue gap peak has the exact node-coordinate derivative
`−F_i'(t_j) ℓ_j(τ_i)`, assembled as a continuous linear functional.
Source: differentiated nodal equations and the ordinary implicit peak chart;
focused reroutes, `polyretry:peak-jacobian`. -/
theorem hasFDerivAt_interpolationGapPeak {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    HasFDerivAt (fun s => interpolationGapPeak n s i)
      (∑ j : Fin n, (-(interpolationGapPolynomial n t i).derivative.eval (t j) *
        (Lagrange.basis univ (canonicalIntervalNodes n t) j.castSucc.succ).eval
          (interpolationGapCriticalPoint n t i)) •
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) t := by
  have h := hasFDerivAt_interpolationGapPeak_fixed_criticalPoint hn ht i
  have heq : fderiv ℝ (fun s => (interpolationGapPolynomial n s i).eval
      (interpolationGapCriticalPoint n t i)) t =
      ∑ j : Fin n, (-(interpolationGapPolynomial n t i).derivative.eval (t j) *
        (Lagrange.basis univ (canonicalIntervalNodes n t) j.castSucc.succ).eval
          (interpolationGapCriticalPoint n t i)) •
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
    ext h
    simp only [_root_.sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    exact fderiv_eval_interpolationGapPolynomial_apply ht i _ h
  rw [heq] at h
  exact h

end NLAlib
