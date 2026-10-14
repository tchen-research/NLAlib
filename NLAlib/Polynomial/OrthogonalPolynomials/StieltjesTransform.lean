import NLAlib.Polynomial.OrthogonalPolynomials.SecondKind
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiLocation
import NLAlib.Polynomial.Quadrature.ComplexExactness

/-! # Actual complex Stieltjes transforms and Gauss cancellation

Finite positive measures on a compact real interval give ordinary complex
Bochner transforms. The canonical second-kind numerator and its square-norm
error are identified by finite polynomial exactness, without a continued
fraction or an assumed transform identity.
Source: Gautschi (2004), Chapter 1; operator derivations AQ16--AQ19.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset

namespace NLAlib

/-- The ordinary complex Stieltjes transform of a real measure. The integral
is total; off-support hypotheses below ensure the intended finite value. -/
def stieltjesTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ

/-- A compactly supported finite measure integrates every complex polynomial
divided by a pole-free linear denominator. -/
theorem integrable_complex_eval_div_sub_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) (p : ℂ[X]) :
    Integrable (fun x : ℝ => p.eval (x : ℂ) / (z - (x : ℂ))) μ := by
  have hc : ContinuousOn (fun x : ℝ => p.eval (x : ℂ) / (z - (x : ℂ))) (Icc a b) :=
    (p.continuous.comp Complex.continuous_ofReal).continuousOn.div
      (continuous_const.sub Complex.continuous_ofReal).continuousOn
      (fun x hx => sub_ne_zero.mpr (hz x hx))
  refine (hc.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [hμ] with x hx hnot
  exact (hnot hx).elim

private theorem gauss_poly_complex_eval_eq_zero {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    (i : Fin n) :
    ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
      Complex.ofRealHom).eval (gaussNodes μ hμ n i : ℂ) = 0 := by
  change ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
    Complex.ofRealHom).eval (Complex.ofRealHom (gaussNodes μ hμ n i)) = 0
  rw [eval_map_apply]
  have h := (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  rw [h, map_zero]

/-- The canonical monic polynomial has no complex zero outside the closed
real support enclosure, including at finite-support termination. -/
theorem eval_map_monicOrthogonalPolynomial_ne_zero_of_off_Icc
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
      Complex.ofRealHom).eval z ≠ 0 := by
  rw [← nodal_gaussNodes_eq_monicOrthogonalPolynomial hμ hn, Lagrange.nodal_eq,
    Polynomial.map_prod, eval_prod]
  apply prod_ne_zero_iff.mpr
  intro i _
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (hz _ (gaussNodes_mem_Icc hμ hs hn i))

/-- The mapped second-kind polynomial is the integral of the actual complex
divided difference of the canonical real monic polynomial.
Source: Gautschi (2004), Chapter 1, AQ16.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_eq_integral_dividedDifference
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) (z : ℂ) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      ∫ x : ℝ, (((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
        Complex.ofRealHom).dividedDifference z).eval (x : ℂ) ∂μ := by
  let L := polynomialIntegral μ hμ
  let p := monicOrthogonalPolynomial L n
  have hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0 := fun k hk =>
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn)
  have hexact : ∀ q : ℝ[X], q.degree < n → L q =
      ∑ i : Fin n, gaussWeights μ hμ n i * q.eval (gaussNodes μ hμ n i) := by
    intro q hq
    exact integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn
      (hq.trans_le (by exact_mod_cast (show n ≤ 2*n by omega)))
  rw [secondKindPolynomial_eq_sum_weight_mul_dividedDifference L n hn0 hL _ _ hexact,
    Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_finsetSum, eval_mul, eval_C]
  rw [integral_complex_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn
    ((degree_dividedDifference_lt hn0 (by rw [natDegree_map, natDegree_monicOrthogonalPolynomial]) z).trans_le
      (by exact_mod_cast (show n ≤ 2*n by omega)))]
  apply sum_congr rfl
  intro i _
  congr 1
  have hm : ((p.dividedDifference (gaussNodes μ hμ n i)).map Complex.ofRealHom) =
      (p.map Complex.ofRealHom).dividedDifference (gaussNodes μ hμ n i : ℂ) := by
    apply mul_left_cancel₀ (monic_X_sub_C (gaussNodes μ hμ n i : ℂ)).ne_zero
    rw [X_sub_C_mul_dividedDifference]
    have h := congrArg (Polynomial.map Complex.ofRealHom)
      (X_sub_C_mul_dividedDifference p (gaussNodes μ hμ n i))
    rw [show (gaussNodes μ hμ n i : ℂ) = Complex.ofRealHom (gaussNodes μ hμ n i) by rfl,
      eval_map_apply]
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using h
  rw [hm, eval_dividedDifference_comm]

/-- At every point outside the support enclosure, the actual second-kind
ratio is the Stieltjes transform of the canonical Gauss atomic rule.
Source: Gautschi (2004), Chapter 1, AQ18.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) / (z - (gaussNodes μ hμ n i : ℂ)) := by
  apply eval_map_secondKindPolynomial_div_eq_sum_weight_div Complex.ofRealHom
    (polynomialIntegral μ hμ) n hn0
    (fun k hk => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn))
  · intro i
    exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  · intro p hp
    exact integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn
      (hp.trans_le (by exact_mod_cast (show n ≤ 2*n by omega)))
  · exact eval_map_monicOrthogonalPolynomial_ne_zero_of_off_Icc hμ hs hn hz
  · intro i
    exact hz _ (gaussNodes_mem_Icc hμ hs hn i)

/-- Subtracting the finite second-kind ratio from the native transform is the
native Cauchy transform of the monic polynomial divided by its value at `z`.
Source: Gautschi (2004), Chapter 1, first equality in AQ19.
atlas: jacobi-fraction-second-kind (partial), gauss-remainder-contour-kernel (partial) -/
theorem stieltjesTransform_sub_secondKind_div_eq_integral
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    stieltjesTransform μ z -
      ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      (∫ x : ℝ, ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
        Complex.ofRealHom).eval (x : ℂ) / (z - (x : ℂ)) ∂μ) /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let p := (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom
  have hpz := eval_map_monicOrthogonalPolynomial_ne_zero_of_off_Icc hμ hs hn hz
  have h1 := integrable_complex_eval_div_sub_of_ae_mem_Icc hs hz (1 : ℂ[X])
  simp only [eval_one, one_div] at h1
  have hp := integrable_complex_eval_div_sub_of_ae_mem_Icc hs hz p
  have hdd := hμ.integrable_complex_eval (p.dividedDifference z)
  have he : (∫ x : ℝ, p.eval (x : ℂ)/(z-(x:ℂ)) ∂μ) =
      p.eval z * stieltjesTransform μ z -
        ∫ x : ℝ, (p.dividedDifference z).eval (x : ℂ) ∂μ := by
    rw [stieltjesTransform, ← integral_const_mul, ← integral_sub (h1.const_mul _) hdd]
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [eval_dividedDifference_of_ne _ (fun h => hz x hx h.symm)]
    field_simp [sub_ne_zero.mpr (hz x hx), sub_ne_zero.mpr (fun h => hz x hx h.symm)]
    ring
  rw [eval_map_secondKindPolynomial_eq_integral_dividedDifference hμ hn0 hn z, he]
  change _ - _ / p.eval z = (p.eval z * _ - _) / p.eval z
  rw [sub_div, mul_div_cancel_left₀ _ hpz]

/-- Polynomial orthogonality turns the native Stieltjes error into the exact
positive-norm numerator integral. Source: Gautschi (2004), Chapter 1, AQ19.
atlas: jacobi-fraction-second-kind (partial), gauss-remainder-contour-kernel (partial) -/
theorem stieltjesTransform_sub_secondKind_div_eq_integral_sq
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    stieltjesTransform μ z -
      ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      (∫ x : ℝ, ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
        Complex.ofRealHom).eval (x : ℂ)^2 / (z - (x : ℂ)) ∂μ) /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z^2 := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let p := (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom
  have hpz := eval_map_monicOrthogonalPolynomial_ne_zero_of_off_Icc hμ hs hn hz
  have hd : (p * p.dividedDifference z).degree < (2*n : ℕ) := by
    apply (degree_mul_le _ _).trans_lt
    have hpdeg : p.degree = (n : ℕ) := by
      dsimp only [p]
      rw [degree_map_eq_of_injective Complex.ofRealHom.injective,
        degree_eq_natDegree (monic_monicOrthogonalPolynomial _ _).ne_zero,
        natDegree_monicOrthogonalPolynomial]
    rw [hpdeg]
    have hdd := degree_dividedDifference_lt (p := p) hn0
      (by dsimp [p]; rw [natDegree_map, natDegree_monicOrthogonalPolynomial]) z
    exact (WithBot.add_lt_add_left (by simp) hdd).trans_eq (by norm_cast; omega)
  have hzero : (∫ x : ℝ, p.eval (x : ℂ) * (p.dividedDifference z).eval (x : ℂ) ∂μ) = 0 := by
    have he := integral_complex_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn hd
    simp only [eval_mul] at he
    rw [he]
    apply sum_eq_zero
    intro i _
    simp only [p, gauss_poly_complex_eval_eq_zero hμ hn i, zero_mul, mul_zero]
  have hp := integrable_complex_eval_div_sub_of_ae_mem_Icc hs hz p
  have hsquare := integrable_complex_eval_div_sub_of_ae_mem_Icc hs hz (p^2)
  simp only [eval_pow] at hsquare
  have hdd := hμ.integrable_complex_eval (p * p.dividedDifference z)
  simp only [eval_mul] at hdd
  have he : p.eval z * (∫ x : ℝ, p.eval (x : ℂ)/(z-(x:ℂ)) ∂μ) =
      ∫ x : ℝ, p.eval (x : ℂ)^2/(z-(x:ℂ)) ∂μ := by
    rw [← integral_const_mul]
    calc
      _ = (∫ x : ℝ, p.eval (x : ℂ)^2/(z-(x:ℂ)) +
          p.eval (x : ℂ) * (p.dividedDifference z).eval (x : ℂ) ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hs] with x hx
        rw [eval_dividedDifference_of_ne _ (fun h => hz x hx h.symm)]
        field_simp [sub_ne_zero.mpr (hz x hx), sub_ne_zero.mpr (fun h => hz x hx h.symm)]
        ring
      _ = _ := by rw [integral_add hsquare hdd, hzero, add_zero]
  rw [stieltjesTransform_sub_secondKind_div_eq_integral hμ hs hn0 hn hz]
  change _ / p.eval z = _ / p.eval z^2
  rw [← he]
  change p.eval z ≠ 0 at hpz
  field_simp
  rfl

/-- The exact native Stieltjes error is bounded by the squared monic norm
divided by a positive support distance and the squared denominator value.
`δ` is any positive lower bound for the distance to the support enclosure.
Source: Gautschi (2004), Chapter 1, AQ19 and AQ25.
atlas: jacobi-fraction-second-kind (partial), gauss-remainder-contour-kernel (partial) -/
theorem norm_stieltjesTransform_sub_secondKind_div_le
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ Icc a b, δ ≤ ‖z - (x : ℂ)‖) :
    ‖stieltjesTransform μ z -
      ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z‖ ≤
      orthogonalPolynomialNorm (polynomialIntegral μ hμ) n /
        (δ * ‖((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
          Complex.ofRealHom).eval z‖^2) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let p := monicOrthogonalPolynomial (polynomialIntegral μ hμ) n
  have hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ) := by
    intro x hx h
    have h' := hgap x hx
    rw [h, sub_self, norm_zero] at h'
    linarith
  have hbound : ‖∫ x : ℝ, ((p.map Complex.ofRealHom).eval (x : ℂ))^2 /
      (z-(x:ℂ)) ∂μ‖ ≤ orthogonalPolynomialNorm (polynomialIntegral μ hμ) n / δ := by
    have hint : Integrable (fun x : ℝ => (p.eval x)^2/δ) μ := by
      simpa only [eval_pow] using
        (show Integrable (fun x : ℝ => (p^2).eval x/δ) μ from (hμ (p^2)).div_const δ)
    have h := norm_integral_le_of_norm_le hint (show ∀ᵐ x : ℝ ∂μ,
        ‖((p.map Complex.ofRealHom).eval (x : ℂ))^2 / (z-(x:ℂ))‖ ≤ (p.eval x)^2/δ by
      filter_upwards [hs] with x hx
      change ‖((p.map Complex.ofRealHom).eval (Complex.ofRealHom x))^2 / (z-(x:ℂ))‖ ≤ _
      rw [eval_map_apply, norm_div, norm_pow]
      change ‖((p.eval x : ℝ) : ℂ)‖^2 / ‖z-(x:ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hδ (hgap x hx))
    simpa only [integral_div, orthogonalPolynomialNorm, polynomialIntegral_apply, eval_pow, p] using h
  rw [stieltjesTransform_sub_secondKind_div_eq_integral_sq hμ hs hn0 hn hz, norm_div, norm_pow]
  change ‖∫ x : ℝ, ((p.map Complex.ofRealHom).eval (x : ℂ))^2 / (z-(x:ℂ)) ∂μ‖ /
    ‖(p.map Complex.ofRealHom).eval z‖^2 ≤ _
  exact (div_le_div_of_nonneg_right hbound (sq_nonneg _)).trans_eq (div_div _ _ _)

/-- At finite-support termination, the second-kind ratio equals the native
Stieltjes transform exactly. It is the atomic terminal case of Markov's theorem.
Source: Gautschi (2004), Chapter 1, finite-support termination.
atlas: jacobi-fraction-second-kind (partial) -/
theorem secondKindPolynomial_div_eq_stieltjesTransform_of_encard_eq
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : μ.support.encard = n) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      stieltjesTransform μ z := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  have he := stieltjesTransform_sub_secondKind_div_eq_integral hμ hs hn0 hn.ge hz
  have hint : (∫ x : ℝ, ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
      Complex.ofRealHom).eval (x:ℂ)/(z-(x:ℂ)) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [μ.support_mem_ae] with x hx
    change ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
      Complex.ofRealHom).eval (Complex.ofRealHom x)/(z-(x:ℂ)) = 0
    rw [eval_map_apply,
      (eval_monicOrthogonalPolynomial_eq_zero_iff_mem_support_of_encard_eq hμ hn x).mpr hx,
      map_zero, zero_div]
  rw [hint, zero_div] at he
  exact (sub_eq_zero.mp he).symm

end NLAlib
