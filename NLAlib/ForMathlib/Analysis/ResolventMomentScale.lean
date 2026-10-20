import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Resolvent moment budgets at the source spectral scale

Elementary square and cube estimates turn the actual variance and gamma
budgets into the spectral-grid error required by the universality proof.
Source: arXiv:2201.05142v3, Lemma 7.5 and Proposition 7.7.
Atlas: independent-sum-spectrum-universality (helpers, not the full target).
-/

noncomputable section
set_option autoImplicit false
namespace Real

/-- The two actual sub-Gaussian moment and realization thresholds have the
source square-root scale. Zero variance and zero height are included.
Source: arXiv:2201.05142v3, Lemma 7.3 (scalar helper). -/
theorem gaussian_resolvent_moment_fluctuations_le {σ p : ℝ}
    (hσ : 0 ≤ σ) (hp : 0 ≤ p) (η : ℝ) :
    sqrt (4*(σ^2*(η⁻¹)^4)*p)+sqrt (σ^2*(η⁻¹)^4)*sqrt (2*p) ≤
      4*σ*sqrt p/η^2 := by
  let c := σ^2*(η⁻¹)^4
  have hc : 0 ≤ c := by positivity
  have hs : sqrt c = σ/η^2 := by
    rw [show c = (σ*(η⁻¹)^2)^2 by dsimp [c]; ring, sqrt_sq (by positivity)]
    simp only [div_eq_mul_inv, inv_pow]
  have ha : sqrt (4*c*p) = 2*sqrt c*sqrt p := by
    have he : (2*sqrt c*sqrt p)^2 = 4*c*p := by
      rw [mul_pow,mul_pow,sq_sqrt hc,sq_sqrt hp]
      ring
    rw [← he,sqrt_sq (by positivity)]
  have hb : sqrt (2*p) ≤ 2*sqrt p :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_sqrt hp]⟩
  have hh := mul_le_mul_of_nonneg_left hb (sqrt_nonneg c)
  calc
    _ ≤ 2*sqrt c*sqrt p+sqrt c*(2*sqrt p) := by rw [ha]; exact add_le_add le_rfl hh
    _ = _ := by rw [hs]; ring

/-- The square-root mixed variance term is bounded by the spectral scale
using its linear and cubic defining inequalities.
Source: arXiv:2201.05142v3, Proposition 7.7 (scalar helper). -/
theorem mixed_resolvent_scale_le_sq {R σ p δ : ℝ}
    (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hRp : R*p ≤ δ) (hcube : R*σ^2*p^2 ≤ δ^3) :
    R*σ*p*sqrt p ≤ δ^2 := by
  have hm := mul_le_mul hcube hRp (mul_nonneg hR hp) (pow_nonneg hδ 3)
  have hs : (R*σ*p*sqrt p)^2 ≤ (δ^2)^2 := by
    calc
      _ = (R*σ^2*p^2)*(R*p) := by
        rw [mul_pow, mul_pow, mul_pow, sq_sqrt hp]
        ring
      _ ≤ δ^3*δ := hm
      _ = _ := by ring
  exact (sq_le_sq₀ (by positivity) (sq_nonneg δ)).mp hs

/-- The explicit resolvent variance and gamma budgets have uniformly bounded
normalized size once their original scalar components are bounded.
Source: arXiv:2201.05142v3, Lemma 7.5 (scalar helper). -/
theorem resolvent_variance_and_gamma_scale_le
    {R E Q v ℓ p δ η : ℝ} (hQ : 0 ≤ Q) (hp : 0 ≤ p)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hδη : δ ≤ η)
    (hvp : v*p ≤ δ^2) (hRE : R*E*p ≤ 3*δ^2)
    (hRQ : R^2*Q*p ≤ δ^4) (hRℓ : R^4*ℓ*p ≤ δ^4)
    (hRp : R^2*p^2 ≤ δ^2) (hR4p : R^4*p^2 ≤ δ^4) :
    let B := (2/η^4)*(8*v+64*R*E)+(32*R^2/η^6)*((exp 1-1)*Q+R^2*ℓ)
    let c := sqrt (6*(16*R^2/η^4+64*R^4/η^6))
    B*p ≤ 500*(δ/η^2)^2 ∧ c*p ≤ 22*(δ/η^2) := by
  let T := δ/η^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hdiv : δ^4/η^6 ≤ δ^2/η^4 := by
    rw [div_le_div_iff₀ (pow_pos hη 6) (pow_pos hη 4)]
    have hm := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hδ hη.le).mpr hδη) (mul_nonneg (sq_nonneg δ) (pow_nonneg hη.le 4))
    calc
      _ = (δ^2*η^4)*δ^2 := by ring
      _ ≤ (δ^2*η^4)*η^2 := hm
      _ = _ := by ring
  have hTtwo : δ^2/η^4 = T^2 := by dsimp [T]; ring
  have hfirst : (2/η^4)*(8*v+64*R*E)*p ≤ 400*δ^2/η^4 := by
    have hn : 2*(8*v+64*R*E)*p ≤ 400*δ^2 := by
      linear_combination 16*hvp+128*hRE
    calc
      _ = (2*(8*v+64*R*E)*p)/η^4 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hn (pow_nonneg hη.le 4)
  have hRQnonneg : 0 ≤ R^2*Q*p := by positivity
  have he := mul_le_mul_of_nonneg_right
    (sub_le_sub_right exp_one_lt_three.le 1) hRQnonneg
  have hsecond : (32*R^2/η^6)*((exp 1-1)*Q+R^2*ℓ)*p ≤ 96*δ^4/η^6 := by
    have hn : 32*R^2*((exp 1-1)*Q+R^2*ℓ)*p ≤ 96*δ^4 := by
      linear_combination 32*he+64*hRQ+32*hRℓ
    calc
      _ = (32*R^2*((exp 1-1)*Q+R^2*ℓ)*p)/η^6 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hn (pow_nonneg hη.le 6)
  have hB : ((2/η^4)*(8*v+64*R*E)+(32*R^2/η^6)*((exp 1-1)*Q+R^2*ℓ))*p ≤
      500*T^2 := by
    have hd := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 96)
    rw [hTtwo] at hd
    have hf : 400*δ^2/η^4 = 400*T^2 := by rw [mul_div_assoc, hTtwo]
    have hs : 96*δ^4/η^6 = 96*(δ^4/η^6) := by ring
    rw [hf] at hfirst
    rw [hs] at hsecond
    nlinarith only [hfirst, hsecond, hd, sq_nonneg T]
  have hκ : 0 ≤ 6*(16*R^2/η^4+64*R^4/η^6) := by positivity
  have hc_sq : (sqrt (6*(16*R^2/η^4+64*R^4/η^6))*p)^2 =
      96*(R^2*p^2/η^4)+384*(R^4*p^2/η^6) := by
    rw [mul_pow, sq_sqrt hκ]
    ring
  have hcp_sq : (sqrt (6*(16*R^2/η^4+64*R^4/η^6))*p)^2 ≤ 480*T^2 := by
    have h1 := div_le_div_of_nonneg_right hRp (pow_nonneg hη.le 4)
    have h2 := div_le_div_of_nonneg_right hR4p (pow_nonneg hη.le 6)
    have h3 := h2.trans hdiv
    rw [hTtwo] at h1 h3
    rw [hc_sq]
    nlinarith only [h1,h3]
  refine ⟨hB, ?_⟩
  have hleft : 0 ≤ sqrt (6*(16*R^2/η^4+64*R^4/η^6))*p := by positivity
  have hright : 0 ≤ 22*T := by positivity
  apply (sq_le_sq₀ hleft hright).mp
  nlinarith only [hcp_sq, sq_nonneg T]

/-- The original bilinear, matrix and radius scale inequalities imply the
required bounds on the literal resolvent variance and gamma expressions.
Source: arXiv:2201.05142v3, Lemma 7.5 and Proposition 7.7.
atlas: independent-sum-spectrum-universality (partial) -/
theorem resolvent_variance_scale_le_of_source_parameters
    {R σ s E Q ℓ p δ η : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hp : 1 ≤ p) (hδ : 0 ≤ δ) (hη : 0 < η) (hδη : δ ≤ η)
    (hE : E ≤ 2*σ*sqrt p+R*p) (hQ0 : 0 ≤ Q) (hQ : Q ≤ σ^2) (hℓ : ℓ ≤ p)
    (hsp : s*sqrt p ≤ δ) (hRp : R*p ≤ δ) (hcube : R*σ^2*p^2 ≤ δ^3) :
    let B := (2/η^4)*(8*s^2+64*R*E)+(32*R^2/η^6)*((exp 1-1)*Q+R^2*ℓ)
    let c := sqrt (6*(16*R^2/η^4+64*R^4/η^6))
    B*p ≤ 500*(δ/η^2)^2 ∧ c*p ≤ 22*(δ/η^2) := by
  have hp0 : 0 ≤ p := by linarith
  have hp2 : 1 ≤ p^2 := by nlinarith
  have hsp2 : s^2*p ≤ δ^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ s*sqrt p) hsp 2
    simpa only [mul_pow, sq_sqrt hp0] using hh
  have hRp2 : R^2*p^2 ≤ δ^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hR hp0) hRp 2
  have hmixed := mixed_resolvent_scale_le_sq hR hσ hp0 hδ hRp hcube
  have hRE : R*E*p ≤ 3*δ^2 := by
    have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hR hp0)
    nlinarith only [hh,hmixed,hRp2]
  have hRQ : R^2*Q*p ≤ δ^4 := by
    have hvar := mul_le_mul_of_nonneg_left hQ
      (mul_nonneg (sq_nonneg R) hp0)
    have hstep := mul_le_mul_of_nonneg_left hp2
      (mul_nonneg (mul_nonneg (sq_nonneg R) (sq_nonneg σ)) hp0)
    have hmsq := pow_le_pow_left₀ (by positivity : 0 ≤ R*σ*p*sqrt p) hmixed 2
    calc
      _ ≤ R^2*σ^2*p := by nlinarith only [hvar]
      _ ≤ R^2*σ^2*p*p^2 := by simpa only [mul_one] using hstep
      _ = (R*σ*p*sqrt p)^2 := by
        rw [mul_pow,mul_pow,mul_pow,sq_sqrt hp0]
        ring
      _ ≤ (δ^2)^2 := hmsq
      _ = _ := by ring
  have hR4p : R^4*p^2 ≤ δ^4 := by
    have hstep := mul_le_mul_of_nonneg_left hp2 (sq_nonneg p)
    have hmul := mul_le_mul_of_nonneg_left hstep (pow_nonneg hR 4)
    have hfour := pow_le_pow_left₀ (mul_nonneg hR hp0) hRp 4
    calc
      _ ≤ R^4*(p^2*p^2) := by simpa only [mul_one] using hmul
      _ = (R*p)^4 := by ring
      _ ≤ _ := hfour
  have hRℓ : R^4*ℓ*p ≤ δ^4 := by
    have hh := mul_le_mul_of_nonneg_left hℓ (mul_nonneg (pow_nonneg hR 4) hp0)
    have hle : R^4*ℓ*p ≤ R^4*p^2 := by nlinarith only [hh]
    exact hle.trans hR4p
  exact resolvent_variance_and_gamma_scale_le hQ0 hp0 hδ hη hδη
    hsp2 hRE hRQ hRℓ hRp2 hR4p

/-- The paired moment and concentration errors, the comparison remainder
and the grid mesh fit one uniform reciprocal-square height bound.
Source: arXiv:2201.05142v3, Proposition 7.7 (scalar helper). -/
theorem resolvent_grid_error_le_of_source_moment_budgets
    {B c p V δ η ε : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hε : ε ≤ δ)
    (hB : B*p ≤ 500*(δ/η^2)^2) (hc : c*p ≤ 22*(δ/η^2))
    (hV : V ≤ 8192*(δ/η^2)) :
    9*(4*sqrt (12*B*p)+8*c*p+sqrt (24*B*p)+c*p+V)+10*ε/η^2 ≤
      80000*δ/η^2 := by
  let T := δ/η^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have h12 : sqrt (12*B*p) ≤ 80*T := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hB, sq_nonneg T]
  have h24 : sqrt (24*B*p) ≤ 110*T := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hB, sq_nonneg T]
  have hmesh : ε/η^2 ≤ T := div_le_div_of_nonneg_right hε (sq_nonneg η)
  have htarget : 80000*δ/η^2 = 80000*T := by dsimp [T]; ring
  change c*p ≤ 22*T at hc
  change V ≤ 8192*T at hV
  have hmesh10 : 10*ε/η^2 ≤ 10*T := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hmesh
      (by norm_num : (0 : ℝ) ≤ 10)
  rw [htarget]
  linear_combination 36*h12+9*h24+81*hc+9*hV+hmesh10+610*hT

/-- The actual rooted-moment comparison remainder has reciprocal-square
height size at the linear and cubic source scales.
Source: arXiv:2201.05142v3, Propositions 7.4 and 7.7 (scalar helper). -/
theorem resolvent_comparison_remainder_le_of_source_parameters
    {R σ Q p δ η : ℝ} (hR : 0 ≤ R) (hp : 0 ≤ p)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hδη : δ ≤ η) (hQ : Q ≤ σ^2)
    (hRp : R*p ≤ δ) (hcube : R*σ^2*p^2 ≤ δ^3) :
    4096*(p^2*R*Q+p^3*R^3)/η^4 ≤ 8192*δ/η^2 := by
  have hfirst : p^2*R*Q ≤ δ^3 := by
    have hh := mul_le_mul_of_nonneg_left hQ (mul_nonneg (sq_nonneg p) hR)
    nlinarith only [hh,hcube]
  have hsecond : p^3*R^3 ≤ δ^3 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hR hp) hRp 3
    simpa only [mul_pow,mul_comm] using hh
  have hdiv : δ^3/η^4 ≤ δ/η^2 := by
    rw [div_le_div_iff₀ (pow_pos hη 4) (pow_pos hη 2)]
    have hh := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hδ hη.le).mpr hδη) (mul_nonneg hδ (sq_nonneg η))
    calc
      _ = (δ*η^2)*δ^2 := by ring
      _ ≤ (δ*η^2)*η^2 := hh
      _ = _ := by ring
  have hn : 4096*(p^2*R*Q+p^3*R^3) ≤ 8192*δ^3 := by
    linear_combination 4096*hfirst+4096*hsecond
  calc
    _ ≤ 8192*δ^3/η^4 := div_le_div_of_nonneg_right hn (pow_nonneg hη.le 4)
    _ = 8192*(δ^3/η^4) := by ring
    _ ≤ 8192*(δ/η^2) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = _ := by ring

/-- A height above an explicit multiple of the spectral scale absorbs the
computed reciprocal-square error into half the spectral-point resolvent.
Source: arXiv:2201.05142v3, Lemma 7.1 (scalar helper). -/
theorem resolvent_grid_error_le_inv_two_height
    {δ η : ℝ} (hη : 0 < η) (hheight : 160000*δ ≤ η) :
    80000*δ/η^2 ≤ (2*η)⁻¹ := by
  rw [← one_div, div_le_div_iff₀ (pow_pos hη 2) (by positivity : 0 < 2*η)]
  have hh := mul_le_mul_of_nonneg_left hheight hη.le
  nlinarith only [hh]

end Real
