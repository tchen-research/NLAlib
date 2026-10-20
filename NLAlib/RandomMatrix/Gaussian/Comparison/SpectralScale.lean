import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# The square-root, cubic and linear spectral-universality scale

Elementary inequalities match the source's displayed scale exactly, and
convert a logarithmic integer moment order into its real tail parameter.
Source: arXiv:2201.05142v3, Theorem 2.6 and Proposition 7.7.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- The source spectral-universality scale; the cube-root grouping keeps
the matrix variance and increment radius visible in its defining inequality.
Source: arXiv:2201.05142v3, Theorem 2.6. -/
def independentSumSpectralScale (R s σ t : ℝ) : ℝ :=
  s*Real.sqrt t+(R*σ^2*t^2)^(1/3 : ℝ)+R*t

/-- The grouped cube root is exactly the source's product of fractional
powers, including zero radius, variance or time. -/
theorem independentSumSpectralScale_eq {R s σ t : ℝ}
    (hR : 0≤R) (hσ : 0≤σ) (ht : 0≤t) :
    independentSumSpectralScale R s σ t =
      s*Real.sqrt t+R^(1/3 : ℝ)*σ^(2/3 : ℝ)*t^(2/3 : ℝ)+R*t := by
  unfold independentSumSpectralScale
  rw [Real.mul_rpow (mul_nonneg hR (sq_nonneg σ)) (sq_nonneg t),
    Real.mul_rpow hR (sq_nonneg σ)]
  rw [← Real.rpow_natCast_mul hσ 2 (1/3 : ℝ),
    ← Real.rpow_natCast_mul ht 2 (1/3 : ℝ)]
  norm_num

/-- The actual source scale is nonnegative. -/
theorem independentSumSpectralScale_nonneg {R s σ t : ℝ}
    (hR : 0≤R) (hs : 0≤s) (ht : 0≤t) :
    0 ≤ independentSumSpectralScale R s σ t := by
  unfold independentSumSpectralScale
  positivity

/-- The linear and square-root components fit in the source scale. -/
theorem sqrt_add_linear_le_independentSumSpectralScale {R s σ t : ℝ} (hR : 0≤R) :
    s*Real.sqrt t+R*t ≤ independentSumSpectralScale R s σ t := by
  have hh := Real.rpow_nonneg (show 0≤R*σ^2*t^2 by positivity) (1/3 : ℝ)
  dsimp [independentSumSpectralScale]
  linarith only [hh]

/-- Cubing the source scale dominates the literal mixed variance monomial. -/
theorem mixed_variance_le_independentSumSpectralScale_cube {R s σ t : ℝ}
    (hR : 0≤R) (hs : 0≤s) (ht : 0≤t) :
    R*σ^2*t^2≤(independentSumSpectralScale R s σ t)^3 := by
  have hx : 0≤R*σ^2*t^2 := by positivity
  have hroot : ((R*σ^2*t^2)^(1/3 : ℝ))^3=R*σ^2*t^2 := by
    simpa only [Nat.cast_ofNat,show (1/3 : ℝ)=(3 : ℝ)⁻¹ by norm_num] using
      Real.rpow_inv_natCast_pow hx (by decide : (3 : ℕ)≠0)
  have hle : (R*σ^2*t^2)^(1/3 : ℝ) ≤ independentSumSpectralScale R s σ t := by
    dsimp [independentSumSpectralScale]
    have h1 : 0≤s*Real.sqrt t := by positivity
    have h2 : 0≤R*t := by positivity
    linarith only [h1,h2]
  simpa only [hroot] using pow_le_pow_left₀ (Real.rpow_nonneg hx _) hle 3

/-- An integer moment order bounded by `22*t` satisfies the exact linear
and cubic source-scale inequalities with scale `22*Δ(t)`. -/
theorem sqrt_add_linear_and_mixed_variance_le_twenty_two_spectralScale {R s σ t p : ℝ}
    (hR : 0≤R) (hs : 0≤s) (ht : 0≤t) (hp : 0≤p) (hpt : p≤22*t) :
    s*Real.sqrt p+R*p≤22*independentSumSpectralScale R s σ t ∧
      R*σ^2*p^2≤(22*independentSumSpectralScale R s σ t)^3 := by
  have hsqrt : Real.sqrt p≤22*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt ht]
    nlinarith only [hpt,ht]
  have hm := mul_le_mul_of_nonneg_left hsqrt hs
  have hlin := mul_le_mul_of_nonneg_left hpt hR
  have hbase := sqrt_add_linear_le_independentSumSpectralScale (s:=s) (σ:=σ) (t:=t) hR
  have hD := independentSumSpectralScale_nonneg (σ:=σ) hR hs ht
  refine ⟨by linear_combination hm+hlin+22*hbase,?_⟩
  have hp2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpt 2)
    (mul_nonneg hR (sq_nonneg σ))
  have hcube := mixed_variance_le_independentSumSpectralScale_cube (σ:=σ) hR hs ht
  have hD3 : 0≤(independentSumSpectralScale R s σ t)^3 := pow_nonneg hD 3
  nlinarith only [hp2,hcube,hD3]

end NLAlib

namespace Real

/-- A logarithmic moment order absorbs the full quadratic grid prefactor
into the source `d*exp(-t)` tail, uniformly in `d≥2`. -/
theorem sixty_mul_sq_mul_exp_neg_le_of_log_le {d t p : ℝ}
    (hd : 2≤d) (ht : log d≤t) (hp : 20*t≤p) :
    60*d^2*exp (-p)≤d*exp (-t) := by
  have hdpos : 0<d := by linarith
  have ht2 : log 2≤t := (log_le_log (by norm_num) hd).trans ht
  have h60 : (60 : ℝ)≤exp (18*t) := by
    calc
      _ ≤ (2 : ℝ)^18 := by norm_num
      _ = exp (18*log 2) := by
        simpa only [Nat.cast_ofNat,exp_log (by norm_num : (0 : ℝ)<2)] using
          (exp_nat_mul (log 2) 18).symm
      _ ≤ _ := exp_le_exp.mpr (by linarith only [ht2])
  have hdt : d≤exp t := by
    rw [← exp_log hdpos]
    exact exp_le_exp.mpr ht
  have hprod : 60*d≤exp (19*t) := by
    calc
      _ ≤ exp (18*t)*exp t := mul_le_mul h60 hdt hdpos.le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hexp : exp (-p)≤exp (-(20*t)) := exp_le_exp.mpr (by linarith only [hp])
  calc
    _ ≤ 60*d^2*exp (-(20*t)) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = d*((60*d)*exp (-(20*t))) := by ring
    _ ≤ d*(exp (19*t)*exp (-(20*t))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hprod (exp_pos _).le) hdpos.le
    _ = _ := by rw [← exp_add]; congr 2; ring

end Real
