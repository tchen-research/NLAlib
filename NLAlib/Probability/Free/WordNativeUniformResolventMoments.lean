import NLAlib.Probability.Free.WordNativeLinearResolventMoments
import NLAlib.Probability.Free.WordNativeHighResolventMoments

/-!
# Actual free resolvent moments at logarithmic order and every height

The mean-clipping estimate at low heights and the actual vacuum-vector
estimate at high heights cover every upper-half-plane parameter whose
real part lies in the actual free spectrum. Explicit polynomial choices
of clip radius and approximation degree keep the moment factor universal.
Source: arXiv:2406.11453v2, Corollary 4.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

private theorem nativeResolventMomentFactor_le {d p : ℝ}
    (hd : 1≤d) (hp : 1≤p) (hlog : Real.log d≤p) :
    d^(3/(4*p))*(72*p*d^4+1)^(3/(4*p))≤73*Real.exp 5 := by
  have hdpos : 0<d := zero_lt_one.trans_le hd
  have hppos : 0<p := zero_lt_one.trans_le hp
  have hbase : 0<72*p*d^4+1 := by positivity
  have hsize : 72*p*d^4+1≤73*p*d^4 := by
    have hpow : 1≤d^4 := one_le_pow₀ hd
    have hh := one_le_mul_of_one_le_of_one_le hp hpow
    nlinarith only [hh]
  have hlogbase : Real.log (72*p*d^4+1)≤Real.log 73+Real.log p+4*Real.log d := by
    have h := Real.log_le_log hbase hsize
    rw [Real.log_mul (by positivity) (pow_ne_zero 4 hdpos.ne'),
      Real.log_mul (by norm_num) hppos.ne',Real.log_pow] at h
    exact h
  have hlogp : Real.log p≤p-1 := Real.log_le_sub_one_of_pos hppos
  have hlog73 : 0≤Real.log (73 : ℝ) := Real.log_nonneg (by norm_num)
  have hcross : 0≤(p-1)*Real.log (73 : ℝ) := mul_nonneg (sub_nonneg.mpr hp) hlog73
  have hnum : 3*(Real.log d+Real.log (72*p*d^4+1))≤(Real.log 73+5)*(4*p) := by
    nlinarith only [hlogbase,hlogp,hlog,hp,hlog73,hcross]
  calc
    _ = Real.exp (Real.log d*(3/(4*p))+Real.log (72*p*d^4+1)*(3/(4*p))) := by
      rw [Real.rpow_def_of_pos hdpos,Real.rpow_def_of_pos hbase,Real.exp_add]
    _ ≤ Real.exp (Real.log 73+5) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = 3*(Real.log d+Real.log (72*p*d^4+1))/(4*p) := by ring
        _ ≤ _ := (div_le_iff₀ (show 0<4*p by positivity)).mpr hnum
    _ = _ := by rw [Real.exp_add,Real.exp_log (by norm_num : 0<(73 : ℝ))]

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

/-- The actual coefficient free resolvent is controlled by its genuine
amplified vacuum Gram moment at logarithmic order, uniformly in the full
mean and at every positive height. The explicit approximation error is
strong enough for the source's weak-variance scaling, even when that
variance is bounded using a crude coordinate trace estimate.

Source: arXiv:2406.11453v2, Corollary 4.4.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_log_order
    (q : ℕ) (hq : 0<q) (hlog : Real.log (Fintype.card D : ℝ)≤q)
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ k, (A k).IsHermitian)
    {z : ℂ} (hz : 0<z.im)
    (hspec : z.re∈spectrum ℝ (wordNativeMatrixLinearCombination A₀ A)) :
    ‖resolvent (wordNativeMatrixLinearCombination A₀ A) z‖ ≤
      (438*Real.exp 5)*
        (((wordMatrixVacuumExpectation (D := D) (ι := ι)
          ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*
            resolvent (wordNativeMatrixLinearCombination A₀ A) z)^(2*q))).re)^
              (1/(4*q : ℝ)) +
          Real.sqrt (specNorm (∑ k, A k^2))/((Fintype.card D : ℝ)^2*z.im^2)) := by
  cases isEmpty_or_nonempty D with
  | inl hD =>
    let : Subsingleton M := ⟨fun S T => by ext i; exact (hD.false i).elim⟩
    rw [spectrum.of_subsingleton] at hspec
    exact hspec.elim
  | inr hD =>
    let : Nonempty D := hD
    let d : ℝ := Fintype.card D
    let σ := Real.sqrt (specNorm (∑ k, A k^2))
    let X := wordNativeMatrixLinearCombination A₀ A
    let R := resolvent X z
    let lp : ℝ := ((wordMatrixVacuumExpectation (D := D) (ι := ι)
      ((star R*R)^(2*q))).re)^(1/(4*q : ℝ))
    let E : ℝ := σ/(d^2*z.im^2)
    let c : ℝ := 73*Real.exp 5
    have hd : 1≤d := by
      change 1≤(Fintype.card D : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := D)))
    have hdpos : 0<d := zero_lt_one.trans_le hd
    have hqR : 1≤(q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
    have hτ : 0≤(wordMatrixVacuumExpectation (D := D) (ι := ι) ((star R*R)^(2*q))).re :=
      (Complex.nonneg_iff.mp ((wordMatrixVacuumPositiveMap (D := D) (ι := ι)).map_nonneg
        (CStarAlgebra.pow_nonneg (star_mul_self_nonneg R) (2*q)))).1
    have hlp : 0≤lp := Real.rpow_nonneg hτ _
    have hE : 0≤E := by dsimp only [E,σ]; positivity
    have hc : 0<c := by dsimp only [c]; positivity
    have hc6 : 438*Real.exp 5=6*c := by dsimp only [c]; ring
    change ‖R‖≤(438*Real.exp 5)*(lp+E)
    rw [hc6]
    by_cases hησ : z.im≤σ
    · let r : ℕ := 36*(Fintype.card D)^4
      let K : ℝ := 6*d^2
      have hr : 0<r := by dsimp only [r]; positivity
      have hK : 4<K := by
        have hh : 1≤d^2 := one_le_pow₀ hd
        dsimp only [K]
        linarith only [hh]
      have hb := norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_mean_uniform
        q r hq hr hA₀ A hA hK hz hησ
      have hbase : (2*q*(r : ℝ)+1 : ℝ)=72*q*d^4+1 := by
        dsimp only [r,d]
        push_cast
        ring
      have herror : 18*σ/z.im^2*(K/(r : ℝ)+K⁻¹)=6*E := by
        dsimp only [K,r,E,d]
        push_cast
        field_simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := D)),hz.ne']
        ring
      change ‖R‖≤d^(3/(4*q : ℝ))*(2*q*(r : ℝ)+1)^(3/(4*q : ℝ))*
        (lp+18*σ/z.im^2*(K/(r : ℝ)+K⁻¹)) at hb
      rw [hbase,herror] at hb
      have hfactor : d^(3/(4*q : ℝ))*(72*q*d^4+1)^(3/(4*q : ℝ))≤c :=
        nativeResolventMomentFactor_le hd hqR hlog
      calc
        _ ≤ _ := hb
        _ ≤ c*(lp+6*E) := mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ ≤ _ := by nlinarith only [mul_nonneg hc.le hlp]
    · have hση : σ≤z.im := le_of_not_ge hησ
      have hb := norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_high
        q hq hA₀ A hA hz hση hspec
      have hdim : d^(1/(4*q : ℝ))≤Real.exp (1/4) := by
        rw [Real.rpow_def_of_pos hdpos]
        apply Real.exp_le_exp.mpr
        have hh : Real.log d/(4*q : ℝ)≤1/4 :=
          (div_le_iff₀ (show 0<(4*q : ℝ) by positivity)).mpr (by nlinarith only [hlog])
        simpa only [div_eq_mul_inv,one_mul] using hh
      have hdimc : 5*d^(1/(4*q : ℝ))≤c := by
        calc
          _ ≤ 5*Real.exp (1/4) := mul_le_mul_of_nonneg_left hdim (by norm_num)
          _ ≤ 5*Real.exp 5 := mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by norm_num)) (by norm_num)
          _ ≤ _ := by dsimp only [c]; nlinarith only [Real.exp_pos (5 : ℝ)]
      change ‖R‖≤5*d^(1/(4*q : ℝ))*lp at hb
      exact hb.trans ((mul_le_mul_of_nonneg_right hdimc hlp).trans
        (by nlinarith only [mul_nonneg hc.le hlp,mul_nonneg hc.le hE]))

end NLAlib

end
