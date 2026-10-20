import NLAlib.Probability.Free.WordMatrixTracialMoments
import NLAlib.Probability.Free.WordMatrixResolventMoments
import NLAlib.ForMathlib.Analysis.CStarAlgebra.FunctionalCalculusClamp
import NLAlib.ForMathlib.Analysis.CStarAlgebra.ResolventMeanCompression

/-!
# Mean-uniform actual matrix-word resolvent moments

The deterministic mean is clipped by its actual native functional calculus.
Naturality preserves its constant-coefficient character, and the genuine
closed-algebra vacuum Gram estimate transports the perturbed moments.
Source: arXiv:2406.11453v2, Theorem 4.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder ContinuousFunctionalCalculus

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

private theorem realMeanResolventCFC (A : Type*) [CStarAlgebra A] :
    IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)

attribute [local instance] realMeanResolventCFC

omit [Fintype ι] in
/-- Scalar coefficients embedded by the actual native matrix star-hom are
constant Wick polynomials, with no change of the native amplified norm. -/
theorem scalar_coefficient_mem_wordWickDegreeSpan
    (D₀ : CStarMatrix D D ℂ) (k : ℕ) (i j : D) :
    CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀ i j ∈
      wordWickDegreeSpan (ι := ι) k := by
  have h1 : (1 : B) ∈ wordWickDegreeSpan (ι := ι) k := by
    simpa only [wordWickOperator] using
      wordWickOperator_mem_wordWickDegreeSpan ([] : List ι) (Nat.zero_le k)
  change (algebraMap ℂ B (D₀ i j)) ∈ wordWickDegreeSpan (ι := ι) k
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ h1

set_option maxHeartbeats 800000 in
/-- At imaginary height the actual native free-polynomial resolvent has a
rooted vacuum-moment bound independent of the norm of its deterministic
scalar matrix mean. The one-step clipping proof gives a sharper error than
the dimension-loss form in source Theorem 4.3.

Source: arXiv:2406.11453v2, Theorem 4.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow_mean_uniform_of_re_eq_zero
    (q r : ℕ) (hq : 0<q) (hr : 0<r)
    (D₀ : CStarMatrix D D ℂ) (hD : IsSelfAdjoint D₀)
    (Y : M) (hY : IsSelfAdjoint Y)
    (hdeg : ∀ i j, Y i j ∈ wordWickDegreeSpan (ι := ι) 1)
    {σ K : ℝ} (hK : 4<K) (hnorm : ‖Y‖≤2*σ)
    {z : ℂ} (hre : z.re=0) (hz : 0<z.im) (hησ : z.im≤σ) :
    ‖resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z‖ ≤
      (Fintype.card D : ℝ) ^ (3 / (4*q : ℝ)) *
        (2*q*r+1 : ℝ) ^ (3 / (4*q : ℝ)) *
          (((wordMatrixVacuumExpectation (D := D) (ι := ι)
            ((star (resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z) *
              resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z) ^
                (2*q))).re) ^ (1 / (4*q : ℝ)) +
            18*σ/z.im^2*(K/(r : ℝ)+K⁻¹)) := by
  cases isEmpty_or_nonempty D with
  | inl hDempty =>
    have hzero : resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z=0 :=
      by ext i; exact (hDempty.false i).elim
    have hcard : Fintype.card D=0 := Fintype.card_eq_zero_iff.mpr hDempty
    have he : (3 : ℝ)/(4*q)≠0 := by
      have hqR : 0<(q : ℝ) := Nat.cast_pos.mpr hq
      positivity
    simp only [hzero,norm_zero,hcard,Nat.cast_zero,Real.zero_rpow he,zero_mul,le_refl]
  | inr hDnonempty =>
    let : Nonempty D := hDnonempty
    let C := CStarMatrix.mapStarAlgHom (D := D) (StarAlgHom.ofId ℂ B)
    let d : M := C D₀
    let e : M := cfcSymmetricClamp (K*σ) d
    let X : M := d+Y
    let Z : M := e+Y
    let c : ℝ := (Fintype.card D : ℝ) ^ (3/(4*q : ℝ)) *
      (2*q*r+1 : ℝ) ^ (3/(4*q : ℝ))
    let δ : ℝ := 9*σ/(K*z.im^2)
    let lp : M → ℝ := fun R =>
      ((wordMatrixVacuumExpectation (D := D) (ι := ι) ((star R*R)^(2*q))).re) ^
        (1/(4*q : ℝ))
    have hσ : 0<σ := hz.trans_le hησ
    have hKpos : 0<K := by linarith only [hK]
    have hrR : 0<(r : ℝ) := Nat.cast_pos.mpr hr
    have hc1 : 1≤c := by
      apply one_le_mul_of_one_le_of_one_le
      · exact Real.one_le_rpow
          (by exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := D))))
          (by positivity)
      · exact Real.one_le_rpow (by
            have hp : 0≤(2 : ℝ)*q*r := by positivity
            linarith only [hp])
          (by positivity)
    have hc : 0≤c := le_trans (by norm_num) hc1
    have hδ : 0≤δ := by dsimp only [δ]; positivity
    have hd : IsSelfAdjoint d := hD.map C
    have he : IsSelfAdjoint e := isSelfAdjoint_cfcSymmetricClamp _ _
    have hX : IsSelfAdjoint X := hd.add hY
    have hZ : IsSelfAdjoint Z := he.add hY
    have heq : e=C (cfcSymmetricClamp (K*σ) D₀) := by
      exact (C.map_cfc (fun x : ℝ => max (-(K*σ)) (min (K*σ) x)) D₀
        (by fun_prop) (by fun_prop) hD hd).symm
    have hdegX : ∀ i j, X i j ∈ wordWickDegreeSpan (ι := ι) 1 := by
      intro i j
      exact Submodule.add_mem _ (scalar_coefficient_mem_wordWickDegreeSpan D₀ 1 i j)
        (hdeg i j)
    have hdegZ : ∀ i j, Z i j ∈ wordWickDegreeSpan (ι := ι) 1 := by
      intro i j
      change e i j+Y i j ∈ _
      rw [heq]
      exact Submodule.add_mem _
        (scalar_coefficient_mem_wordWickDegreeSpan (cfcSymmetricClamp (K*σ) D₀) 1 i j)
        (hdeg i j)
    have hRef : ‖resolvent d z-resolvent e z‖≤(K*σ)⁻¹ :=
      hd.norm_resolvent_sub_cfcSymmetricClamp_le hre hz (mul_pos hKpos hσ)
    have hdiff : ‖resolvent X z-resolvent Z z‖≤δ := by
      exact norm_resolvent_sub_le_of_reference_difference hX hZ hd he hz
        (by dsimp only [X,Z]; noncomm_ring) hησ hKpos
        (by simpa only [X,add_sub_cancel_left] using hnorm)
        (by simpa only [Z,add_sub_cancel_left] using hnorm) hRef
    have hmemX : resolvent X z ∈ wordMatrixFieldAlgebra (D := D) (ι := ι) := by
      rw [hX.resolvent_eq_cfc_of_im_ne_zero hz.ne']
      exact cfc_mem_wordMatrixFieldAlgebra _ (mem_wordMatrixFieldAlgebra_of_entries_degree hdegX)
    have hmemZ : resolvent Z z ∈ wordMatrixFieldAlgebra (D := D) (ι := ι) := by
      rw [hZ.resolvent_eq_cfc_of_im_ne_zero hz.ne']
      exact cfc_mem_wordMatrixFieldAlgebra _ (mem_wordMatrixFieldAlgebra_of_entries_degree hdegZ)
    have hLp : lp (resolvent Z z)≤lp (resolvent X z)+δ := by
      have hm := (abs_wordMatrixVacuum_gramMoment_rpow_sub_le_norm
        (resolvent Z z) (resolvent X z) hmemZ hmemX (2*q) (by omega)).trans
          (by simpa only [norm_sub_rev] using hdiff)
      have he : ((2 : ℝ)*(2*q : ℕ))⁻¹=1/(4*q : ℝ) := by push_cast; ring
      simp only [he] at hm
      have hh : lp (resolvent Z z)-lp (resolvent X z)≤δ := (le_abs_self _).trans hm
      linarith only [hh]
    have hZnorm : ‖Z‖≤(K+2)*σ := by
      calc
        _ ≤ ‖e‖+‖Y‖ := norm_add_le _ _
        _ ≤ K*σ+2*σ := add_le_add
          (norm_cfcSymmetricClamp_le _ (mul_pos hKpos hσ).le d) hnorm
        _ = _ := by ring
    have hnonuniform : ‖resolvent Z z‖≤
        c*(lp (resolvent Z z)+12*‖Z‖/((r : ℝ)*z.im^2)) := by
      simpa only [Nat.cast_one,mul_one] using
        norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow 1 q r hq hr Z hZ hdegZ hz
    have herror : 2*δ+12*((K+2)*σ)/((r : ℝ)*z.im^2) ≤
        18*σ/z.im^2*(K/(r : ℝ)+K⁻¹) := by
      have hlinear : 12*(K+2)≤18*K := by linarith only [hK]
      calc
        _ ≤ 2*δ+18*K*σ/((r : ℝ)*z.im^2) := by
          apply add_le_add le_rfl
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith only [mul_le_mul_of_nonneg_right hlinear hσ.le]
        _ = _ := by dsimp only [δ]; field_simp [hKpos.ne',hz.ne',hrR.ne']; ring
    change ‖resolvent X z‖≤c*(lp (resolvent X z)+_)
    calc
      _ ≤ ‖resolvent Z z‖+δ := by
        calc
          _ = ‖resolvent Z z+(resolvent X z-resolvent Z z)‖ := by
            congr 1
            abel
          _ ≤ ‖resolvent Z z‖+‖resolvent X z-resolvent Z z‖ := norm_add_le _ _
          _ ≤ _ := add_le_add le_rfl hdiff
      _ ≤ c*(lp (resolvent Z z)+12*‖Z‖/((r : ℝ)*z.im^2))+δ :=
        add_le_add hnonuniform le_rfl
      _ ≤ c*(lp (resolvent X z)+δ+12*((K+2)*σ)/((r : ℝ)*z.im^2))+δ := by
        gcongr
      _ ≤ c*(lp (resolvent X z)+(2*δ+12*((K+2)*σ)/((r : ℝ)*z.im^2))) := by
        nlinarith only [mul_le_mul_of_nonneg_right hc1 hδ]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hc

set_option maxHeartbeats 800000 in
/-- The actual native free-polynomial resolvent has a rooted amplified
vacuum-moment estimate uniform in its full deterministic mean, at every
upper-half-plane parameter of height at most the free-series scale.

Source: arXiv:2406.11453v2, Theorem 4.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow_mean_uniform
    (q r : ℕ) (hq : 0<q) (hr : 0<r)
    (D₀ : CStarMatrix D D ℂ) (hD : IsSelfAdjoint D₀)
    (Y : M) (hY : IsSelfAdjoint Y)
    (hdeg : ∀ i j, Y i j ∈ wordWickDegreeSpan (ι := ι) 1)
    {σ K : ℝ} (hK : 4<K) (hnorm : ‖Y‖≤2*σ)
    {z : ℂ} (hz : 0<z.im) (hησ : z.im≤σ) :
    ‖resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z‖ ≤
      (Fintype.card D : ℝ) ^ (3 / (4*q : ℝ)) *
        (2*q*r+1 : ℝ) ^ (3 / (4*q : ℝ)) *
          (((wordMatrixVacuumExpectation (D := D) (ι := ι)
            ((star (resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z) *
              resolvent (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) D₀+Y) z) ^
                (2*q))).re) ^ (1 / (4*q : ℝ)) +
            18*σ/z.im^2*(K/(r : ℝ)+K⁻¹)) := by
  let C := CStarMatrix.mapStarAlgHom (D := D) (StarAlgHom.ofId ℂ B)
  let D₁ : CStarMatrix D D ℂ := D₀-(z.re : ℂ)•1
  let ζ : ℂ := z-(z.re : ℂ)
  have hscalar : IsSelfAdjoint ((z.re : ℂ)•(1 : CStarMatrix D D ℂ)) := by
    change star ((z.re : ℂ)•(1 : CStarMatrix D D ℂ))=_
    simp only [star_smul,star_one,Complex.star_def,Complex.conj_ofReal]
  have hD₁ : IsSelfAdjoint D₁ := hD.sub hscalar
  have hre : ζ.re=0 := by simp only [ζ,Complex.sub_re,Complex.ofReal_re,sub_self]
  have him : ζ.im=z.im := by simp only [ζ,Complex.sub_im,Complex.ofReal_im,sub_zero]
  have hR : resolvent (C D₁+Y) ζ=resolvent (C D₀+Y) z := by
    dsimp only [D₁,ζ]
    rw [map_sub,map_smul,map_one]
    have he : C D₀-(z.re : ℂ)•1+Y=(C D₀+Y)-(z.re : ℂ)•1 := by abel
    rw [he]
    exact resolvent_sub_smul_one_sub_eq _ _ _
  have hb := norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow_mean_uniform_of_re_eq_zero
    q r hq hr D₁ hD₁ Y hY hdeg hK hnorm hre (by rwa [him]) (by rwa [him])
  change ‖resolvent (C D₀+Y) z‖≤_
  rw [hR,him] at hb
  exact hb

end NLAlib

end
