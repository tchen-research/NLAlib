import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import NLAlib.ForMathlib.Analysis.Normed.Algebra.ResolventProjection

/-!
# Resolvent comparison after changing only the deterministic reference

The exact second-resolvent identity factors the actual endpoint difference
through the difference of the two deterministic resolvents. This allows
one-step mean clipping, without individual spectral projections or an
integration path.
-/

noncomputable section
set_option autoImplicit false

section Algebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- If the actual endpoint change is exactly the deterministic reference
change, the resolvent difference factors through the reference difference
with the two genuine perturbation correction factors. -/
theorem resolvent_sub_eq_reference_sub_factorization {a b d e : A} {z : R}
    (ha : z ∈ resolventSet R a) (hb : z ∈ resolventSet R b)
    (hd : z ∈ resolventSet R d) (he : z ∈ resolventSet R e)
    (hab : a-b=d-e) :
    resolvent a z-resolvent b z =
      (1+resolvent a z*(a-d)) * (resolvent d z-resolvent e z) *
        (1+(b-e)*resolvent b z) := by
  rw [spectrum.resolvent_sub_resolvent ha hb,hab]
  calc
    _ = ((1+resolvent a z*(a-d))*(resolvent d z*(d-e)))*resolvent b z := by
      rw [← resolvent_mul_eq_one_add_mul_resolvent_mul ha hd (d-e)]
    _ = (1+resolvent a z*(a-d))*
        ((resolvent d z*(d-e))*resolvent b z) := by rw [mul_assoc]
    _ = _ := by
      rw [mul_resolvent_eq_mul_resolvent_mul_one_add hb he (resolvent d z*(d-e)),
        ← spectrum.resolvent_sub_resolvent hd he]
      rw [mul_assoc]

end Algebra

section ScalarShift

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Shifting the element and spectral parameter by the same scalar leaves
the native total resolvent unchanged, including at nonunits. -/
theorem resolvent_sub_smul_one_sub_eq (a : A) (t z : R) :
    resolvent (a-t•(1 : A)) (z-t)=resolvent a z := by
  dsimp only [resolvent]
  congr 1
  simp only [map_sub,Algebra.algebraMap_eq_smul_one]
  abel

end ScalarShift

section Norm

variable {A : Type*} [CStarAlgebra A]

private theorem norm_one_compression_le : ‖(1 : A)‖ ≤ 1 := by
  have hh := CStarRing.norm_star_mul_self (x := (1 : A))
  simp only [star_one,one_mul] at hh
  nlinarith [norm_nonneg (1 : A)]

/-- A genuine supported reference-resolvent difference of size `1/(Kσ)`
controls the actual perturbed resolvents by `9σ/(Kη²)`, uniformly in the
size of the deterministic references. -/
theorem norm_resolvent_sub_le_of_reference_difference
    {a b d e : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hd : IsSelfAdjoint d) (he : IsSelfAdjoint e) {z : ℂ} (hz : 0<z.im)
    (hab : a-b=d-e) {σ K : ℝ} (hησ : z.im ≤ σ) (hK : 0<K)
    (hY₀ : ‖a-d‖ ≤ 2*σ) (hY₁ : ‖b-e‖ ≤ 2*σ)
    (hRef : ‖resolvent d z-resolvent e z‖ ≤ (K*σ)⁻¹) :
    ‖resolvent a z-resolvent b z‖ ≤ 9*σ/(K*z.im^2) := by
  have hσ : 0<σ := hz.trans_le hησ
  have hRa : ‖resolvent a z‖ ≤ z.im⁻¹ := by
    simpa only [abs_of_pos hz] using ha.norm_resolvent_le hz.ne'
  have hRb : ‖resolvent b z‖ ≤ z.im⁻¹ := by
    simpa only [abs_of_pos hz] using hb.norm_resolvent_le hz.ne'
  have hratio : 1 ≤ σ/z.im := (le_div_iff₀ hz).mpr (by simpa using hησ)
  have hscalar : 1+2*σ*z.im⁻¹ ≤ 3*σ/z.im := by
    rw [div_eq_mul_inv] at hratio ⊢
    nlinarith
  have hleft : ‖1+resolvent a z*(a-d)‖ ≤ 3*σ/z.im := by
    calc
      _ ≤ ‖(1 : A)‖+‖resolvent a z‖*‖a-d‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
      _ ≤ 1+z.im⁻¹*(2*σ) := add_le_add norm_one_compression_le
        (mul_le_mul hRa hY₀ (norm_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith [hscalar]
  have hright : ‖1+(b-e)*resolvent b z‖ ≤ 3*σ/z.im := by
    calc
      _ ≤ ‖(1 : A)‖+‖b-e‖*‖resolvent b z‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
      _ ≤ 1+(2*σ)*z.im⁻¹ := add_le_add norm_one_compression_le
        (mul_le_mul hY₁ hRb (norm_nonneg _) (by positivity))
      _ ≤ _ := hscalar
  rw [resolvent_sub_eq_reference_sub_factorization
    (ha.isUnit_algebraMap_sub_of_im_ne_zero hz.ne')
    (hb.isUnit_algebraMap_sub_of_im_ne_zero hz.ne')
    (hd.isUnit_algebraMap_sub_of_im_ne_zero hz.ne')
    (he.isUnit_algebraMap_sub_of_im_ne_zero hz.ne') hab]
  calc
    _ ≤ (‖1+resolvent a z*(a-d)‖ * ‖resolvent d z-resolvent e z‖) *
        ‖1+(b-e)*resolvent b z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((3*σ/z.im)*(K*σ)⁻¹)*(3*σ/z.im) := by
      gcongr
    _ = _ := by field_simp [hσ.ne',hK.ne',hz.ne']; ring

end Norm

end
