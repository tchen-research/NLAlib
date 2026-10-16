import NLAlib.Matrix.Functions.MonotoneConcavity
import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Operator-monotone modulus of continuity

Scalar concavity gives scalar subadditivity. Comparing each matrix with
the other plus its norm distance then proves the sharp modulus, without
asserting subadditivity on unrelated matrices. Toolkit formula (F1).
-/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

/-- Concavity on the nonnegative half-line and a zero boundary value
imply scalar subadditivity. -/
theorem _root_.ConcaveOn.apply_add_le_of_nonneg {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Ici 0) f) (hf0 : f 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : f (x+y) ≤ f x + f y := by
  by_cases hsum : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simp [hx0, hy0, hf0]
  have hs : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hsum)
  have hab : x/(x+y)+y/(x+y)=1 := by rw [← add_div, div_self hsum]
  have heq₁ : (x/(x+y)) • (x+y) + (y/(x+y)) • (0 : ℝ) = x := by simp [smul_eq_mul, div_mul_cancel₀ _ hsum]
  have heq₂ : (y/(x+y)) • (x+y) + (x/(x+y)) • (0 : ℝ) = y := by simp [smul_eq_mul, div_mul_cancel₀ _ hsum]
  have h₁ := hf.2 hs.le (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (div_nonneg hx hs.le) (div_nonneg hy hs.le) hab
  have h₂ := hf.2 hs.le (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (div_nonneg hy hs.le) (div_nonneg hx hs.le) (by linarith : y/(x+y)+x/(x+y)=1)
  rw [heq₁, hf0, smul_zero, add_zero] at h₁
  rw [heq₂, hf0, smul_zero, add_zero] at h₂
  have h := add_le_add h₁ h₂
  simpa only [smul_eq_mul, ← add_mul, hab, one_mul] using h

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private local instance : NormedAlgebra ℝ (Matrix n n 𝕜) := normedAlgebraRealMatrix

/-- A Hermitian matrix is below its norm times the identity over both
real and complex fields, including empty dimensions. -/
theorem le_algebraMap_norm_of_isHermitian {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    H ≤ algebraMap ℝ (Matrix n n 𝕜) ‖H‖ := by
  cases isEmpty_or_nonempty n with
  | inl he => exact (Subsingleton.elim H (algebraMap ℝ (Matrix n n 𝕜) ‖H‖)).le
  | inr hn =>
    apply (le_algebraMap_iff_spectrum_le hH).mpr
    intro x hx
    exact (le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx)

/-- Hermitian norm/order equivalence, with both scalar bounds supplied. -/
theorem norm_le_of_isHermitian_of_order_bounds {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c)
    (hl : algebraMap ℝ (Matrix n n 𝕜) (-c) ≤ H)
    (hu : H ≤ algebraMap ℝ (Matrix n n 𝕜) c) : ‖H‖ ≤ c := by
  have hn : ‖cfc (fun x : ℝ => x) H‖ ≤ c := by
    apply norm_cfc_le hc
    intro x hx
    exact abs_le.mpr ⟨(algebraMap_le_iff_le_spectrum hH).mp hl x hx,
      (le_algebraMap_iff_spectrum_le hH).mp hu x hx⟩
  calc
    ‖H‖ = ‖cfc (fun x : ℝ => x) H‖ := by congr 1; exact (cfc_id' ℝ H hH).symm
    _ ≤ c := hn

private theorem norm_cfc_sub_le_of_monotone_concave {f : ℝ → ℝ}
    (hc : ConcaveOn ℝ (Ici 0) f) (hf0 : f 0=0) (hfn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hm : ∀ A B : Matrix n n 𝕜, A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖cfc f A - cfc f B‖ ≤ f ‖A-B‖ := by
  have hup (A B : Matrix n n 𝕜) (hA : A.PosSemidef) (hB : B.PosSemidef) :
      cfc f A ≤ cfc f B + algebraMap ℝ (Matrix n n 𝕜) (f ‖A-B‖) := by
    let t := ‖A-B‖
    have hfin (q : ℝ → ℝ) : ContinuousOn q (spectrum ℝ B) := B.finite_real_spectrum.continuousOn q
    have ht : 0 ≤ t := norm_nonneg _
    have hBt : (B + algebraMap ℝ (Matrix n n 𝕜) t).PosSemidef :=
      hB.add ((show (0 : Matrix n n 𝕜) ≤ algebraMap ℝ (Matrix n n 𝕜) t from
        by simpa only [Algebra.algebraMap_eq_smul_one] using
          (show (0 : Matrix n n 𝕜) ≤ t • 1 from smul_nonneg ht zero_le_one)).posSemidef)
    have hcmp : A ≤ B + algebraMap ℝ (Matrix n n 𝕜) t := by
      have h := le_algebraMap_norm_of_isHermitian (hA.isHermitian.sub hB.isHermitian)
      exact (sub_le_iff_le_add').mp h
    have hshift : cfc f (B + algebraMap ℝ (Matrix n n 𝕜) t) = cfc (fun x => f (x+t)) B := by
      have hi : cfc (fun x : ℝ => x+t) B = B + algebraMap ℝ (Matrix n n 𝕜) t := by
        calc
          _ = cfc (fun x : ℝ => x) B + algebraMap ℝ (Matrix n n 𝕜) t :=
            cfc_add_const t _ B (hfin _) hB.isHermitian
          _ = _ := by congr 1; exact cfc_id' ℝ B hB.isHermitian
      calc
        _ = cfc f (cfc (fun x : ℝ => x+t) B) := congrArg (cfc f) hi.symm
        _ = _ := (cfc_comp f (fun x : ℝ => x+t) B hB.isHermitian
          ((B.finite_real_spectrum.image _).continuousOn _) (hfin _)).symm
    have hscalar : cfc (fun x => f (x+t)) B ≤ cfc f B + algebraMap ℝ (Matrix n n 𝕜) (f t) := by
      calc
        _ ≤ cfc (fun x => f x + f t) B := by
          apply cfc_mono (hf := hfin _) (hg := hfin _)
          intro x hx
          exact hc.apply_add_le_of_nonneg hf0 (spectrum_nonneg_of_nonneg hB.nonneg hx) ht
        _ = _ := cfc_add_const (f t) f B (hfin _) hB.isHermitian
    exact (hm A _ hA hBt hcmp).trans (hshift ▸ hscalar)
  apply norm_le_of_isHermitian_of_order_bounds
    ((show (cfc f A).IsHermitian from cfc_predicate _ _).sub (cfc_predicate _ _))
    (hfn _ (norm_nonneg _))
  · have h := hup B A hB hA
    rw [norm_sub_rev B A] at h
    rw [map_neg]
    exact (neg_le_sub_iff_le_add).mpr h
  · exact (sub_le_iff_le_add').mpr (hup A B hA hB)

/-- The sharp operator-monotone modulus for complex PSD matrices.
The scalar assumptions hold only on the nonnegative half-line.
atlas: operator-monotone-modulus-continuity (partial) -/
theorem specNorm_cfc_sub_le_of_operatorMonotoneOn_nonneg {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) (hf : ContinuousOn f (Ici 0))
    (hf0 : f 0=0) (hfn : ∀ t, 0 ≤ t → 0 ≤ f t)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    specNorm (cfc f A-cfc f B) ≤ f (specNorm (A-B)) := by
  change ‖cfc f A-cfc f B‖ ≤ f ‖A-B‖
  have hmono (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
      (hAB : A ≤ B) : cfc f A ≤ cfc f B := by
    apply hm.cfc_le hA.isHermitian hB.isHermitian _ _ hAB
    · exact fun _ hx => spectrum_nonneg_of_nonneg hA.nonneg hx
    · exact fun _ hx => spectrum_nonneg_of_nonneg hB.nonneg hx
  convert! norm_cfc_sub_le_of_monotone_concave (𝕜 := ℂ) (hm.concaveOn_nonneg hf) hf0 hfn
    hmono hA hB using 1

/-- The same sharp modulus for real PSD matrices, transported through
the library's canonical real matrix embedding.
atlas: operator-monotone-modulus-continuity (partial) -/
theorem specNorm_cfc_sub_le_of_operatorMonotoneOn_nonneg_real {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) (hf : ContinuousOn f (Ici 0))
    (hf0 : f 0=0) (hfn : ∀ t, 0 ≤ t → 0 ≤ f t)
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    specNorm (cfc f A-cfc f B) ≤ f (specNorm (A-B)) := by
  simp only [specNorm_eq_norm]
  apply norm_cfc_sub_le_of_monotone_concave (hm.concaveOn_nonneg hf) hf0 hfn ?_ hA hB
  intro A B hA hB hAB
  apply (realMatrixComplexification_le_iff (𝕜 := ℂ) _ _).mp
  rw [realMatrixComplexification_cfc f hA.isHermitian,
    realMatrixComplexification_cfc f hB.isHermitian]
  have hAc := (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) A).mpr hA
  have hBc := (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) B).mpr hB
  exact hm.cfc_le hAc.isHermitian hBc.isHermitian
    (fun _ hx => spectrum_nonneg_of_nonneg hAc.nonneg hx)
    (fun _ hx => spectrum_nonneg_of_nonneg hBc.nonneg hx)
    ((realMatrixComplexification_le_iff A B).mpr hAB)

end NLAlib
