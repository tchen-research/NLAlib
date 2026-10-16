import NLAlib.Matrix.Basic.PSDDuality
import NLAlib.Matrix.Norms.Frobenius
import NLAlib.Matrix.Functions.CFCTrace

/-!
# Rayleigh domination for maps preserving the PSD cone

Positive and negative spectral parts turn a Hermitian test matrix into
a positive test matrix of the same Frobenius norm. This concerns cone
positivity, which does not imply positivity of a Hilbert quadratic form.
Source: matrix_toolkit_open_routes_2026_10_15, F22.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- PSD matrices have nonnegative real Frobenius pairing. -/
theorem frobInner_nonneg_of_posSemidef {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ frobInner P Q := by
  rw [frobInner_eq_trace, hP.isHermitian.eq]
  exact Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hP hQ) |>.1

/-- Every Hermitian matrix splits as two orthogonal positive spectral
parts. Their sum and difference have the same Frobenius norm. -/
theorem exists_posSemidef_parts {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ P N : Matrix n n ℂ, P.PosSemidef ∧ N.PosSemidef ∧
      H=P-N ∧ frobInner P N=0 ∧ frobSq (P+N)=frobSq H := by
  let f : ℝ → ℝ := fun x => max x 0
  let g : ℝ → ℝ := fun x => max (-x) 0
  have hf : Continuous f := continuous_id.max continuous_const
  have hg : Continuous g := continuous_neg.max continuous_const
  let P := cfc f H
  let N := cfc g H
  have hP : P.PosSemidef := posSemidef_cfc_of_nonneg_eigenvalues hH (fun i => le_max_right _ _)
  have hN : N.PosSemidef := posSemidef_cfc_of_nonneg_eigenvalues hH (fun i => le_max_right _ _)
  have hfg (x : ℝ) : f x-g x=x := by
    dsimp [f,g]
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith : 0 ≤ -x)]; ring
  have hfg0 (x : ℝ) : f x*g x=0 := by
    dsimp [f,g]
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (neg_nonpos.mpr hx), mul_zero]
    · rw [max_eq_right (le_of_not_ge hx), zero_mul]
  have hdiff : P-N=H := by
    calc
      _ = cfc (fun x => f x-g x) H := (cfc_sub f g H hf.continuousOn hg.continuousOn).symm
      _ = cfc (fun x : ℝ => x) H := cfc_congr (fun x _ => hfg x)
      _ = H := cfc_id ℝ H hH
  have hPN : P*N=0 := by
    calc
      _ = cfc (fun x => f x*g x) H := (cfc_mul f g H hf.continuousOn hg.continuousOn).symm
      _ = cfc (fun _ : ℝ => 0) H := cfc_congr (fun x _ => hfg0 x)
      _ = 0 := cfc_zero ℝ H
  have hi : frobInner P N=0 := by
    rw [frobInner_eq_trace, hP.isHermitian.eq, hPN, Matrix.trace_zero, map_zero]
  refine ⟨P,N,hP,hN,hdiff.symm,hi,?_⟩
  rw [← hdiff, frobSq_add, frobSq_sub, hi]
  ring

/-- A cone-positive real-linear map has a PSD Rayleigh majorant for
every Hermitian test, with exactly the same Frobenius norm. -/
theorem exists_posSemidef_rayleigh_majorant
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hL : ∀ P : Matrix n n ℂ, P.PosSemidef → (L P).PosSemidef)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ K : Matrix n n ℂ, K.PosSemidef ∧ frobSq K=frobSq H ∧
      |frobInner H (L H)| ≤ frobInner K (L K) := by
  obtain ⟨P,N,hP,hN,hH,hi,hnorm⟩ := exists_posSemidef_parts hH
  refine ⟨P+N,hP.add hN,hnorm,?_⟩
  rw [hH, map_sub, map_add]
  simp only [frobInner_add_left, frobInner_add_right, frobInner_sub_left, frobInner_sub_right]
  have hPP := frobInner_nonneg_of_posSemidef hP (hL P hP)
  have hPN := frobInner_nonneg_of_posSemidef hP (hL N hN)
  have hNP := frobInner_nonneg_of_posSemidef hN (hL P hP)
  have hNN := frobInner_nonneg_of_posSemidef hN (hL N hN)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end NLAlib
