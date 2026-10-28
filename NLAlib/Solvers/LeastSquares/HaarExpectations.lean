import NLAlib.Solvers.LeastSquares.HaarFrameConsumer
import NLAlib.RandomMatrix.Haar.TopGramMoments

/-!
# Exact native real and complex Haar sketch-and-solve expectations

The actual compact-group Haar law, its exact inverse top-Gram mean and native
Moore--Penrose frame decomposition give the finite-dimensional correction.
Source: Epperly--Webber (2026), Theorem 2.1 and Section 5.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Exact integrable real Haar estimator mean, at arbitrary matrix rank.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_haar_real {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) :
    Integrable (fun Ω => sketchAndSolve A Ω.valᴴ B) (unitaryHaarFrameLaw ℝ n ell helln) ∧
      (∫ Ω,sketchAndSolve A Ω.valᴴ B ∂unitaryHaarFrameLaw ℝ n ell helln)=moorePenroseInverse A*B := by
  obtain ⟨U,hU,hUA,_⟩ := exists_orthonormal_range_frame A
  obtain ⟨V,hV,hUV,hcomp⟩ := exists_unitary_complement_orthogonal U hU
  exact integrable_and_integral_sketchAndSolve_haar_of_frame A B U V hU hV hUV hcomp hUA rfl helln
    (ae_isUnit_topGram_haar_real (by omega) helln U hU)
    (integrable_and_integral_re_trace_inv_topGram_haar_real hs helln U hU).1

open scoped Matrix.Norms.L2Operator in
/-- Exact integrable complex Haar estimator mean, including nonreal data.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_haar_complex {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) :
    Integrable (fun Ω => sketchAndSolve A Ω.valᴴ B) (unitaryHaarFrameLaw ℂ n ell helln) ∧
      (∫ Ω,sketchAndSolve A Ω.valᴴ B ∂unitaryHaarFrameLaw ℂ n ell helln)=moorePenroseInverse A*B := by
  obtain ⟨U,hU,hUA,_⟩ := exists_orthonormal_range_frame A
  obtain ⟨V,hV,hUV,hcomp⟩ := exists_unitary_complement_orthogonal U hU
  exact integrable_and_integral_sketchAndSolve_haar_of_frame A B U V hU hV hUV hcomp hUA rfl helln
    (ae_isUnit_topGram_haar_complex (by omega) helln U hU)
    (integrable_and_integral_re_trace_inv_topGram_haar_complex hs helln U hU).1

/-- Exact integrable real Haar residual moment with its finite-dimension correction.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_real {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) :
    Integrable (fun Ω => frobSq (B-A*sketchAndSolve A Ω.valᴴ B)) (unitaryHaarFrameLaw ℝ n ell helln) ∧
      (∫ Ω,frobSq (B-A*sketchAndSolve A Ω.valᴴ B) ∂unitaryHaarFrameLaw ℝ n ell helln)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank-1)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨U,hU,hUA,_⟩ := exists_orthonormal_range_frame A
  obtain ⟨V,hV,hUV,hcomp⟩ := exists_unitary_complement_orthogonal U hU
  obtain ⟨htrace,hvalue⟩ := integrable_and_integral_re_trace_inv_topGram_haar_real hs helln U hU
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_of_frame
    A B U V hU hV hUV hcomp hUA rfl helln (by simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (show A.rank<n by omega))
    (ae_isUnit_topGram_haar_real (by omega) helln U hU) htrace
  refine ⟨hi,hv.trans ?_⟩
  rw [hvalue]
  simp only [Fintype.card_fin]
  rw [Nat.cast_sub (show A.rank≤n by omega)]
  ring

/-- Exact integrable complex Haar residual moment with denominator `ell-r`.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_complex {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) :
    Integrable (fun Ω => frobSq (B-A*sketchAndSolve A Ω.valᴴ B)) (unitaryHaarFrameLaw ℂ n ell helln) ∧
      (∫ Ω,frobSq (B-A*sketchAndSolve A Ω.valᴴ B) ∂unitaryHaarFrameLaw ℂ n ell helln)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨U,hU,hUA,_⟩ := exists_orthonormal_range_frame A
  obtain ⟨V,hV,hUV,hcomp⟩ := exists_unitary_complement_orthogonal U hU
  obtain ⟨htrace,hvalue⟩ := integrable_and_integral_re_trace_inv_topGram_haar_complex hs helln U hU
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_of_frame
    A B U V hU hV hUV hcomp hUA rfl helln (by simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (show A.rank<n by omega))
    (ae_isUnit_topGram_haar_complex (by omega) helln U hU) htrace
  refine ⟨hi,hv.trans ?_⟩
  rw [hvalue]
  simp only [Fintype.card_fin]
  rw [Nat.cast_sub (show A.rank≤n by omega)]
  ring

end NLAlib
