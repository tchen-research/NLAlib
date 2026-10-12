import NLAlib.Matrix.Spectral.SVD
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A real invariant line or conjugate-eigenvalue plane

Real and imaginary parts of a complex eigenvector give either a real
eigenline or an independent real invariant two-plane. This is the common
deflation step for real Schur, real normal form, and real QZ.
-/

noncomputable section
open Module
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Real and imaginary parts of a nonreal eigenvector are real linearly
independent. The two displayed real equations are exactly the real and
imaginary parts of its eigenvalue equation. Horn–Johnson 2013,
Theorems 2.3.1 and 2.5.4; real invariant-plane helper. -/
theorem linearIndependent_real_imag_of_nonreal_eigen_equations {n : Type*}
    [Fintype n] (A : Matrix n n ℝ) (a b : ℝ) (hb : b ≠ 0)
    (u v : n → ℝ) (huv : u ≠ 0 ∨ v ≠ 0)
    (hAu : A *ᵥ u = a • u - b • v) (hAv : A *ᵥ v = b • u + a • v) :
    LinearIndependent ℝ ![u, v] := by
  have hv : v ≠ 0 := by
    intro hv
    have hu : u = 0 := by
      have hh : b • u = 0 := by simpa only [hv, Matrix.mulVec_zero, smul_zero, add_zero] using hAv.symm
      exact (smul_eq_zero.mp hh).resolve_left hb
    exact huv.elim (fun h => h hu) (fun h => h hv)
  rw [linearIndependent_fin2]
  refine ⟨hv, ?_⟩
  intro c hc
  change c • v = u at hc
  have hh := congrArg (fun x : n → ℝ => A *ᵥ x) hc
  rw [Matrix.mulVec_smul, hAv, hAu, ← hc] at hh
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have he := congrFun hh i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at he
  have hz : b * (c ^ 2 + 1) * v i = 0 := by nlinarith [he]
  have hbp : b * (c ^ 2 + 1) ≠ 0 := mul_ne_zero hb (by positivity)
  exact (mul_ne_zero hbp hi) hz

/-- Every nonempty real square matrix has a real eigenline or an independent
real invariant two-plane carrying a nonreal conjugate pair. The two-plane
coordinates here need not be orthonormal; later orthonormalization produces
the general real Schur block. Horn–Johnson 2013, Theorem 2.3.1;
derivations §gen:schur. -/
theorem exists_real_eigenvector_or_invariant_plane {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] (A : Matrix n n ℝ) :
    (∃ a : ℝ, ∃ u : n → ℝ, u ≠ 0 ∧ A *ᵥ u = a • u) ∨
    (∃ a b : ℝ, b ≠ 0 ∧ ∃ X : Matrix n (Fin 2) ℝ,
      LinearIndependent ℝ X.col ∧ A * X = X * !![a, b; -b, a]) := by
  let AC := A.map Complex.ofReal
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue AC.mulVecLin
  obtain ⟨z, hz, hz0⟩ := hμ.exists_hasEigenvector
  have hAz : AC *ᵥ z = μ • z := Module.End.mem_eigenspace_iff.mp hz
  let u : n → ℝ := fun i => (z i).re
  let v : n → ℝ := fun i => (z i).im
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    funext i
    apply Complex.ext
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hAu : A *ᵥ u = μ.re • u - μ.im • v := by
    funext i
    have hh := congrArg Complex.re (congrFun hAz i)
    simpa only [AC, u, v, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hh
  have hAv : A *ᵥ v = μ.im • u + μ.re • v := by
    funext i
    have hh := congrArg Complex.im (congrFun hAz i)
    simpa only [AC, u, v, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul, add_comm] using hh
  by_cases hμi : μ.im = 0
  · left
    rcases huv with hu | hv
    · exact ⟨μ.re, u, hu, by simpa only [hμi, zero_smul, sub_zero] using hAu⟩
    · exact ⟨μ.re, v, hv, by simpa only [hμi, zero_smul, zero_add] using hAv⟩
  · right
    let X : Matrix n (Fin 2) ℝ := Matrix.of (fun i => ![u i, v i])
    refine ⟨μ.re, μ.im, hμi, X, ?_, ?_⟩
    · have hcol : X.col = ![u, v] := by funext j; fin_cases j <;> rfl
      rw [hcol]
      exact linearIndependent_real_imag_of_nonreal_eigen_equations A μ.re μ.im hμi u v huv hAu hAv
    · ext i j
      fin_cases j
      · have hh := congrFun hAu i
        simpa [X, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          mul_comm, sub_eq_add_neg] using hh
      · have hh := congrFun hAv i
        simpa [X, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using hh

end NLAlib
