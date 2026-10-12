import NLAlib.Matrix.Spectral.ComplexVariationalPrinciple
import NLAlib.Matrix.Inequalities.TraceTail
/-!
# Native complex spectral trace tails

Loewner monotonicity of complex Hermitian eigenvalues, and the complex instance of the
trace-square energy bound for complex RPCholesky. The spectral tail itself and its
nonnegativity, trace and zero-tail rank bounds are stated once over `[RCLike 𝕜]` in
`NLAlib.Matrix.Inequalities.TraceTail`. Source: manuscript
`sa:rp-recursion`, `sa:rp-theorem`, and the complex audit Part VII.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Native complex Hermitian eigenvalues are monotone under PSD order.
Source: complex Courant--Fischer; supports manuscript `sa:rp-recursion`. -/
theorem complex_eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨S, hS, hAS⟩ := complex_exists_submodule_finrank_eq_eigenvalues₀_mul_le hA k
  refine complex_le_eigenvalues₀_of_forall_mem hB k S hS.ge fun x hx => (hAS x hx).trans ?_
  have h0 := h.re_dotProduct_nonneg (WithLp.ofLp x)
  have he : ∀ M : Matrix n n ℂ,
      (inner ℂ x (M.toEuclideanLin x)).re =
        (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)).re := by
    intro M
    change (inner ℂ (WithLp.toLp 2 (WithLp.ofLp x))
      (WithLp.toLp 2 (M *ᵥ WithLp.ofLp x))).re = _
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [he, he]
  change 0 ≤ (star x.ofLp ⬝ᵥ ((B - A) *ᵥ x.ofLp)).re at h0
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h0
  linarith

/-- A Loewner-bounded positive semidefinite residual has enough trace-square energy
to pay the exact relative trace drift (complex Hermitian case of
`sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le`). Source: manuscript
`sa:rp-recursion`; CETW (2025), eigenvalue monotonicity and Cauchy--Schwarz.
The sorted tail and zero trace cases are explicit. -/
theorem complex_sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq
    {A R : Matrix n n ℂ} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hAR : (A - R).PosSemidef) (r : ℕ) :
    (max (R.trace.re - spectralTraceTail A hA.isHermitian r) 0) ^ 2 ≤
      (r : ℝ) * (R * R).trace.re :=
  sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le hA hR
    (complex_eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hR.isHermitian hA.isHermitian hAR) r

end NLAlib
