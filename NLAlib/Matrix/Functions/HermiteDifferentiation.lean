import NLAlib.Matrix.Functions.CFCFlatRemainder
import NLAlib.ForMathlib.Analysis.PolynomialDifferential
import NLAlib.Polynomial.Interpolation.Hermite

/-!
# Finite Hermite reduction of matrix differentiation

An explicit double-node Hermite polynomial transfers its derivative to
the original scalar function at one Hermitian matrix. Repeated matrix
eigenvalues are reduced to a finite set of distinct scalar nodes.
Tropp (2022), Theorem 14.13; toolkit derivations, formulas (F6)--(F9).
-/

noncomputable section
open Matrix Polynomial Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A scalar function differentiable at every eigenvalue has, along the
Hermitian matrices, the derivative of a polynomial matching its values
and first derivatives at those eigenvalues. -/
theorem exists_hermite_polynomial_hasFDerivWithinAt_cfc
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ f (hA.eigenvalues i)) :
    ∃ p : ℝ[X], (∀ i, p.eval (hA.eigenvalues i) = f (hA.eigenvalues i)) ∧
      (∀ i, p.derivative.eval (hA.eigenvalues i) = deriv f (hA.eigenvalues i)) ∧
      HasFDerivWithinAt (fun B : Matrix n n ℂ => cfc f B)
        (p.frechetDerivative A) {B | B.IsHermitian} A := by
  classical
  let s := Finset.univ.image hA.eigenvalues
  let p := Lagrange.hermiteInterpolate s id f (deriv f)
  have hv (i : n) : p.eval (hA.eigenvalues i) = f (hA.eigenvalues i) :=
    Lagrange.eval_hermiteInterpolate_at_node (fun _ _ _ _ h => h) f (deriv f)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hd (i : n) : p.derivative.eval (hA.eigenvalues i) = deriv f (hA.eigenvalues i) :=
    Lagrange.eval_derivative_hermiteInterpolate_at_node (fun _ _ _ _ h => h) f (deriv f)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  refine ⟨p, hv, hd, ?_⟩
  let g : ℝ → ℝ := fun x => f x - p.eval x
  have hg (i : n) : g (hA.eigenvalues i) = 0 := by dsimp [g]; rw [hv, sub_self]
  have hg' (i : n) : HasDerivAt g 0 (hA.eigenvalues i) := by
    have h := (hf i).hasDerivAt.sub (p.hasDerivAt (hA.eigenvalues i))
    convert! h using 1
    exact (sub_self _).symm.trans (congrArg (fun z => deriv f (hA.eigenvalues i) - z) (hd i).symm)
  have h := (hasFDerivWithinAt_cfc_zero_of_spectral_vanishing hA hg hg').add
    (p.hasFDerivAt_aeval_noncomm A).hasFDerivWithinAt
  simp only [zero_add] at h
  have heq (B : Matrix n n ℂ) (hB : B.IsHermitian) :
      cfc f B = cfc g B + aeval B p := by
    have hsub : cfc g B = cfc f B - cfc p.eval B :=
      cfc_sub f p.eval B (B.finite_real_spectrum.continuousOn f)
        (B.finite_real_spectrum.continuousOn p.eval)
    have hp : cfc p.eval B = aeval B p := cfc_polynomial p B hB
    calc
      _ = (cfc f B - cfc p.eval B) + cfc p.eval B := by abel
      _ = _ := by rw [← hsub, hp]
  exact h.congr (fun B hB => heq B hB) (heq A hA)

end NLAlib
