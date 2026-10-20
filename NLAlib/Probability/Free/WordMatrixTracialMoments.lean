import NLAlib.Probability.Free.WordMatrixClosedAlgebra
import NLAlib.ForMathlib.MeasureTheory.TracialGramMoments

/-!
# Native vacuum Gram moments under actual norm perturbations

The native amplified vacuum is restricted to the genuine norm-closed
matrix field algebra before invoking tracial moment estimates. Its norm is
the inherited native amplified norm. No trace on all Hilbert operators is
claimed or assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

/-- Genuine rooted amplified-vacuum Gram moments change by at most the
actual native norm of the perturbation, provided both actual operators
belong to the closed matrix word algebra. Empty dimensions are included.

Prerequisite for the mean-uniform bound of arXiv:2406.11453v2, Theorem 4.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem abs_wordMatrixVacuum_gramMoment_rpow_sub_le_norm
    (S T : M) (hS : S ∈ wordMatrixFieldAlgebra (D := D) (ι := ι))
    (hT : T ∈ wordMatrixFieldAlgebra (D := D) (ι := ι)) (m : ℕ) (hm : 0 < m) :
    |((wordMatrixVacuumExpectation (D := D) (ι := ι) ((star S*S)^m)).re) ^
        ((2*m : ℝ)⁻¹) -
      ((wordMatrixVacuumExpectation (D := D) (ι := ι) ((star T*T)^m)).re) ^
        ((2*m : ℝ)⁻¹)| ≤ ‖S-T‖ := by
  cases isEmpty_or_nonempty D with
  | inl hD =>
    have he : S=T := by ext i; exact (hD.false i).elim
    subst T
    simp
  | inr hD =>
    let : Nonempty D := hD
    let P := wordMatrixFieldAlgebra (D := D) (ι := ι)
    let hclosed : IsClosed (P : Set M) := isClosed_wordMatrixFieldAlgebra
    let : CStarAlgebra P := StarSubalgebra.cstarAlgebra P (h_closed := hclosed)
    let : PartialOrder P := CStarAlgebra.spectralOrder P
    let : StarOrderedRing P := CStarAlgebra.spectralOrderedRing P
    let τ : P →ₚ[ℂ] ℂ :=
      PositiveLinearMap.mk₀
        ((wordMatrixVacuumExpectation (D := D) (ι := ι)).comp
          P.subtype.toAlgHom.toLinearMap)
        (fun X hX => by
          apply (wordMatrixVacuumPositiveMap (D := D) (ι := ι)).map_nonneg
          have hXX : X=star (CFC.sqrt X)*CFC.sqrt X := by
            rw [(CFC.sqrt_nonneg X).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self X hX]
          change 0≤(X : M)
          calc
            _ ≤ star ((CFC.sqrt X : P) : M)*((CFC.sqrt X : P) : M) :=
              star_mul_self_nonneg _
            _ = (X : M) := congrArg (fun Z : P => (Z : M)) hXX.symm)
    have hτ : τ 1=1 := wordMatrixVacuumExpectation_one
    have htrace (X Y : P) : τ (X*Y)=τ (Y*X) :=
      wordMatrixVacuumExpectation_mul_comm X.val Y.val X.property Y.property
    have h := τ.abs_gramMoment_rpow_sub_le_norm hτ htrace
      (⟨S,hS⟩ : P) (⟨T,hT⟩ : P) m hm
    exact h

end NLAlib

end
