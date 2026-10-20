import NLAlib.ForMathlib.Analysis.Matrix.PositiveLimit
import Mathlib.Topology.Connected.Clopen

/-! # Positive definiteness along a genuine connected family of units

The PSD cone is closed, while positive definiteness is open among
Hermitian matrices. Genuine invertibility excludes a change of sign.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- A continuous connected family of genuinely invertible Hermitian
matrices is positive definite everywhere if it is positive definite
at one point. Neither PSD nor a spectral-gap conclusion is assumed
at the other parameters. -/
theorem posDef_everywhere_of_preconnected_isUnit
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → M) (hA : Continuous A) (hH : ∀ x : X, (A x).IsHermitian)
    (hU : ∀ x : X, IsUnit (A x)) (h0 : ∃ x : X, (A x).PosDef) :
    ∀ x : X, (A x).PosDef := by
  let P : Set X := {x | (0 : M)≤A x}
  have hPc : IsClosed P := isClosed_le continuous_const hA
  have hPo : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hPSD : (A x).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hx
    have hp : (A x).PosDef := hPSD.posDef_iff_isUnit.mpr (hU x)
    have he := hp.eventually_of_tendsto (hA.continuousAt.tendsto)
      (Eventually.of_forall hH)
    exact he.mono fun y hy => hy.posSemidef.nonneg
  have hPne : P.Nonempty := by
    obtain ⟨x,hx⟩ := h0
    exact ⟨x,hx.posSemidef.nonneg⟩
  have hPeq : P=univ := (show IsClopen P from ⟨hPc,hPo⟩).eq_univ hPne
  intro x
  have hp : x∈P := by rw [hPeq]; trivial
  have hPSD : (A x).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hp
  exact hPSD.posDef_iff_isUnit.mpr (hU x)

end Matrix
