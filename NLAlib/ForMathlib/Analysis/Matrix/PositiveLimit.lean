import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module

/-! # Positive definiteness under genuine Hermitian limits

Strict positivity is open inside the Hermitian space. A positive
derivative therefore gives positive increments on a small right ray.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- A true Hermitian matrix limit that is positive definite makes all
matrices eventually positive definite. The filter may be arbitrary. -/
theorem PosDef.eventually_of_tendsto {X : Type*} {l : Filter X} {f : X → M} {B : M}
    (hB : B.PosDef) (hf : Tendsto f l (𝓝 B))
    (hH : ∀ᶠ x in l, (f x).IsHermitian) : ∀ᶠ x in l, (f x).PosDef := by
  obtain ⟨δ,hδ,hδB⟩ : ∃ δ : ℝ, 0<δ ∧ δ•(1 : M)≤B := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CFC.exists_pos_algebraMap_le_iff hB.isHermitian.isSelfAdjoint).mpr
        (fun r hr => hB.isStrictlyPositive.spectrum_pos hr)
  have hn : ∀ᶠ x in l, ‖f x-B‖<δ :=
    ((hf.sub_const B).norm).eventually (Iio_mem_nhds (by simpa using hδ))
  filter_upwards [hn,hH] with x hx hHx
  have hneg : (-‖f x-B‖)•(1 : M)≤f x-B := by
    simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using
      (hHx.sub hB.isHermitian).isSelfAdjoint.neg_algebraMap_norm_le_self
  have hle : (δ-‖f x-B‖)•(1 : M)≤f x := by
    convert! add_le_add hδB hneg using 1 <;> module
  have hp : IsStrictlyPositive (f x) :=
    (Matrix.PosDef.one.smul (sub_pos.mpr hx)).isStrictlyPositive.of_le hle
  exact Matrix.IsStrictlyPositive.posDef hp

/-- A genuine positive matrix derivative and Hermitian values give
positive increments on a small right ray. No monotonicity conclusion is
assumed. -/
theorem eventually_posDef_sub_of_posDef_deriv
    (f : ℝ → M) (B : M) (hderiv : HasDerivAt f B 0) (hB : B.PosDef)
    (hH : ∀ᶠ t : ℝ in 𝓝 0, (f t).IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (f t-f 0).PosDef := by
  have hlim : Tendsto (fun t : ℝ => t⁻¹•(f t-f 0)) (𝓝[>] 0) (𝓝 B) := by
    simpa only [zero_add] using hderiv.tendsto_slope_zero_right
  have hH0 : (f 0).IsHermitian := hH.self_of_nhds
  have hHs : ∀ᶠ t : ℝ in 𝓝[>] 0, (t⁻¹•(f t-f 0)).IsHermitian := by
    filter_upwards [hH.filter_mono nhdsWithin_le_nhds] with t ht
    exact (ht.sub hH0).smul (IsSelfAdjoint.all t⁻¹)
  have hp := hB.eventually_of_tendsto hlim hHs
  filter_upwards [hp,self_mem_nhdsWithin] with t ht htp
  have hpos : 0<t := htp
  have h := ht.smul hpos
  simpa only [smul_smul,mul_inv_cancel₀ hpos.ne',one_smul] using h

end Matrix
