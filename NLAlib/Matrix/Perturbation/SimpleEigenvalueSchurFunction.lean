import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The scalar Schur-complement equation near a simple eigenvalue

For a separated scalar/block decomposition, the eigenvalue equation reduces
to a scalar implicit equation with derivative `(t,s) ↦ s-a t` at the origin.
Source: Horn–Johnson (2013), Theorem 6.3.12; operator re-derivation §gen:simple-branch.
This supplies the analytic part of `simple-eigenvalue-perturbation`.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The scalar row/resolvent/column coupling as a continuous linear map on
matrices. Source: operator re-derivation §gen:simple-branch, formula (G18). -/
def schurResolventCoupling (b c : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun M := b ⬝ᵥ (M *ᵥ c)
     map_add' M N := by rw [Matrix.add_mulVec, dotProduct_add]
     map_smul' a M := by rw [Matrix.smul_mulVec, dotProduct_smul]; rfl } :
      Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

/-- The scalar Schur-complement eigenvalue equation, with `s` measuring the
eigenvalue shift and `t` the perturbation parameter. Source: operator
re-derivation §gen:simple-branch, formula (G18). -/
def simpleEigenvalueSchurFunction (μ a : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  p.2 - p.1 * a - p.1 ^ 2 * schurResolventCoupling b c
    (Ring.inverse ((μ + p.2) • 1 - B - p.1 • F))

set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar Schur equation has the expected strict derivative at the
origin whenever the remaining block excludes the original eigenvalue.
Source: Horn–Johnson (2013), Theorem 6.3.12; the quadratic coupling has zero
first derivative at zero, and Banach-algebra inversion is smooth there. -/
theorem hasStrictFDerivAt_simpleEigenvalueSchurFunction (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    HasStrictFDerivAt (simpleEigenvalueSchurFunction μ a B F b c)
      (ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
  let K₀ : Matrix n n ℂ := μ • 1 - B
  let L : (ℂ × ℂ) →L[ℂ] Matrix n n ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight 1 -
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight F
  have hK₀ : IsUnit K₀ := by
    simpa only [K₀, Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hKfun : (fun p : ℂ × ℂ => (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) =
      (fun p => K₀ + L p) := by
    funext p
    change (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F =
      (μ • 1 - B) + (p.2 • 1 - p.1 • F)
    rw [add_smul]
    abel
  have hK : HasStrictFDerivAt (fun p : ℂ × ℂ => K₀ + L p) L 0 :=
    HasStrictFDerivAt.const_add K₀ L.hasStrictFDerivAt
  have hInv : HasStrictFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) ↑hK₀.unit⁻¹ ↑hK₀.unit⁻¹) K₀ := by
    simpa only [hK₀.unit_spec] using hasStrictFDerivAt_ringInverse (𝕜 := ℂ) hK₀.unit
  have hInv' : HasStrictFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) ↑hK₀.unit⁻¹ ↑hK₀.unit⁻¹)
        (K₀ + L (0 : ℂ × ℂ)) := by
    simpa only [map_zero, add_zero] using hInv
  have hQ := (schurResolventCoupling b c).hasStrictFDerivAt.comp 0 (hInv'.comp 0 hK)
  have hfst : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := hasStrictFDerivAt_snd
  have hsq : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1 ^ 2)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) 0 := by
    convert! hfst.mul hfst using 1 <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p
       change (0 : ℂ) = (0 : ℂ) * p.1 + (0 : ℂ) * p.1
       simp)
    | (funext p; simp [pow_two])
  have hquad := hsq.mul hQ
  have hbase' : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2 - p.1 * a)
      (ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
    exact hsnd.sub (hfst.mul_const a)
  have h := hbase'.sub hquad
  have hKval (p : ℂ × ℂ) := congrFun hKfun p
  convert! h using 1 <;> first
  | rfl
  | (apply ContinuousLinearMap.ext; intro p
     simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, sub_apply]
     change p.2 - a * p.1 = (p.2 - a * p.1) -
       ((0 : ℂ) ^ 2 * _ + _ * (0 : ℂ))
     simp)
  | (funext p; simp [simpleEigenvalueSchurFunction, hKval, pow_two])

end NLAlib
