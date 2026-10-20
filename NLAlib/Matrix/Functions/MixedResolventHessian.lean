import NLAlib.Matrix.Functions.MixedResolventDerivatives
import NLAlib.Matrix.Functions.ResolventMomentDerivatives

/-! # Cyclic Hessians of actual mixed resolvent traces

The first cyclic derivative is differentiated as an actual real coordinate
function. Its second derivative is expressed through two strictly positive
resolvent arcs rather than pairs of inserted list positions.
Source: arXiv:2108.06312v2, Lemma 6.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "M" => Matrix d d ℂ
local notation "E" => ((d × d) ⊕ (d × d)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- The exact insertion sum for a mixed trace with a fixed left coefficient.
Every summand has two positive total inverse-arc lengths. -/
def mixedResolventTraceInsertion (X C H : M) (ζ ω : ℂ) (a b : ℕ) : ℂ :=
  (∑ i ∈ Finset.range a, normalizedTrace
    (C * resolvent X ζ ^ (a - i) * H * resolvent X ζ ^ (i + 1) * resolvent X ω ^ b)) +
  ∑ j ∈ Finset.range b, normalizedTrace
    (C * resolvent X ζ ^ a * resolvent X ω ^ (b - j) * H * resolvent X ω ^ (j + 1))

open scoped Matrix.Norms.L2Operator in
/-- Differentiating an actual mixed native resolvent trace with a fixed left
coefficient gives the exact insertion sum, preserving noncommutative order. -/
theorem hasDerivAt_normalizedTrace_left_mul_mixed_resolvent_curve
    {X : ℝ → M} {H : M} {t : ℝ} (hX : HasDerivAt X H t)
    (hXt : (X t).IsHermitian) (C : M) (ζ ω : ℂ)
    (hζ : ζ.im ≠ 0) (hω : ω.im ≠ 0) (a b : ℕ) :
    HasDerivAt (fun u : ℝ => normalizedTrace
      (C * resolvent (X u) ζ ^ a * resolvent (X u) ω ^ b))
      (mixedResolventTraceInsertion (X t) C H ζ ω a b) t := by
  have hr (r : ℂ) (hr : r.im ≠ 0) : HasDerivAt
      (fun u : ℝ => resolvent (X u) r)
      (resolvent (X t) r * H * resolvent (X t) r) t := by
    simpa only [Function.comp_def, rationalBlockMap_apply, rationalBlockDifference_resolvent,
      ContinuousLinearMap.coe_restrictScalars'] using
      (((hasFDerivAt_resolvent_of_isHermitian r (X t) hXt hr).restrictScalars ℝ).comp_hasDerivAt t hX)
  let T : M →L[ℝ] ℂ :=
    ((normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ).comp
      (ContinuousLinearMap.mul ℝ M C)
  have hd := T.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mixed_powers_of_sandwich H (hr ζ hζ) (hr ω hω) a b)
  simpa only [T, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
    normalizedTraceLinearMap_apply, ContinuousLinearMap.mul_apply',
    mixedResolventTraceInsertion, Matrix.mul_add, Finset.mul_sum, normalizedTrace,
    Matrix.trace_add, Matrix.trace_sum, mul_add, Finset.mul_sum, Matrix.mul_assoc] using hd

open scoped Matrix.Norms.L2Operator in
private theorem contDiff_mixed_resolvent_coordinate (A : M) (hA : A.IsHermitian)
    (ζ ω : ℂ) (hζ : ζ.im ≠ 0) (hω : ω.im ≠ 0) (a b : ℕ) :
    ContDiff ℝ ⊤ (fun y : E => normalizedTrace
      (resolvent (A + L y) ζ ^ a * resolvent (A + L y) ω ^ b)) := by
  let w : Fin (a + b) → ℂ × M :=
    Fin.append (fun _ : Fin a => (ζ, 1)) (fun _ : Fin b => (ω, 1))
  have hw : ∀ j, (w j).1.im ≠ 0 := by
    intro j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
    · simpa only [w, Fin.append_left] using hζ
    · simpa only [w, Fin.append_right] using hω
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  simpa only [T, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
    hermitianCoordinateResolventWord, hermitianCoordinateResolvent, w,
    List.ofFn_fin_append, List.map_append, List.prod_append, List.ofFn_const,
    List.map_replicate, List.prod_replicate, mul_one] using
      T.contDiff.comp (contDiff_hermitianCoordinateResolventWord A hA w hw)

open scoped Matrix.Norms.L2Operator in
/-- The actual directional first derivative in Hermitian coordinates is the
two-term cyclic formula, with no commutation assumption on the direction. -/
theorem fderiv_normalizedTrace_mixed_resolvent_coordinate_cyclic_apply
    (A : M) (hA : A.IsHermitian) (ζ ω : ℂ)
    (hζ : ζ.im ≠ 0) (hω : ω.im ≠ 0) (a b : ℕ) (y h : E) :
    fderiv ℝ (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ a * resolvent (A + L x) ω ^ b)) y h =
      (a : ℝ) • normalizedTrace
        (L h * resolvent (A + L y) ζ ^ (a + 1) * resolvent (A + L y) ω ^ b) +
      (b : ℝ) • normalizedTrace
        (L h * resolvent (A + L y) ζ ^ a * resolvent (A + L y) ω ^ (b + 1)) := by
  have hl : HasDerivAt (fun t : ℝ => y + t • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const h |>.const_add y
  have hX : HasDerivAt (fun t : ℝ => A + L (y + t • h)) (L h) 0 :=
    ((L).hasFDerivAt.comp_hasDerivAt 0 hl).const_add A
  have hd := hasDerivAt_normalizedTrace_mixed_resolvent_curve hX
    (by simpa using hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)) ζ ω hζ hω a b
  have hc := contDiff_mixed_resolvent_coordinate A hA ζ ω hζ hω a b
  have he := (hc.differentiable (by simp) (y + (0 : ℝ) • h)).hasFDerivAt.comp_hasDerivAt 0 hl
  have hu := he.unique (by simpa only [Function.comp_def] using hd)
  simpa only [zero_smul, add_zero] using hu

open scoped Matrix.Norms.L2Operator in
/-- The true second coordinate derivative is the cyclic two-arc Hessian.
The formula is obtained by differentiating the actual first gradient, so it
does not assume any Hessian or twice-insertion identity.
Source: arXiv:2108.06312v2, Lemma 6.2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem fderiv_fderiv_normalizedTrace_mixed_resolvent_coordinate_cyclic_apply
    (A : M) (hA : A.IsHermitian) (ζ ω : ℂ)
    (hζ : ζ.im ≠ 0) (hω : ω.im ≠ 0) (a b : ℕ) (y h k : E) :
    fderiv ℝ (fderiv ℝ (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ a * resolvent (A + L x) ω ^ b))) y k h =
      (a : ℝ) • mixedResolventTraceInsertion (A + L y) (L h) (L k) ζ ω (a + 1) b +
      (b : ℝ) • mixedResolventTraceInsertion (A + L y) (L h) (L k) ζ ω a (b + 1) := by
  let f : E → ℂ := fun x => normalizedTrace
    (resolvent (A + L x) ζ ^ a * resolvent (A + L x) ω ^ b)
  have hc : ContDiff ℝ ⊤ f := contDiff_mixed_resolvent_coordinate A hA ζ ω hζ hω a b
  have hdfc : ContDiff ℝ ⊤ (fderiv ℝ f) := hc.fderiv_right (by simp)
  have hl : HasDerivAt (fun t : ℝ => y + t • k) k 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const k |>.const_add y
  have hX : HasDerivAt (fun t : ℝ => A + L (y + t • k)) (L k) 0 :=
    ((L).hasFDerivAt.comp_hasDerivAt 0 hl).const_add A
  have hXt : (A + L (y + (0 : ℝ) • k)).IsHermitian := by
    simpa only [zero_smul, add_zero] using hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)
  have h₁ := hasDerivAt_normalizedTrace_left_mul_mixed_resolvent_curve hX hXt
    (L h) ζ ω hζ hω (a + 1) b
  have h₂ := hasDerivAt_normalizedTrace_left_mul_mixed_resolvent_curve hX hXt
    (L h) ζ ω hζ hω a (b + 1)
  let ev : (E →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ h
  have hv := (ev.hasFDerivAt.comp (y + (0 : ℝ) • k)
    (hdfc.differentiable (by simp) (y + (0 : ℝ) • k)).hasFDerivAt).comp_hasDerivAt 0 hl
  have heq : (fun t : ℝ => ev (fderiv ℝ f (y + t • k))) =
      fun t : ℝ => (a : ℝ) • normalizedTrace
        (L h * resolvent (A + L (y + t • k)) ζ ^ (a + 1) * resolvent (A + L (y + t • k)) ω ^ b) +
        (b : ℝ) • normalizedTrace
        (L h * resolvent (A + L (y + t • k)) ζ ^ a * resolvent (A + L (y + t • k)) ω ^ (b + 1)) := by
    funext t
    exact fderiv_normalizedTrace_mixed_resolvent_coordinate_cyclic_apply A hA ζ ω hζ hω a b _ h
  have hv' : HasDerivAt (fun t : ℝ => ev (fderiv ℝ f (y + t • k)))
      (fderiv ℝ (fderiv ℝ f) y k h) 0 := by
    simpa only [ev, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, zero_smul, add_zero] using hv
  have hd := (h₁.const_smul (a : ℝ)).add (h₂.const_smul (b : ℝ))
  have hd' : HasDerivAt (fun t : ℝ => ev (fderiv ℝ f (y + t • k)))
      ((a : ℝ) • mixedResolventTraceInsertion (A + L y) (L h) (L k) ζ ω (a + 1) b +
       (b : ℝ) • mixedResolventTraceInsertion (A + L y) (L h) (L k) ζ ω a (b + 1)) 0 := by
    rw [heq]
    simpa +instances only [Pi.add_def, Pi.smul_def, Function.comp_def, zero_smul, add_zero] using! hd
  exact hv'.unique hd'

end NLAlib
