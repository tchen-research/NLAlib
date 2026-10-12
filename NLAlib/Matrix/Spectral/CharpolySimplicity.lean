import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic

/-!
# Persistence of simple characteristic roots

The derivative of the characteristic polynomial depends continuously on
the affine pencil parameter and evaluation point. Its nonvanishing makes
every nearby continuous eigenvalue branch algebraically simple.
Source: Horn--Johnson (2013), Theorem 6.3.12; derivations Section gen:simple.
-/

noncomputable section
open Polynomial Filter
open scoped Topology Matrix
namespace NLAlib

/-- A nonzero polynomial has a simple root exactly when its value vanishes
and its derivative does not. Horn--Johnson (2013), Theorem 6.3.12;
scalar helper for persistence of simple eigenvalues. -/
theorem rootMultiplicity_eq_one_iff_isRoot_and_derivative_ne_zero
    {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) (z : K) :
    p.rootMultiplicity z = 1 ↔ p.IsRoot z ∧ p.derivative.eval z ≠ 0 := by
  constructor
  · intro h
    have hroot : p.IsRoot z := (rootMultiplicity_pos hp).mp (by omega)
    refine ⟨hroot, ?_⟩
    intro hd
    have := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, hd⟩
    omega
  · rintro ⟨hroot, hd⟩
    have hpos := (rootMultiplicity_pos hp).mpr hroot
    have hle : p.rootMultiplicity z ≤ 1 := by
      by_contra! hgt
      exact hd ((one_lt_rootMultiplicity_iff_isRoot hp).mp hgt).2
    omega

/-- Evaluating the characteristic-polynomial derivative of an affine
complex pencil is jointly continuous in the parameter and root coordinate.
This uses the fixed bivariate characteristic polynomial, including the
constant characteristic polynomial in dimension zero. Source:
Horn--Johnson (2013), Theorem 6.3.12; simple-root persistence helper. -/
theorem continuous_eval_derivative_charpoly_affine
    {n : Type*} [Fintype n] [DecidableEq n] (A E : Matrix n n ℂ) :
    Continuous (fun p : ℂ × ℂ => ((A + p.1 • E).charpoly.derivative).eval p.2) := by
  let M : Matrix n n ℂ[X] := A.map C + (X : ℂ[X]) • E.map C
  let P := M.charpoly
  have hmap (t : ℂ) : P.map (evalRingHom t) = (A + t • E).charpoly := by
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j
    simp [M, Matrix.map_apply]
    ring
  have hder (t : ℂ) : P.derivative.map (evalRingHom t) =
      (A + t • E).charpoly.derivative := by
    rw [← derivative_map, hmap]
  have hcont : Continuous (fun p : ℂ × ℂ =>
      (P.derivative.map (evalRingHom p.1)).eval p.2) := by
    simp only [eval_map, eval₂_eq_sum, Polynomial.sum, coe_evalRingHom]
    apply continuous_finsetSum
    intro i _
    exact ((P.derivative.coeff i).continuous.comp continuous_fst).mul (continuous_snd.pow i)
  simpa only [hder] using hcont

/-- Any continuous eigenvalue branch through an algebraically simple
eigenvalue of an affine pencil stays algebraically simple near its base
point. The parameter space is arbitrary, so both complex and real branches
are covered. There is no nonempty-dimension assumption; the simplicity
hypothesis is impossible for the empty matrix. Source: Horn--Johnson
(2013), Theorem 6.3.12; derivations gen:simple.
atlas: simple-eigenvalue-perturbation (partial)
-/
theorem eventually_rootMultiplicity_eq_one_of_continuous_eigenvalue
    {n T : Type*} [Fintype n] [DecidableEq n] [TopologicalSpace T]
    (A E : Matrix n n ℂ) {t₀ : T} (τ φ : T → ℂ)
    (hτ : ContinuousAt τ t₀) (hφ : ContinuousAt φ t₀) (hτ₀ : τ t₀ = 0)
    (hμ : A.charpoly.rootMultiplicity (φ t₀) = 1)
    (hspec : ∀ᶠ t in 𝓝 t₀, φ t ∈ spectrum ℂ (A + τ t • E)) :
    ∀ᶠ t in 𝓝 t₀, (A + τ t • E).charpoly.rootMultiplicity (φ t) = 1 := by
  have hne : A.charpoly.derivative.eval (φ t₀) ≠ 0 :=
    ((rootMultiplicity_eq_one_iff_isRoot_and_derivative_ne_zero
      A.charpoly A.charpoly_monic.ne_zero (φ t₀)).mp hμ).2
  have hc : ContinuousAt (fun t => (A + τ t • E).charpoly.derivative.eval (φ t)) t₀ :=
    (continuous_eval_derivative_charpoly_affine A E).continuousAt.comp
      (hτ.prodMk hφ)
  have hnear := hc.eventually_ne (by simpa only [hτ₀, zero_smul, add_zero] using hne)
  filter_upwards [hspec, hnear] with t ht hdt
  exact (rootMultiplicity_eq_one_iff_isRoot_and_derivative_ne_zero
    _ (A + τ t • E).charpoly_monic.ne_zero _).mpr
      ⟨Matrix.mem_spectrum_iff_isRoot_charpoly.mp ht, hdt⟩

end NLAlib
