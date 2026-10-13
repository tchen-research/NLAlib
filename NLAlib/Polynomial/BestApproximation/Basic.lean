import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Uniform polynomial approximation and interpolation

The canonical degree-bounded subspace of continuous real functions on a compact set,
its best uniform approximation error, and the Lebesgue function and constant of Lagrange
interpolation. Sources: Trefethen, ATAP, Chapters 10 and 15.
Atlas: `minimax-error-def`, `lebesgue-constant-def`.
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- Restrictions of real polynomials of degree at most `n` to `s`.
Source: Trefethen, ATAP, Chapter 10, the space `P_n`.
atlas: minimax-error-def (partial) -/
def polynomialApproximationSpace (s : Set ℝ) (n : ℕ) : Submodule ℝ C(s, ℝ) :=
  (degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap

/-- Best uniform error for degree at most `n`, defined as distance to the polynomial subspace.
Source: Trefethen, ATAP, Chapter 10, `E_n(f)`.
atlas: minimax-error-def (partial) -/
def minimaxError {s : Set ℝ} [CompactSpace s] (n : ℕ) (f : C(s, ℝ)) : ℝ :=
  Metric.infDist f (polynomialApproximationSpace s n)

/-- The pointwise sum of absolute Lagrange cardinal functions.
Source: Trefethen, ATAP, Chapter 15, the Lebesgue function.
atlas: lebesgue-constant-def (partial) -/
def lebesgueFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, |(Lagrange.basis Finset.univ v i).eval x|

/-- The Lebesgue constant on `s`, expressed using the supremum norm.
Source: Trefethen, ATAP, Chapter 15.
atlas: lebesgue-constant-def (partial) -/
def lebesgueConstant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Set ℝ) [CompactSpace s] (v : ι → ℝ) : ℝ :=
  ‖(⟨fun x : s => lebesgueFunction v x,
    by unfold lebesgueFunction; fun_prop⟩ : C(s, ℝ))‖

/-- A continuous function belongs to the degree-bounded polynomial space exactly when it
is the restriction of a polynomial of the required degree. Source: ATAP, Chapter 10. -/
theorem mem_polynomialApproximationSpace_iff {s : Set ℝ} {n : ℕ} {f : C(s, ℝ)} :
    f ∈ polynomialApproximationSpace s n ↔
      ∃ p : ℝ[X], p.degree ≤ n ∧ p.toContinuousMapOn s = f := by
  simp [polynomialApproximationSpace, Submodule.mem_map, mem_degreeLE]

/-- Lagrange interpolation as a linear map on continuous functions.
Source: Trefethen, ATAP, Chapter 15. -/
def interpolationLinearMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Set ℝ) (v : ι → s) : C(s, ℝ) →ₗ[ℝ] C(s, ℝ) :=
  (toContinuousMapOnAlgHom s).toLinearMap ∘ₗ
    (Lagrange.interpolate Finset.univ (fun i => (v i : ℝ))) ∘ₗ
      { toFun := fun f i => f (v i)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }

/-- Interpolation is the restriction of Mathlib's Lagrange interpolating polynomial.
Source: Trefethen, ATAP, Chapter 15. -/
@[simp] theorem interpolationLinearMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Set ℝ) (v : ι → s) (f : C(s, ℝ)) :
    interpolationLinearMap s v f =
      (Lagrange.interpolate Finset.univ (fun i => (v i : ℝ)) (fun i => f (v i))).toContinuousMapOn
        s := rfl

/-- A real rational function of type `(m,n)` with no pole on the approximation domain.
Source: Trefethen, ATAP, Chapters 23–24. Canonical numerator and denominator are Mathlib's
coprime `RatFunc.num` and monic `RatFunc.denom`.
atlas: rational-equioscillation (partial) -/
def IsPoleFreeRationalApproximation (s : Set ℝ) (m n : ℕ) (r : RatFunc ℝ) : Prop :=
  r.num.degree ≤ m ∧ r.denom.degree ≤ n ∧ ∀ x ∈ s, r.denom.eval x ≠ 0

/-- Restriction of a pole-free rational function to its real domain.
Source: Trefethen, ATAP, Chapters 23–24. -/
def rationalContinuousMap (s : Set ℝ) (r : RatFunc ℝ)
    (hpole : ∀ x ∈ s, r.denom.eval x ≠ 0) : C(s, ℝ) :=
  ⟨fun x => r.num.eval (x : ℝ) / r.denom.eval (x : ℝ),
    (r.num.continuous.comp continuous_subtype_val).div
      (r.denom.continuous.comp continuous_subtype_val) (fun x => hpole (x : ℝ) x.property)⟩

/-- The restricted rational map uses Mathlib's canonical rational-function evaluation.
Source: Trefethen, ATAP, Chapter 23. -/
@[simp] theorem rationalContinuousMap_apply_eq_eval (s : Set ℝ) (r : RatFunc ℝ)
    (hpole : ∀ x ∈ s, r.denom.eval x ≠ 0) (x : s) :
    rationalContinuousMap s r hpole x = r.eval (RingHom.id ℝ) x := by
  simp [rationalContinuousMap, RatFunc.eval]

/-- The set of pole-free type-`(m,n)` real rational restrictions.
Source: Trefethen, ATAP, Chapter 23.
atlas: rational-equioscillation (partial) -/
def rationalApproximationSpace (s : Set ℝ) (m n : ℕ) : Set C(s, ℝ) :=
  {g | ∃ (r : RatFunc ℝ) (hr : IsPoleFreeRationalApproximation s m n r),
    rationalContinuousMap s r hr.2.2 = g}

/-- Best uniform error among pole-free real rational functions of type `(m,n)`.
Source: Trefethen, ATAP, Chapter 24.
atlas: rational-equioscillation (partial) -/
def rationalMinimaxError {s : Set ℝ} [CompactSpace s] (m n : ℕ) (f : C(s, ℝ)) : ℝ :=
  Metric.infDist f (rationalApproximationSpace s m n)

/-- The exact number of numerator degrees available in rational descent directions.
For a nonzero function this is `m+n-defect`; the zero function has degree parameter `m`,
equivalently defect `n`, rather than treating its numerator as a degree-zero polynomial.
Source: Trefethen, ATAP, Chapter 24; operator rederivations, `polybest:rational`.
atlas: rational-equioscillation (partial) -/
def rationalAlternationDegree (m n : ℕ) (r : RatFunc ℝ) : ℕ := by
  classical
  exact if r = 0 then m else max (m + r.denom.natDegree) (n + r.num.natDegree)

/-- Canonical interpolation nodes with endpoints `−1,1` and the supplied interior coordinates.
Source: focused reroutes, the node simplex for `lebesgue-constant-lower-bound`. -/
def canonicalIntervalNodes (n : ℕ) (t : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.cases (-1) (Fin.lastCases 1 t)

/-- The open ordered simplex of canonical interpolation node configurations.
Source: focused reroutes, the node simplex for `lebesgue-constant-lower-bound`. -/
def interiorNodeSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {t | StrictMono (canonicalIntervalNodes n t)}

/-- The fixed signs of Lagrange cardinals in a specified gap of an ordered node grid.
Source: focused reroutes, the gap polynomial for `lebesgue-constant-lower-bound`. -/
def interpolationGapSign (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) : ℝ :=
  if j.val ≤ i.val then (-1) ^ (i.val - j.val) else (-1) ^ (j.val - i.val - 1)

/-- The signed cardinal polynomial which equals the Lebesgue function on its node gap.
Source: focused reroutes, the polynomial `F_i` in `lebesgue-constant-lower-bound`. -/
def interpolationGapPolynomial (n : ℕ) (t : Fin n → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (canonicalIntervalNodes n t) (interpolationGapSign n i)

/-- The actual interpolation Lebesgue peak on one closed canonical node gap.
Source: focused reroutes, the peak map in `lebesgue-constant-lower-bound`. -/
def interpolationGapPeak (n : ℕ) (t : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  lebesgueConstant (Set.Icc (canonicalIntervalNodes n t i.castSucc)
    (canonicalIntervalNodes n t i.succ)) (canonicalIntervalNodes n t)

/-- The canonical vector of interpolation peak differences from the first gap.
Source: focused reroutes, the proper peak-difference map for
`lebesgue-constant-lower-bound`; first-gap differences replace adjacent differences
by an invertible triangular coordinate change. -/
def interpolationPeakDifference (n : ℕ) (t : Fin n → ℝ) : Fin n → ℝ :=
  fun j => interpolationGapPeak n t j.succ - interpolationGapPeak n t 0

end NLAlib
