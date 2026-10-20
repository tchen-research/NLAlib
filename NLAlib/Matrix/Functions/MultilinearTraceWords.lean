import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Continuous multilinear alternating matrix trace words

The actual ordered trace-word map is continuous multilinear both in its
arguments and in its coefficient array. The latter supplies measurability
and integrability for random coefficient arrays.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Proposition 5.1;
Supports `independent-sum-spectrum-universality`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The literal alternating matrix trace word as a continuous complex
multilinear map in its deterministic factors. Products are in ascending Fin
order, so this definition applies to noncommutative matrix multiplication.
Source: the multilinear functional in Brailovskaya–van Handel,
arXiv:2201.05142v3, Proposition 5.1. -/
def traceWordMultilinear {n : Type*} [Fintype n] [DecidableEq n]
    {k : ℕ} (Z : Fin k → Matrix n n ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Matrix n n ℂ) ℂ :=
  (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.compContinuousMultilinearMap
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (Matrix n n ℂ)).compContinuousLinearMap
      (fun j => ContinuousLinearMap.mul ℂ (Matrix n n ℂ) (Z j)))

open scoped Matrix.Norms.L2Operator in
@[simp]
theorem traceWordMultilinear_apply {n : Type*} [Fintype n] [DecidableEq n]
    {k : ℕ} (Z Y : Fin k → Matrix n n ℂ) :
    traceWordMultilinear Z Y = (List.ofFn (fun j => Z j * Y j)).prod.trace := rfl


open scoped Matrix.Norms.L2Operator in
/-- The ordered trace-word functional is itself continuous multilinear in its
matrix coefficients. This supplies native measurability and Bochner
integrability of the actual random multilinear functional. -/
def traceWordMultilinearCoefficients {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin k => Matrix n n ℂ)
      (ContinuousMultilinearMap ℂ (fun _ : Fin k => Matrix n n ℂ) ℂ) :=
  ContinuousMultilinearMap.compContinuousLinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapLRight
      ((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.compContinuousMultilinearMap
        (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (Matrix n n ℂ))))
    (fun _ => ContinuousLinearMap.mul ℂ (Matrix n n ℂ))

open scoped Matrix.Norms.L2Operator in
@[simp]
theorem traceWordMultilinearCoefficients_apply {n : Type*} [Fintype n] [DecidableEq n]
    {k : ℕ} (Z : Fin k → Matrix n n ℂ) :
    traceWordMultilinearCoefficients (n := n) k Z = traceWordMultilinear Z := by
  ext Y
  rfl

open scoped Matrix.Norms.L2Operator in
/-- A uniform coefficient bound gives a bound on the actual trace-word
functional. Its auxiliary operator norm is used only to prove integrability;
it does not occur in the sharp common-marginal endpoint. -/
theorem norm_traceWordMultilinear_le_of_bound {n : Type*} [Fintype n] [DecidableEq n]
    {k : ℕ} (Z : Fin k → Matrix n n ℂ) {R : ℝ}
    (hZ : ∀ j, specNorm (Z j) ≤ R) :
    ‖traceWordMultilinear Z‖ ≤ ‖traceWordMultilinearCoefficients (n := n) k‖ * R ^ k := by
  have h := (traceWordMultilinearCoefficients (n := n) k).le_opNorm_mul_prod_of_le
    (b := fun _ => R) (fun j => by simpa only [← specNorm_eq_norm] using hZ j)
  simpa only [traceWordMultilinearCoefficients_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using h

end NLAlib
