/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.SparseFock.SparseStackDistribution
import NLAlib.Matrix.Spectral.TraceEigenvalues
import NLAlib.Matrix.Spectral.QuadraticProbe
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite Gram distortion and matrix tails

Concrete Euclidean quadratic forms link spectral Gram error to subspace distortion and finite trace-moment tail estimates.
Ported from `SparseFockFormal.MatrixTail` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseFock

namespace MatrixTail

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every even power of a real symmetric matrix has nonnegative trace.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_even_pow_nonneg (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (q : ℕ) :
    0 ≤ (A ^ (2 * q)).trace := by
  rw [NLAlib.trace_pow_eq_sum_eigenvalues hA]
  exact Finset.sum_nonneg fun i _hi => (even_two_mul q).pow_nonneg (hA.eigenvalues i)

/-- For a nonempty finite index type, the even power of the L2 operator norm
is bounded by the trace of the corresponding even matrix power.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem opNorm_even_pow_le_trace_of_nonempty [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (q : ℕ) :
    ‖A‖ ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  rw [← specNorm_eq_norm, specNorm_eq_norm_eigenvalues hA,
    NLAlib.trace_pow_eq_sum_eigenvalues hA]
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.eigenvalues).1
  rw [← hi]
  calc
    ‖hA.eigenvalues i‖ ^ (2 * q) = hA.eigenvalues i ^ (2 * q) := by
      rw [Real.norm_eq_abs, ← abs_pow]
      exact abs_of_nonneg ((even_two_mul q).pow_nonneg (hA.eigenvalues i))
    _ ≤ ∑ j, hA.eigenvalues j ^ (2 * q) := by
      exact Finset.single_le_sum
        (fun j _hj => (even_two_mul q).pow_nonneg (hA.eigenvalues j))
        (Finset.mem_univ i)

/-- The operator-norm/trace bridge also covers the empty matrix index type;
there both sides are definitionally zero.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem opNorm_even_pow_le_trace (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (q : ℕ) (hq : 0 < q) :
    ‖A‖ ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      have : IsEmpty ι := hι
      have hzero : A = 0 := Subsingleton.elim _ _
      subst A
      simp [Nat.ne_of_gt hq]
  | inr hι =>
      have : Nonempty ι := hι
      exact opNorm_even_pow_le_trace_of_nonempty A hA q

/-- Finite matrix Markov inequality in the precise form used by the moment
method.  The sample space is literal and finite, and symmetry is assumed
pointwise only to invoke the proved operator-norm/trace inequality above.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_markov_tail {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ ω, (A ω).IsHermitian) (q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    μ.prob {ω | ε ≤ ‖A ω‖} ≤
      μ.expect (fun ω => ((A ω) ^ (2 * q)).trace) / ε ^ (2 * q) := by
  have hpow_ne : 2 * q ≠ 0 := Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hq)
  have hevent : {ω | ε ≤ ‖A ω‖} = {ω | ε ^ (2 * q) ≤ ‖A ω‖ ^ (2 * q)} := by
    ext ω
    exact (pow_le_pow_iff_left₀ hε.le (norm_nonneg _) hpow_ne).symm
  rw [hevent]
  calc
    μ.prob {ω | ε ^ (2 * q) ≤ ‖A ω‖ ^ (2 * q)} ≤
        μ.expect (fun ω => ‖A ω‖ ^ (2 * q)) / ε ^ (2 * q) := by
      exact μ.markov
        (fun ω => pow_nonneg (norm_nonneg (A ω)) (2 * q))
        (pow_pos hε (2 * q))
    _ ≤ μ.expect (fun ω => ((A ω) ^ (2 * q)).trace) / ε ^ (2 * q) := by
      exact div_le_div_of_nonneg_right
        (μ.expect_mono (fun ω => opNorm_even_pow_le_trace (A ω) (hA ω) q hq))
        (pow_nonneg hε.le (2 * q))

open ParsevalFrame SparseStackModel

open SparseStackDistribution

/-- The concrete finite-law Markov tail for the actual independent uniform
signed-hash SparseStack distribution.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_matrix_markov_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (rawSampleLaw s b n hb).prob
        {z | ε ≤ ‖gramError F (stackMatrix (toSample z))‖} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (stackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  exact matrix_markov_tail (rawSampleLaw s b n hb)
    (fun z => gramError F (stackMatrix (toSample z)))
    (fun z => gramError_isHermitian F (stackMatrix (toSample z))) q hq ε hε

/-- Failure of the vector OSE property is contained in the concrete norm-tail
event, so it obeys the same trace-moment bound.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_ose_failure_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (rawSampleLaw s b n hb).prob
        {z | ¬ IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (stackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  calc
    (rawSampleLaw s b n hb).prob
        {z | ¬ IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε} ≤
        (rawSampleLaw s b n hb).prob
          {z | ε ≤ ‖gramError F (stackMatrix (toSample z))‖} := by
      apply FiniteLaw.prob_mono
      intro z hz
      have hiff := norm_gramError_le_iff_isSubspaceEmbedding F (stackMatrix (toSample z)) hε.le
      by_contra htail
      exact hz (hiff.mp (not_le.mp htail).le)
    _ ≤ (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (stackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := sparseStack_matrix_markov_tail hb F q hq ε hε

/-- A supplied trace-moment estimate immediately yields an explicit lower
bound on the OSE success probability under the exact SparseStack law.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_ose_success_probability {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ)
    (hmoment :
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (stackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) ≤ δ) :
    1 - δ ≤ (rawSampleLaw s b n hb).prob
      {z | IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε} := by
  let good : Set (RawSample s b n) :=
    {z | IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε}
  have hfail : (rawSampleLaw s b n hb).prob goodᶜ ≤ δ := by
    calc
      (rawSampleLaw s b n hb).prob goodᶜ =
          (rawSampleLaw s b n hb).prob
            {z | ¬ IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε} := by
        rfl
      _ ≤ (rawSampleLaw s b n hb).expect
            (fun z => ((gramError F (stackMatrix (toSample z))) ^ (2 * q)).trace) /
          ε ^ (2 * q) := sparseStack_ose_failure_tail hb F q hq ε hε
      _ ≤ δ := hmoment
  calc
    1 - δ ≤ 1 - (rawSampleLaw s b n hb).prob goodᶜ := by
      exact sub_le_sub_left hfail 1
    _ = (rawSampleLaw s b n hb).prob good := by
      simpa using (FiniteLaw.prob_compl (rawSampleLaw s b n hb) goodᶜ).symm
    _ = (rawSampleLaw s b n hb).prob
        {z | IsSubspaceEmbedding (stackMatrix (toSample z)) (rowMatrix F.u) ε} := rfl

end

end MatrixTail

end NLAlib.SparseFock
