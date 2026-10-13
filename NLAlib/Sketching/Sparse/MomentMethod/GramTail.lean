/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.SparseStackLaw
import NLAlib.Matrix.Spectral.TracePowerBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Trace-moment tails of the Gram error

Markov's inequality on `E tr G^{2q}` for a finite law (`matrix_markov_tail`, through
`specNorm_pow_two_mul_le_trace_pow`), and its SparseStack instances: the Gram-error norm tail,
the subspace-embedding failure tail and the success-probability lower bound.
Ported from `SparseFockFormal.MatrixTail` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseSketch

open SparseStackSelectors

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite matrix Markov inequality in the precise form used by the moment
method.  The sample space is literal and finite, and symmetry is assumed
pointwise only to invoke the proved operator-norm/trace inequality above.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem FiniteLaw.prob_le_norm_le_expect_trace_pow_div {Ω : Type*} [Fintype Ω]
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
        (μ.expect_mono (fun ω => by
          simpa only [specNorm_eq_norm] using specNorm_pow_two_mul_le_trace_pow (hA ω) hq))
        (pow_nonneg hε.le (2 * q))

/-- The concrete finite-law Markov tail for the actual independent uniform
signed-hash SparseStack distribution.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_matrix_markov_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (sparseStackSelectorLaw s b n hb).prob
        {z | ε ≤ ‖gramError F (sparseStackMatrix (toSample z))‖} ≤
      (sparseStackSelectorLaw s b n hb).expect
          (fun z => ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  exact FiniteLaw.prob_le_norm_le_expect_trace_pow_div (sparseStackSelectorLaw s b n hb)
    (fun z => gramError F (sparseStackMatrix (toSample z)))
    (fun z => gramError_isHermitian F (sparseStackMatrix (toSample z))) q hq ε hε

/-- Failure of the vector OSE property is contained in the concrete norm-tail
event, so it obeys the same trace-moment bound.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_ose_failure_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (sparseStackSelectorLaw s b n hb).prob
        {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε} ≤
      (sparseStackSelectorLaw s b n hb).expect
          (fun z => ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  calc
    (sparseStackSelectorLaw s b n hb).prob
        {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε} ≤
        (sparseStackSelectorLaw s b n hb).prob
          {z | ε ≤ ‖gramError F (sparseStackMatrix (toSample z))‖} := by
      apply FiniteLaw.prob_mono
      intro z hz
      have hiff := norm_gramError_le_iff_isSubspaceEmbedding F (sparseStackMatrix (toSample z))
          hε.le
      by_contra htail
      exact hz (hiff.mp (not_le.mp htail).le)
    _ ≤ (sparseStackSelectorLaw s b n hb).expect
          (fun z => ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) := sparseStack_matrix_markov_tail hb F q hq ε hε

/-- A supplied trace-moment estimate immediately yields an explicit lower
bound on the OSE success probability under the exact SparseStack law.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseStack_ose_success_probability {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ)
    (hmoment :
      (sparseStackSelectorLaw s b n hb).expect
          (fun z => ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
        ε ^ (2 * q) ≤ δ) :
    1 - δ ≤ (sparseStackSelectorLaw s b n hb).prob
      {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε} := by
  let good : Set (SparseStackSelectors s b n) :=
    {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε}
  have hfail : (sparseStackSelectorLaw s b n hb).prob goodᶜ ≤ δ := by
    calc
      (sparseStackSelectorLaw s b n hb).prob goodᶜ =
          (sparseStackSelectorLaw s b n hb).prob
            {z | ¬ IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε} := by
        rfl
      _ ≤ (sparseStackSelectorLaw s b n hb).expect
            (fun z => ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) /
          ε ^ (2 * q) := sparseStack_ose_failure_tail hb F q hq ε hε
      _ ≤ δ := hmoment
  calc
    1 - δ ≤ 1 - (sparseStackSelectorLaw s b n hb).prob goodᶜ := by
      exact sub_le_sub_left hfail 1
    _ = (sparseStackSelectorLaw s b n hb).prob good := by
      simpa using (FiniteLaw.prob_compl (sparseStackSelectorLaw s b n hb) goodᶜ).symm
    _ = (sparseStackSelectorLaw s b n hb).prob
        {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) ε} := rfl

end

end NLAlib.SparseSketch
