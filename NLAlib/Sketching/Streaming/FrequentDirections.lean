import NLAlib.Sketching.Streaming.SingularValueShrinkage
import NLAlib.Sketching.Streaming.CovarianceLoss
import NLAlib.ForMathlib.LinearAlgebra.Matrix.RowCol

/-! # The exact Frequent Directions row stream

The state is a fixed-capacity row matrix and accumulated scalar loss. Each update
uses an actual full SVD of the matrix obtained by inserting into its zero last row.
The run relation permits every SVD choice; a chosen-SVD finite fold realizes a run.
Source: Ghashami–Liberty–Phillips–Woodruff (2016), Algorithm 2.1 and §2.1.
Atlas: `frequent-directions-streaming-realization`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {ℓ d : ℕ}

/-- The numeric Frequent Directions state: capacity rows and accumulated shrinkage loss. -/
structure FrequentDirectionsState (ℓ d : ℕ) (𝕜 : Type*) where
  sketch : Matrix (Fin ℓ) (Fin d) 𝕜
  loss : ℝ

/-- The final row slot of a positive-capacity sketch. -/
def fdLastRow (hℓ : 0 < ℓ) : Fin ℓ := ⟨ℓ - 1, by omega⟩

/-- The actual covariance of a finite incoming row list. -/
def rowStreamGram (rows : List (Fin d → 𝕜)) : Matrix (Fin d) (Fin d) 𝕜 :=
  (rows.map (fun a => Matrix.vecMulVec (star a) a)).sum

@[simp] theorem rowStreamGram_nil : rowStreamGram ([] : List (Fin d → 𝕜)) = 0 := rfl
@[simp] theorem rowStreamGram_cons (a : Fin d → 𝕜) (rows : List (Fin d → 𝕜)) :
    rowStreamGram (a :: rows) = Matrix.vecMulVec (star a) a + rowStreamGram rows := rfl
@[simp] theorem rowStreamGram_append (xs ys : List (Fin d → 𝕜)) :
    rowStreamGram (xs ++ ys) = rowStreamGram xs + rowStreamGram ys := by
  simp [rowStreamGram, List.map_append, List.sum_append]

/-- The row-list covariance is the native Gram of its actual positional matrix. -/
theorem rowStreamGram_eq_gram_ofRowList (rows : List (Fin d → 𝕜)) :
    rowStreamGram rows = (Matrix.ofRowList rows)ᴴ * Matrix.ofRowList rows :=
  (Matrix.conjTranspose_ofRowList_mul_ofRowList rows).symm

/-- Enumerating a matrix's rows gives exactly its Gram. -/
theorem rowStreamGram_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin d) 𝕜) :
    rowStreamGram (List.ofFn (fun i => A i)) = Aᴴ * A := Matrix.sum_rowGrams_ofFn A

namespace FrequentDirectionsState

/-- Start from a zero sketch and zero accumulated loss. -/
def initial : FrequentDirectionsState ℓ d 𝕜 := ⟨0, 0⟩

/-- Insert the incoming row into the last slot. Correct states have a zero row there. -/
def insertRow (s : FrequentDirectionsState ℓ d 𝕜) (hℓ : 0 < ℓ) (a : Fin d → 𝕜) :
    Matrix (Fin ℓ) (Fin d) 𝕜 := s.sketch.updateRow (fdLastRow hℓ) a

/-- A transition with its actual SVD witness, retaining every permitted singular basis. -/
def step (s : FrequentDirectionsState ℓ d 𝕜) (hℓ : 0 < ℓ) (a : Fin d → 𝕜)
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜}
    (_h : IsSVD (s.insertRow hℓ a) U V) : FrequentDirectionsState ℓ d 𝕜 :=
  ⟨fdShrinkageRows (s.insertRow hℓ a) V, s.loss + fdShrinkageLoss (s.insertRow hℓ a)⟩

private def svdChoice (C : Matrix (Fin ℓ) (Fin d) 𝕜) :
    {UV : Matrix (Fin ℓ) (Fin ℓ) 𝕜 × Matrix (Fin d) (Fin d) 𝕜 // IsSVD C UV.1 UV.2} :=
  Classical.choice (show Nonempty {UV : Matrix (Fin ℓ) (Fin ℓ) 𝕜 ×
      Matrix (Fin d) (Fin d) 𝕜 // IsSVD C UV.1 UV.2} from by
    obtain ⟨U, V, h⟩ := exists_isSVD C
    exact ⟨⟨(U, V), h⟩⟩)

/-- A total exact-arithmetic SVD transition on positive-capacity states. No measurable
singular-vector selector or finite-precision implementation is assumed. -/
def next (hℓ : 0 < ℓ) (s : FrequentDirectionsState ℓ d 𝕜) (a : Fin d → 𝕜) :
    FrequentDirectionsState ℓ d 𝕜 :=
  s.step hℓ a (svdChoice (s.insertRow hℓ a)).property

/-- The chosen-SVD finite row fold from an arbitrary numeric state. -/
def runFrom (hℓ : 0 < ℓ) (s : FrequentDirectionsState ℓ d 𝕜) (rows : List (Fin d → 𝕜)) :
    FrequentDirectionsState ℓ d 𝕜 := rows.foldl (next hℓ) s

/-- The actual Frequent Directions row-stream algorithm. -/
def run (hℓ : 0 < ℓ) (rows : List (Fin d → 𝕜)) : FrequentDirectionsState ℓ d 𝕜 :=
  runFrom hℓ initial rows

/-- The same algorithm on a positional matrix input, in its row order. -/
def runMatrix {N : ℕ} (hℓ : 0 < ℓ) (A : Matrix (Fin N) (Fin d) 𝕜) :
    FrequentDirectionsState ℓ d 𝕜 := run hℓ (List.ofFn (fun i => A i))

end FrequentDirectionsState

/-- All finite runs of the actual row-insertion/SVD update, allowing every SVD witness. -/
inductive FrequentDirectionsRun (hℓ : 0 < ℓ) :
    FrequentDirectionsState ℓ d 𝕜 → List (Fin d → 𝕜) → FrequentDirectionsState ℓ d 𝕜 → Prop
  | nil (s : FrequentDirectionsState ℓ d 𝕜) : FrequentDirectionsRun hℓ s [] s
  | cons {s out : FrequentDirectionsState ℓ d 𝕜} {a : Fin d → 𝕜} {rows : List (Fin d → 𝕜)}
      {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜}
      (hSVD : IsSVD (s.insertRow hℓ a) U V)
      (hTail : FrequentDirectionsRun hℓ (s.step hℓ a hSVD) rows out) :
      FrequentDirectionsRun hℓ s (a :: rows) out

/-- The zero-row, covariance, and exact trace-loss invariants of a processed prefix. -/
structure FrequentDirectionsInvariant (hℓ : 0 < ℓ) (G : Matrix (Fin d) (Fin d) 𝕜)
    (s : FrequentDirectionsState ℓ d 𝕜) : Prop where
  last_row_zero : s.sketch (fdLastRow hℓ) = 0
  certificate : CovarianceLossCertificate ℓ G (s.sketchᴴ * s.sketch) s.loss
  trace_eq : RCLike.re (G - s.sketchᴴ * s.sketch).trace = (ℓ : ℝ) * s.loss

/-- The initial state realizes all invariants, including an empty stream. -/
theorem frequentDirections_initial_invariant (hℓ : 0 < ℓ) :
    FrequentDirectionsInvariant hℓ (0 : Matrix (Fin d) (Fin d) 𝕜)
      FrequentDirectionsState.initial := by
  constructor
  · rfl
  · simpa [FrequentDirectionsState.initial] using
      CovarianceLossCertificate.zero ℓ (0 : Matrix (Fin d) (Fin d) 𝕜)
  · simp [FrequentDirectionsState.initial]

/-- Every actual SVD update preserves the zero-row and exact covariance-loss invariants.
This theorem permits arbitrary ties and zero removed singular values. -/
theorem frequentDirections_step_invariant {hℓ : 0 < ℓ} (hℓd : ℓ ≤ d)
    {G : Matrix (Fin d) (Fin d) 𝕜} {s : FrequentDirectionsState ℓ d 𝕜}
    (hs : FrequentDirectionsInvariant hℓ G s) (a : Fin d → 𝕜)
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜}
    (hSVD : IsSVD (s.insertRow hℓ a) U V) :
    FrequentDirectionsInvariant hℓ (G + Matrix.vecMulVec (star a) a) (s.step hℓ a hSVD) := by
  let C := s.insertRow hℓ a
  let B := fdShrinkageRows C V
  let δ := fdShrinkageLoss C
  have hInsert : Cᴴ * C = s.sketchᴴ * s.sketch + Matrix.vecMulVec (star a) a :=
    Matrix.conjTranspose_updateRow_mul_updateRow_eq_add s.sketch (fdLastRow hℓ) a hs.last_row_zero
  have hBounds := hSVD.fdShrinkage_gram_loss_bounds hℓ hℓd
  have hLoss := hSVD.fdShrinkage_frobSq_loss hℓ hℓd
  have hTrace : RCLike.re (Cᴴ * C - Bᴴ * B).trace = (ℓ : ℝ) * δ := by
    rw [Matrix.trace_sub, map_sub, ← frobSq_eq_re_trace_conjTranspose_mul_self,
      ← frobSq_eq_re_trace_conjTranspose_mul_self]
    exact hLoss
  have hStepCert : CovarianceLossCertificate ℓ (Cᴴ * C) (Bᴴ * B) δ :=
    ⟨fdShrinkageLoss_nonneg C, hBounds.1, hBounds.2, hTrace.ge⟩
  have hBefore : CovarianceLossCertificate ℓ (G + Matrix.vecMulVec (star a) a) (Cᴴ * C) s.loss := by
    have hc := hs.certificate.add (CovarianceLossCertificate.zero ℓ (Matrix.vecMulVec (star a) a))
    simpa only [hInsert, add_zero] using hc
  have hD : G + Matrix.vecMulVec (star a) a - Bᴴ * B =
      (G - s.sketchᴴ * s.sketch) + (Cᴴ * C - Bᴴ * B) := by rw [hInsert]; abel
  constructor
  · funext j
    exact fdShrinkageRows_last_eq_zero C V hℓ j
  · exact hBefore.trans hStepCert
  · change RCLike.re (G + Matrix.vecMulVec (star a) a - Bᴴ * B).trace = (ℓ : ℝ) * (s.loss + δ)
    rw [hD, Matrix.trace_add, map_add, hs.trace_eq, hTrace]
    ring

/-- Every permitted finite run realizes the covariance-loss certificate and exact trace
identity. The statement is uniform over all SVD choices made by the run.
atlas: frequent-directions-streaming-realization (partial) -/
theorem FrequentDirectionsRun.invariant {hℓ : 0 < ℓ} {s out : FrequentDirectionsState ℓ d 𝕜}
    {rows : List (Fin d → 𝕜)} (hRun : FrequentDirectionsRun hℓ s rows out) (hℓd : ℓ ≤ d)
    (G : Matrix (Fin d) (Fin d) 𝕜) (hs : FrequentDirectionsInvariant hℓ G s) :
    FrequentDirectionsInvariant hℓ (G + rowStreamGram rows) out := by
  induction hRun generalizing G with
  | nil s => simpa using hs
  | @cons s out a rows U V hSVD hTail ih =>
    have hNext := frequentDirections_step_invariant hℓd hs a hSVD
    have hOut := ih (G + Matrix.vecMulVec (star a) a) hNext
    simpa only [rowStreamGram_cons, add_assoc] using hOut

/-- The chosen-SVD finite fold is an actual permitted run.
atlas: frequent-directions-streaming-realization (partial) -/
theorem frequentDirections_runFrom_realizes (hℓ : 0 < ℓ) (s : FrequentDirectionsState ℓ d 𝕜)
    (rows : List (Fin d → 𝕜)) :
    FrequentDirectionsRun hℓ s rows (FrequentDirectionsState.runFrom hℓ s rows) := by
  induction rows generalizing s with
  | nil => exact FrequentDirectionsRun.nil s
  | cons a rows ih =>
    let w := FrequentDirectionsState.svdChoice (s.insertRow hℓ a)
    exact FrequentDirectionsRun.cons w.property (ih (FrequentDirectionsState.next hℓ s a))

/-- The actual chosen-SVD row-stream output satisfies all source invariants.
Ghashami–Liberty–Phillips–Woodruff (2016), Algorithm 2.1, Properties 1–3.
atlas: frequent-directions-streaming-realization (partial) -/
theorem frequentDirections_run_invariant (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    (rows : List (Fin d → 𝕜)) :
    FrequentDirectionsInvariant hℓ (rowStreamGram rows) (FrequentDirectionsState.run hℓ rows) := by
  have hRun := frequentDirections_runFrom_realizes hℓ FrequentDirectionsState.initial rows
  have hInv := hRun.invariant hℓd 0 (frequentDirections_initial_invariant hℓ)
  simpa only [zero_add, FrequentDirectionsState.run] using hInv

/-- The matrix-input implementation preserves the exact Gram and trace-loss contracts,
including zero input rows and an empty input matrix.
atlas: frequent-directions-streaming-realization (partial) -/
theorem frequentDirections_runMatrix_invariant {N : ℕ} (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    (A : Matrix (Fin N) (Fin d) 𝕜) :
    FrequentDirectionsInvariant hℓ (Aᴴ * A) (FrequentDirectionsState.runMatrix hℓ A) := by
  simpa only [rowStreamGram_ofFn, FrequentDirectionsState.runMatrix] using frequentDirections_run_invariant hℓ hℓd
    (List.ofFn (fun i => A i))

/-- The source trace budget is an exact difference of squared Frobenius norms for the
implemented stream, rather than only an inequality.
atlas: frequent-directions-streaming-realization (partial) -/
theorem frequentDirections_runMatrix_frobSq_loss {N : ℕ}
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) (A : Matrix (Fin N) (Fin d) 𝕜) :
    frobSq A - frobSq (FrequentDirectionsState.runMatrix hℓ A).sketch =
      (ℓ : ℝ) * (FrequentDirectionsState.runMatrix hℓ A).loss := by
  have ht := (frequentDirections_runMatrix_invariant hℓ hℓd A).trace_eq
  rw [Matrix.trace_sub, map_sub, ← frobSq_eq_re_trace_conjTranspose_mul_self,
    ← frobSq_eq_re_trace_conjTranspose_mul_self] at ht
  exact ht

/-- The implemented matrix-input stream has the optimal covariance-tail constant.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.1.
atlas: frequent-directions-streaming-realization (partial)-/
theorem frequentDirections_runMatrix_specNorm_sub_gram_le {N : ℕ}
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) (A : Matrix (Fin N) (Fin d) 𝕜)
    {k : ℕ} (hkℓ : k < ℓ) :
    specNorm (Aᴴ * A - (FrequentDirectionsState.runMatrix hℓ A).sketchᴴ *
      (FrequentDirectionsState.runMatrix hℓ A).sketch) ≤
        bestRankFrobSq A k / ((ℓ - k : ℕ) : ℝ) := by
  have hc := (frequentDirections_runMatrix_invariant hℓ hℓd A).certificate
  exact hc.specNorm_sub_gram_le_bestRankFrobSq_div hkℓ (by simpa using (hkℓ.le.trans hℓd))

/-- Every leading right projector of the actual stream output gives the source relative
rank-k projection bound. There is no extra eigenspace or maximization assumption.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.2.
atlas: frequent-directions-streaming-realization (partial)-/
theorem frequentDirections_runMatrix_frobSq_error_le {N : ℕ}
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) (A : Matrix (Fin N) (Fin d) 𝕜)
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜}
    (hB : IsSVD (FrequentDirectionsState.runMatrix hℓ A).sketch U V)
    {k : ℕ} (hkℓ : k < ℓ) :
    frobSq (A - A * hB.leadingRightProjector k) ≤
      (ℓ : ℝ) / ((ℓ - k : ℕ) : ℝ) * bestRankFrobSq A k := by
  exact CovarianceLossCertificate.frobSq_error_le_capacity_mul_bestRankFrobSq_div_of_isSVD
    hB (frequentDirections_runMatrix_invariant hℓ hℓd A).certificate hkℓ (by simpa using (hkℓ.le.trans hℓd))

end NLAlib
