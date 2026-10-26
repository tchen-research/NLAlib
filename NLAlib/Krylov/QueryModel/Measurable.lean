import NLAlib.Krylov.QueryModel.Basic
import NLAlib.ForMathlib.MeasureTheory.FinTuple
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Measurable and randomized query strategies

A randomized strategy is indexed by a seed. Jointly measurable query and output maps
produce jointly measurable outputs under a jointly measurable oracle. Thus an ordinary
seed probability space suffices; no distribution or independence hypothesis is implicit.

Proofs adapted from Apache-2.0 NLA-lib/NLAlib, commit
79f8cc2f74523a30d1d53316542b826018e245a4, `LowerBounds/QueryModel/Basic.lean`.
Only source is reused; imports refer to the original atlas library.
atlas: matvec-query-model (partial)
-/

namespace NLAlib.QueryAlgorithm
variable {Q R β : Type*} {q : ℕ}
/-- A query algorithm is **measurable** when each of its `q` query maps and the output map are
measurable (for the product σ-algebras on histories); the unused maps `query i`, $i \ge q$, are
unconstrained. Lower bounds quantify over these. -/
structure IsMeasurable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
    (alg : QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is measurable. -/
  measurable_query : ∀ i < q, Measurable (alg.query i)
  /-- The output map is measurable. -/
  measurable_output : Measurable alg.output

/-- A seeded family of query algorithms, a **randomized algorithm** with seed space `S`, is
measurable when its query and output maps are jointly measurable in the seed and the history. -/
structure IsMeasurableFamily {S : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    [MeasurableSpace R] [MeasurableSpace β] (alg : S → QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is jointly measurable in the seed and the history. -/
  measurable_query : ∀ i < q, Measurable fun p : S × (Fin i → R) => (alg p.1).query i p.2
  /-- The output map is jointly measurable in the seed and the transcript. -/
  measurable_output : Measurable fun p : S × (Fin q → R) => (alg p.1).output p.2

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] {M : Type*}
  [MeasurableSpace M]

/-- The history of length $i \le q$ is measurable in the input: for a measurable algorithm and an
oracle $O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ history is
measurable. -/
theorem IsMeasurable.measurable_history {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) {i : ℕ}
    (hi : i ≤ q) : Measurable fun x => alg.history (O x) i := by
  induction i with
  | zero => exact measurable_pi_iff.2 fun j => j.elim0
  | succ i ih =>
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      simp only [QueryAlgorithm.history, Fin.snoc_last]
      exact hO.comp (measurable_id.prodMk
        ((halg.measurable_query i (by omega)).comp (ih (by omega))))
    | cast j =>
      simp only [QueryAlgorithm.history, Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (ih (by omega))

/-- The transcript is measurable in the input: for a measurable algorithm and an oracle
$O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ transcript is
measurable. -/
theorem IsMeasurable.measurable_transcript {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.transcript (O x) :=
  halg.measurable_history hO le_rfl

/-- The output is measurable in the input, for a measurable algorithm and a jointly
measurable oracle. -/
theorem IsMeasurable.measurable_run {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.run (O x) :=
  halg.measurable_output.comp (halg.measurable_transcript hO)

/-- The query matrix is measurable in the transcript, for a measurable algorithm with vector
queries. This is what makes the projectors onto the query spans random matrices. -/
theorem IsMeasurable.measurable_queryMatrix {𝕜 n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm (n → 𝕜) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.queryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp ((halg.measurable_query j j.isLt).comp
    (measurable_pi_iff.2 fun l => measurable_pi_apply _))

/-- The right query matrix is measurable in the transcript, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$. -/
theorem IsMeasurable.measurable_rightQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.rightQueryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp (measurable_fst.comp
    ((halg.measurable_query j j.isLt).comp (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- The left query matrix is measurable in the transcript, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$. -/
theorem IsMeasurable.measurable_leftQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.leftQueryMatrix : (Fin q → R) → Matrix m (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp
    (measurable_snd.comp ((halg.measurable_query j j.isLt).comp
      (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- The histories of a measurable seeded family, jointly measurable in the seed and the input. -/
private theorem measurable_history_family {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    ∀ i ≤ q, Measurable fun p : S × M => (alg p.1).history (O p.2) i := by
  intro i
  induction i with
  | zero => intro _; exact measurable_const
  | succ i ih =>
    intro hi
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      simp only [QueryAlgorithm.history, Fin.snoc_last]
      exact hO.comp (measurable_snd.prodMk ((halg.measurable_query i (by omega)).comp
        (measurable_fst.prodMk (ih (by omega)))))
    | cast j =>
      simp only [QueryAlgorithm.history, Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (ih (by omega))

/-- A randomized algorithm has a jointly measurable output: for a measurable seeded family
and a jointly measurable oracle, (seed, input) $\mapsto$ output is measurable. -/
theorem IsMeasurableFamily.measurable_run {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    Measurable fun p : S × M => (alg p.1).run (O p.2) :=
  halg.measurable_output.comp
    (measurable_fst.prodMk (measurable_history_family halg hO q le_rfl))

/-- Each member of a measurable family is measurable: fixing the seed of a measurable
randomized algorithm gives a measurable deterministic one. -/
theorem IsMeasurableFamily.isMeasurable {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) (s : S) :
    (alg s).IsMeasurable :=
  ⟨fun i hi => (halg.measurable_query i hi).comp measurable_prodMk_left,
    halg.measurable_output.comp measurable_prodMk_left⟩

/-- Truncating a measurable algorithm keeps it measurable, for `i ≤ q`. -/
theorem IsMeasurable.truncate {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable) {i : ℕ}
    (hi : i ≤ q) : (alg.truncate i).IsMeasurable :=
  ⟨fun j hj => halg.measurable_query j (by omega), measurable_const⟩

end Measurable

end NLAlib.QueryAlgorithm
