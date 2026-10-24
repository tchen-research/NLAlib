import NLAlib.Sketching.Streaming.FrequentDirections

/-! # Actual finite Frequent Directions merge trees

Each internal node streams the actual rows of both child sketches through the same
capacity-ℓ row-insertion/SVD algorithm. Loss counters add across children and the node.
The certificate retains capacity ℓ at every depth. Numerical output associativity is
not asserted. Source: Ghashami–Liberty–Phillips–Woodruff (2016), §3.1.
Atlas: `frequent-directions-mergeability`.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {ℓ d : ℕ}

/-- Merge two numeric summaries by running FD on their actual sketch rows and adding
both child loss counters to the new compression loss. -/
def FrequentDirectionsState.merge (hℓ : 0 < ℓ) (s₁ s₂ : FrequentDirectionsState ℓ d 𝕜) :
    FrequentDirectionsState ℓ d 𝕜 :=
  let t := FrequentDirectionsState.run hℓ
    (List.ofFn (fun i => s₁.sketch i) ++ List.ofFn (fun i => s₂.sketch i))
  ⟨t.sketch, s₁.loss + s₂.loss + t.loss⟩

/-- Actual merge composition for arbitrary child summaries carrying valid covariance
certificates. The children may have zero loss or repeated singular values.
Ghashami–Liberty–Phillips–Woodruff (2016), §3.1.
atlas: frequent-directions-mergeability (partial)-/
theorem frequentDirections_merge_certificate (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    {G₁ G₂ : Matrix (Fin d) (Fin d) 𝕜} {s₁ s₂ : FrequentDirectionsState ℓ d 𝕜}
    (h₁ : CovarianceLossCertificate ℓ G₁ (s₁.sketchᴴ * s₁.sketch) s₁.loss)
    (h₂ : CovarianceLossCertificate ℓ G₂ (s₂.sketchᴴ * s₂.sketch) s₂.loss) :
    CovarianceLossCertificate ℓ (G₁ + G₂)
      ((s₁.merge hℓ s₂).sketchᴴ * (s₁.merge hℓ s₂).sketch) (s₁.merge hℓ s₂).loss := by
  let rows := List.ofFn (fun i => s₁.sketch i) ++ List.ofFn (fun i => s₂.sketch i)
  let t := FrequentDirectionsState.run hℓ rows
  have hNode : CovarianceLossCertificate ℓ (s₁.sketchᴴ * s₁.sketch + s₂.sketchᴴ * s₂.sketch)
      (t.sketchᴴ * t.sketch) t.loss := by
    simpa only [rows, rowStreamGram_append, rowStreamGram_ofFn] using
      (frequentDirections_run_invariant hℓ hℓd rows).certificate
  exact (h₁.add h₂).trans hNode

/-- Merge any finite batch of actual numeric summaries by streaming their stacked rows.
This is the rowwise merge realization, including the empty batch. -/
def FrequentDirectionsState.mergeMany (hℓ : 0 < ℓ)
    (summaries : List (FrequentDirectionsState ℓ d 𝕜)) : FrequentDirectionsState ℓ d 𝕜 :=
  let t := FrequentDirectionsState.run hℓ
    (summaries.flatMap (fun s => List.ofFn (fun i => s.sketch i)))
  ⟨t.sketch, (summaries.map (fun s => s.loss)).sum + t.loss⟩

/-- Arbitrary finite batches of certified summaries retain capacity ℓ after their actual
stacked-row FD merge. Gram inputs may represent blocks of any row sizes, including zero.
Ghashami–Liberty–Phillips–Woodruff (2016), §3.1.
atlas: frequent-directions-mergeability (partial)-/
theorem frequentDirections_mergeMany_certificate (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    (blocks : List (Matrix (Fin d) (Fin d) 𝕜 × FrequentDirectionsState ℓ d 𝕜))
    (hBlocks : ∀ p ∈ blocks,
      CovarianceLossCertificate ℓ p.1 (p.2.sketchᴴ * p.2.sketch) p.2.loss) :
    CovarianceLossCertificate ℓ (blocks.map Prod.fst).sum
      ((FrequentDirectionsState.mergeMany hℓ (blocks.map Prod.snd)).sketchᴴ *
        (FrequentDirectionsState.mergeMany hℓ (blocks.map Prod.snd)).sketch)
      (FrequentDirectionsState.mergeMany hℓ (blocks.map Prod.snd)).loss := by
  have hBefore : CovarianceLossCertificate ℓ (blocks.map Prod.fst).sum
      (blocks.map (fun p => p.2.sketchᴴ * p.2.sketch)).sum
      (blocks.map (fun p => p.2.loss)).sum := by
    induction blocks with
    | nil => simpa using CovarianceLossCertificate.zero ℓ (0 : Matrix (Fin d) (Fin d) 𝕜)
    | cons p ps ih =>
      have hp := hBlocks p (by simp)
      have ht := ih (by intro q hq; exact hBlocks q (by simp [hq]))
      simpa only [List.map_cons, List.sum_cons] using hp.add ht
  let rows := (blocks.map Prod.snd).flatMap (fun s => List.ofFn (fun i => s.sketch i))
  have hGram : rowStreamGram rows = (blocks.map (fun p => p.2.sketchᴴ * p.2.sketch)).sum := by
    clear hBefore hBlocks
    dsimp only [rows]
    induction blocks with
    | nil => rfl
    | cons p ps ih =>
      simpa only [List.map_cons, List.flatMap_cons, rowStreamGram_append,
        rowStreamGram_ofFn, List.sum_cons] using congrArg (p.2.sketchᴴ * p.2.sketch + ·) ih
  have hNode := (frequentDirections_run_invariant hℓ hℓd rows).certificate
  rw [hGram] at hNode
  simpa only [FrequentDirectionsState.mergeMany, List.map_map, Function.comp_def] using
    hBefore.trans hNode

/-- Any finite binary merge shape, with a possibly empty row block at each leaf. -/
inductive FrequentDirectionsMergeTree (d : ℕ) (𝕜 : Type*) where
  | leaf (rows : List (Fin d → 𝕜))
  | node (left right : FrequentDirectionsMergeTree d 𝕜)

namespace FrequentDirectionsMergeTree

/-- The original row stream represented by the leaves, in their tree order. -/
def rows : FrequentDirectionsMergeTree d 𝕜 → List (Fin d → 𝕜)
  | .leaf xs => xs
  | .node left right => left.rows ++ right.rows

/-- Run each leaf block and perform the actual fixed-capacity merge at every node. -/
def run (hℓ : 0 < ℓ) : FrequentDirectionsMergeTree d 𝕜 → FrequentDirectionsState ℓ d 𝕜
  | .leaf xs => FrequentDirectionsState.run hℓ xs
  | .node left right => (left.run hℓ).merge hℓ (right.run hℓ)

/-- Every actual finite merge tree preserves the source covariance certificate with
capacity independent of the depth and shape of the tree.
Ghashami–Liberty–Phillips–Woodruff (2016), §3.1.
atlas: frequent-directions-mergeability (partial)-/
theorem certificate (tree : FrequentDirectionsMergeTree d 𝕜) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    CovarianceLossCertificate ℓ (rowStreamGram tree.rows)
      ((tree.run hℓ).sketchᴴ * (tree.run hℓ).sketch) (tree.run hℓ).loss := by
  induction tree with
  | leaf xs => exact (frequentDirections_run_invariant hℓ hℓd xs).certificate
  | node left right ihL ihR =>
    simpa only [rows, run, rowStreamGram_append] using
      frequentDirections_merge_certificate hℓ hℓd ihL ihR

/-- The merged sketch retains the same covariance-tail constant as one stream, with
no multiplicative loss depending on the merge tree depth.
atlas: frequent-directions-mergeability (partial) -/
theorem specNorm_sub_gram_le (tree : FrequentDirectionsMergeTree d 𝕜)
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) {k : ℕ} (hkℓ : k < ℓ) :
    specNorm (rowStreamGram tree.rows - (tree.run hℓ).sketchᴴ * (tree.run hℓ).sketch) ≤
      bestRankFrobSq (Matrix.ofRowList tree.rows) k / ((ℓ - k : ℕ) : ℝ) := by
  have hc := tree.certificate hℓ hℓd
  rw [rowStreamGram_eq_gram_ofRowList] at hc ⊢
  exact hc.specNorm_sub_gram_le_bestRankFrobSq_div hkℓ (by simpa using (hkℓ.le.trans hℓd))

/-- Every leading right projector of the actual merged summary gives the same relative
projection bound, independently of the merge tree depth or leaf block sizes.
Ghashami–Liberty–Phillips–Woodruff (2016), §3.1 and Theorem 1.2.
atlas: frequent-directions-mergeability (partial)-/
theorem frobSq_error_le (tree : FrequentDirectionsMergeTree d 𝕜)
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜}
    (hB : IsSVD (tree.run hℓ).sketch U V) {k : ℕ} (hkℓ : k < ℓ) :
    frobSq (Matrix.ofRowList tree.rows - Matrix.ofRowList tree.rows * hB.leadingRightProjector k) ≤
      (ℓ : ℝ) / ((ℓ - k : ℕ) : ℝ) * bestRankFrobSq (Matrix.ofRowList tree.rows) k := by
  have hc := tree.certificate hℓ hℓd
  rw [rowStreamGram_eq_gram_ofRowList] at hc
  exact CovarianceLossCertificate.frobSq_error_le_capacity_mul_bestRankFrobSq_div_of_isSVD
    hB hc hkℓ (by simpa using (hkℓ.le.trans hℓd))

end FrequentDirectionsMergeTree
end NLAlib
