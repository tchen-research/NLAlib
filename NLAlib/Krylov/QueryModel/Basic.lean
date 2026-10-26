import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Adaptive matrix-vector query algorithms

A query algorithm is independent of its oracle: its next query depends only on the finite
history of responses. Randomized algorithms are seed-indexed families of these objects.
The two-sided matrix oracle records products with a matrix and its adjoint separately;
zero queries cost no product. The rank of either query span is bounded by its product count.

The finite transcript construction and proofs are adapted from the Apache-2.0 NLAlib
`LowerBounds/QueryModel/Basic.lean` source (NLA-lib/NLAlib, commit
79f8cc2f74523a30d1d53316542b826018e245a4). This module has no dependency on that repository.
Source: Simchowitz, El Alaoui and Recht (2018), the adaptive matrix-vector query model.
This file supplies the model and indistinguishability lemmas; algorithm realizations are separate.
atlas: matvec-query-model (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A deterministic **adaptive query algorithm** with `q` queries to an oracle `Q → R` and output
in `β`. The `i`-th query is `query i` applied to the first `i` responses; the output is `output`
applied to all `q` responses. Queries with index $i \ge q$ are never made. A randomized algorithm is
a family `S → QueryAlgorithm Q R q β` indexed by a seed (`QueryAlgorithm.IsMeasurableFamily`). -/
structure QueryAlgorithm (Q R : Type*) (q : ℕ) (β : Type*) where
  /-- The `i`-th query as a function of the first `i` responses. -/
  query : (i : ℕ) → (Fin i → R) → Q
  /-- The output as a function of the `q` responses. -/
  output : (Fin q → R) → β

/-- The **two-sided matrix–vector oracle** of $\mathbf{A} \in \Bbbk^{m \times n}$: the query
$(\mathbf{x}, \mathbf{y})$ returns $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$,
one product with $\mathbf{A}$ (the right part) and one with $\mathbf{A}^{\mathsf{H}}$ (the left
part). A zero part returns zero and costs nothing (`QueryAlgorithm.rightCount`,
`QueryAlgorithm.leftCount`). -/
def twoSidedMulVec {𝕜 m n : Type*} [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring 𝕜] [Star 𝕜]
    (A : Matrix m n 𝕜) (v : (n → 𝕜) × (m → 𝕜)) : (m → 𝕜) × (n → 𝕜) :=
  (A *ᵥ v.1, Aᴴ *ᵥ v.2)

namespace QueryAlgorithm

variable {Q R β : Type*} {q : ℕ}

/-- The first `i` responses of the algorithm run against the oracle `f`, by recursion on `i`:
the next query is computed from the responses so far and its response appended. -/
def history (alg : QueryAlgorithm Q R q β) (f : Q → R) : (i : ℕ) → Fin i → R
  | 0 => Fin.elim0
  | i + 1 => Fin.snoc (α := fun _ => R) (history alg f i) (f (alg.query i (history alg f i)))

/-- The `i`-th query the algorithm makes when run against the oracle `f`. -/
def queryAt (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) : Q :=
  alg.query i (alg.history f i)

/-- The **transcript**: the `q` responses of the algorithm run against the oracle `f`. -/
def transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) : Fin q → R :=
  alg.history f q

/-- The output of the algorithm run against the oracle `f`. -/
def run (alg : QueryAlgorithm Q R q β) (f : Q → R) : β :=
  alg.output (alg.transcript f)

/-- The queries recomputed from a list `τ` of `q` responses: the `j`-th is `query j` applied to
the first `j` entries of `τ`. On the transcript they are the queries made
(`QueryAlgorithm.queryAt_eq_queries_transcript`). -/
def queries (alg : QueryAlgorithm Q R q β) (τ : Fin q → R) (j : Fin q) : Q :=
  alg.query j fun l => τ (Fin.castLE j.isLt.le l)

/-- For vector queries, the **query matrix** of a transcript `τ`: its column `j` is the `j`-th
query `alg.queries τ j`. -/
def queryMatrix {𝕜 n : Type*} (alg : QueryAlgorithm (n → 𝕜) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => alg.queries τ j r

section TwoSided

variable {𝕜 m n : Type*}

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **right query matrix**
of a transcript `τ`: its column `j` is the right part $\mathbf{x}_j$ of the `j`-th query. -/
def rightQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).1 r

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **left query matrix** of
a transcript `τ`: its column `j` is the left part $\mathbf{y}_j$ of the `j`-th query. -/
def leftQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix m (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).2 r

variable [Zero 𝕜]

/-- The **number of right products** of a transcript `τ`: the rounds whose right part
$\mathbf{x}_j$ is nonzero, each one product $\mathbf{A}\mathbf{x}_j$. A budget of $q_R$ products
with $\mathbf{A}$ is the hypothesis `∀ τ, alg.rightCount τ ≤ q_R`. -/
noncomputable def rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).1 ≠ 0}.ncard

/-- The **number of left products** of a transcript `τ`: the rounds whose left part
$\mathbf{y}_j$ is nonzero, each one product $\mathbf{A}^{\mathsf{H}}\mathbf{y}_j$. A budget of
$q_L$ products with $\mathbf{A}^{\mathsf{H}}$ is the hypothesis `∀ τ, alg.leftCount τ ≤ q_L`. -/
noncomputable def leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).2 ≠ 0}.ncard

/-- A pair-query algorithm is **one-sided** when it makes no product with
$\mathbf{A}^{\mathsf{H}}$: every left part is zero, for every transcript. -/
def IsOneSided (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) : Prop :=
  ∀ τ, alg.leftCount τ = 0

end TwoSided

/-- The algorithm **truncated** to its first `i` queries, with no output: its transcript is the
history of length `i` (`QueryAlgorithm.transcript_truncate`). Inductions over the number of
queries (deferred decision) run through it. -/
def truncate (alg : QueryAlgorithm Q R q β) (i : ℕ) : QueryAlgorithm Q R i Unit where
  query := alg.query
  output _ := ()

/-- The truncated algorithm has the same histories. -/
@[simp]
theorem history_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i j : ℕ) :
    (alg.truncate i).history f j = alg.history f j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [history, history, ih]; rfl

/-- The transcript of the truncated algorithm is the history of length `i`. -/
@[simp]
theorem transcript_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) :
    (alg.truncate i).transcript f = alg.history f i :=
  history_truncate alg f i i

/-- A query algorithm is **non-adaptive** when each of its `q` queries is the same for every
history: the queries are fixed in advance (the sketching model). For pair queries both parts are
fixed in advance: a one-pass algorithm with $\ell$ products with $\mathbf{A}$ and $p$ with
$\mathbf{A}^{\mathsf{H}}$ is `IsNonAdaptive` with `rightCount ≤ ℓ` and `leftCount ≤ p`. -/
def IsNonAdaptive (alg : QueryAlgorithm Q R q β) : Prop :=
  ∀ i < q, ∀ h h' : Fin i → R, alg.query i h = alg.query i h'

/-- Responses are oracle values: the `j`-th of the first `i` responses of an algorithm run
against the oracle $f$ is $f$ at the `j`-th query, $h_j = f(x_j)$. -/
theorem history_apply (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) (j : Fin i) :
    alg.history f i j = f (alg.queryAt f j) := by
  induction i with
  | zero => exact j.elim0
  | succ i ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [history, Fin.snoc_last]
      rfl
    · rw [history, Fin.snoc_castSucc, ih]
      rfl

/-- Entries of a history do not depend on the length of the history. -/
private theorem history_eq_history (alg : QueryAlgorithm Q R q β) (f : Q → R) {n m j : ℕ}
    (hn : j < n) (hm : j < m) : alg.history f n ⟨j, hn⟩ = alg.history f m ⟨j, hm⟩ := by
  rw [history_apply, history_apply]

/-- The queries made are the queries of the transcript: the `j`-th query of an algorithm run
against $f$ is `queries` evaluated at its transcript. -/
theorem queryAt_eq_queries_transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) (j : Fin q) :
    alg.queryAt f j = alg.queries (alg.transcript f) j := by
  unfold queryAt queries transcript
  congr 1
  funext l
  exact history_eq_history alg f l.isLt (l.isLt.trans j.isLt)

/-- Indistinguishability: if a second oracle $g$ agrees with $f$ at every query the algorithm
makes against $f$, then the algorithm makes the same queries against $g$ and gets the same
transcript. This is the deterministic half of every adversary and deferred-decision argument. -/
theorem transcript_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.transcript g = alg.transcript f := by
  have key : ∀ i, i ≤ q → alg.history g i = alg.history f i := by
    intro i
    induction i with
    | zero => intro _; funext j; exact j.elim0
    | succ i ih =>
      intro hi
      have hq : i < q := hi
      have hgf := h ⟨i, hq⟩
      rw [← queryAt_eq_queries_transcript alg f ⟨i, hq⟩] at hgf
      unfold history
      rw [ih (by omega)]
      congr 1
  exact key q le_rfl

/-- Indistinguishability of outputs: if $g$ agrees with $f$ at every query the algorithm makes
against $f$, the algorithm outputs the same value against both. -/
theorem run_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.run g = alg.run f :=
  congrArg alg.output (transcript_eq_of_forall_apply_queries_eq alg h)

/-- Non-adaptive queries are fixed: a non-adaptive algorithm makes the same queries whatever
the responses, so `queries` does not depend on the transcript. -/
theorem IsNonAdaptive.queries_eq {alg : QueryAlgorithm Q R q β} (h : alg.IsNonAdaptive)
    (τ τ' : Fin q → R) : alg.queries τ = alg.queries τ' := by
  funext j
  exact h j j.isLt _ _

/-! ### Measurability -/
section Count

variable {𝕜 m n : Type*} [Field 𝕜]

/-- A matrix whose columns vanish outside `S` has rank at most `S.ncard`. -/
private lemma rank_le_ncard_of_col_eq_zero {m : Type*} (M : Matrix m (Fin q) 𝕜)
    (S : Set (Fin q)) (h : ∀ j ∉ S, ∀ r, M r j = 0) : M.rank ≤ S.ncard := by
  classical
  have hS : S.Finite := Set.toFinite S
  have : Fintype S := hS.fintype
  let N : Matrix m S 𝕜 := fun r j => M r j
  let P : Matrix S (Fin q) 𝕜 := fun j k => if (j : Fin q) = k then 1 else 0
  have hMNP : M = N * P := by
    ext r k
    rw [Matrix.mul_apply]
    by_cases hk : k ∈ S
    · rw [Finset.sum_eq_single (⟨k, hk⟩ : S)]
      · simp [N, P]
      · intro b _ hb
        have : (b : Fin q) ≠ k := fun e => hb (Subtype.ext e)
        simp [N, P, this]
      · simp
    · rw [h k hk r]
      refine Eq.symm (Finset.sum_eq_zero fun b _ => ?_)
      have : (b : Fin q) ≠ k := fun e => hk (e ▸ b.2)
      simp [P, this]
  calc M.rank = (N * P).rank := by rw [← hMNP]
    _ ≤ N.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card S := Matrix.rank_le_card_width N
    _ = S.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The right query span is bounded by the number of right products: the rank of the right
query matrix is at most the number of rounds with a nonzero right part. -/
theorem rank_rightQueryMatrix_le_rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.rightQueryMatrix τ).rank ≤ alg.rightCount τ :=
  rank_le_ncard_of_col_eq_zero _ _ fun j hj r => by
    simp only [Set.mem_ofPred_eq, not_not] at hj
    simp [QueryAlgorithm.rightQueryMatrix, hj]

/-- The left query span is bounded by the number of left products: the rank of the left query
matrix is at most the number of rounds with a nonzero left part. -/
theorem rank_leftQueryMatrix_le_leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.leftQueryMatrix τ).rank ≤ alg.leftCount τ :=
  rank_le_ncard_of_col_eq_zero _ _ fun j hj r => by
    simp only [Set.mem_ofPred_eq, not_not] at hj
    simp [QueryAlgorithm.leftQueryMatrix, hj]

end Count

end QueryAlgorithm
end NLAlib
