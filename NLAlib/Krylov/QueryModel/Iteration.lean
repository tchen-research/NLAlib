import NLAlib.Krylov.QueryModel.Basic

/-!
# Oracle realization of finite state recurrences

A state update that uses the oracle only through one response has a genuine adaptive
query implementation. The query strategy and update are fixed before the oracle is supplied.
The theorem includes zero steps and total updates, so freezing after successful termination
does not require a separate algorithm or an uncharged access to the matrix.

atlas: matvec-query-model (partial)
-/

namespace NLAlib.QueryAlgorithm

variable {S Q R : Type*}

/-- Change only the final processing of a transcript, without making additional queries. -/
def withOutput {q : ℕ} {α β : Type*} (alg : QueryAlgorithm Q R q α)
    (output : (Fin q → R) → β) : QueryAlgorithm Q R q β where
  query := alg.query
  output := output

/-- Free final processing leaves every oracle response unchanged. -/
@[simp] theorem history_withOutput {q : ℕ} {α β : Type*} (alg : QueryAlgorithm Q R q α)
    (output : (Fin q → R) → β) (f : Q → R) (i : ℕ) :
    (alg.withOutput output).history f i = alg.history f i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [history, history, ih]; rfl

/-- Final processing of a transcript is free in the matrix-vector query model. -/
theorem run_withOutput {q : ℕ} {α β : Type*} (alg : QueryAlgorithm Q R q α)
    (output : (Fin q → R) → β) (f : Q → R) :
    (alg.withOutput output).run f = output (alg.transcript f) := by
  change output ((alg.withOutput output).history f q) = output (alg.history f q)
  rw [history_withOutput]

/-- Make one initialization query, then choose the remaining strategy from its response.
The total budget includes this first query. -/
def prependQuery {q : ℕ} {β : Type*} (first : Q) (next : R → QueryAlgorithm Q R q β) :
    QueryAlgorithm Q R (q + 1) β where
  query
    | 0, _ => first
    | i + 1, h => (next (h 0)).query i (fun j => h j.succ)
  output h := (next (h 0)).output (fun j => h j.succ)

/-- The transcript after initialization is the first response followed by the remaining
strategy's transcript. -/
theorem history_prependQuery {q : ℕ} {β : Type*} (first : Q)
    (next : R → QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) :
    (prependQuery first next).history f (i + 1) =
      Fin.cons (f first) ((next (f first)).history f i) := by
  induction i with
  | zero => ext j; fin_cases j; rfl
  | succ i ih =>
    rw [history, ih]
    change Fin.snoc (α := fun _ => R) (Fin.cons (f first) ((next (f first)).history f i))
      (f ((next (f first)).query i ((next (f first)).history f i))) =
      Fin.cons (f first) (Fin.snoc (α := fun _ => R) ((next (f first)).history f i)
        (f ((next (f first)).query i ((next (f first)).history f i))))
    exact (Fin.cons_snoc_eq_snoc_cons _ _ _).symm

/-- Running the initialization query and then the selected strategy charges `q + 1`
queries and has exactly the expected semantics. -/
theorem run_prependQuery {q : ℕ} {β : Type*} (first : Q)
    (next : R → QueryAlgorithm Q R q β) (f : Q → R) :
    (prependQuery first next).run f = (next (f first)).run f := by
  change (next ((prependQuery first next).history f (q + 1) 0)).output
    (fun j => (prependQuery first next).history f (q + 1) j.succ) = _
  rw [history_prependQuery]
  rfl

/-- Reconstruct a state from an initial state and a finite history of responses. -/
def replay (initial : S) (update : S → R → S) : {i : ℕ} → (Fin i → R) → S
  | 0, _ => initial
  | i + 1, h => update (replay initial update (fun j : Fin i => h j.castSucc)) (h (Fin.last i))

/-- A state recurrence with one oracle response per step, compiled to an adaptive query
algorithm. Neither `query` nor `update` has access to the oracle. -/
def ofState (initial : S) (query : S → Q) (update : S → R → S) (q : ℕ) :
    QueryAlgorithm Q R q S where
  query _ h := query (replay initial update h)
  output h := replay initial update h

/-- Replaying actual responses reconstructs the corresponding oracle-driven state. -/
theorem replay_history_ofState (initial : S) (query : S → Q) (update : S → R → S)
    (q : ℕ) (f : Q → R) (i : ℕ) :
    replay initial update ((ofState initial query update q).history f i) =
      (fun s => update s (f (query s)))^[i] initial := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [history, replay, Fin.snoc_castSucc, Fin.snoc_last]
    change update (replay initial update ((ofState initial query update q).history f i))
      (f (query (replay initial update ((ofState initial query update q).history f i)))) = _
    rw [ih, Function.iterate_succ_apply']

/-- Exact realization of a finite recurrence using `q` adaptive queries, including `q = 0`.
atlas: matvec-query-model (partial) -/
theorem run_ofState (initial : S) (query : S → Q) (update : S → R → S)
    (q : ℕ) (f : Q → R) :
    (ofState initial query update q).run f =
      (fun s => update s (f (query s)))^[q] initial :=
  replay_history_ofState initial query update q f q

/-- The next query is the query of the current state. -/
theorem queryAt_ofState (initial : S) (query : S → Q) (update : S → R → S)
    (q : ℕ) (f : Q → R) (i : ℕ) :
    (ofState initial query update q).queryAt f i =
      query ((fun s => update s (f (query s)))^[i] initial) := by
  change query (replay initial update ((ofState initial query update q).history f i)) = _
  rw [replay_history_ofState]

end NLAlib.QueryAlgorithm
