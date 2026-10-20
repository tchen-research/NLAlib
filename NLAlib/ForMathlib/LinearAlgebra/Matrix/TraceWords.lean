import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite closed-index expansions of ordered matrix trace words

Every matrix product is ordered by `List.ofFn`; only the resulting scalar entry
products use commutativity. The boundary-chain form covers its length-zero
interior and the cyclic form requires one or more matrix factors.
-/

noncomputable section
open scoped BigOperators
namespace Matrix

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem sum_fin_snoc {m : ℕ} (F : (Fin (m + 1) → n) → R) :
    (∑ v, F v) = ∑ v : Fin m → n, ∑ j : n, F (Fin.snoc v j) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => n)).sum_comp F,
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The trace of an ordered matrix word with a boundary factor is the exact
finite sum of its closed entry chains. The case of zero interior factors is
the usual trace sum of the boundary matrix. -/
theorem trace_mul_list_ofFn_prod_eq_sum {m : ℕ}
    (B : Matrix n n R) (A : Fin m → Matrix n n R) :
    (B * (List.ofFn A).prod).trace =
      ∑ v : Fin (m + 1) → n,
        B (v (Fin.last m)) (v 0) *
          ∏ r : Fin m, A r (v r.castSucc) (v r.succ) := by
  classical
  induction m generalizing B with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil,
      Fin.prod_univ_zero, mul_one]
    exact ((Equiv.funUnique (Fin 1) n).sum_comp (fun i => B i i)).symm
  | succ m ih =>
    let A' : Fin m → Matrix n n R := fun r => A r.castSucc
    have heq : (B * (List.ofFn A).prod).trace =
        ((A (Fin.last m) * B) * (List.ofFn A').prod).trace := by
      rw [List.ofFn_succ', List.prod_concat, Matrix.trace_mul_cycle', ← Matrix.mul_assoc]
    rw [heq, ih, sum_fin_snoc (m := m + 1)]
    simp only [Matrix.mul_apply, Finset.sum_mul, Fin.prod_univ_castSucc,
      ← Fin.castSucc_succ, Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.snoc_apply_zero]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [A']
    ring

/-- A nonempty ordered matrix trace word is the sum over all assignments of
its cyclic vertices, with the final factor joining the last vertex to zero. -/
theorem trace_list_ofFn_prod_eq_sum {m : ℕ} (A : Fin (m + 1) → Matrix n n R) :
    (List.ofFn A).prod.trace =
      ∑ v : Fin (m + 1) → n,
        (∏ r : Fin m, A r.castSucc (v r.castSucc) (v r.succ)) *
          A (Fin.last m) (v (Fin.last m)) (v 0) := by
  rw [List.ofFn_succ', List.prod_concat, Matrix.trace_mul_comm,
    trace_mul_list_ofFn_prod_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_comm _ _

/-- The cyclic finite-word trace expansion uses the native full-cycle
permutation `finRotate`, in the same order as the original matrix word. -/
theorem trace_list_ofFn_prod_eq_sum_cyclic {m : ℕ}
    (A : Fin (m + 1) → Matrix n n R) :
    (List.ofFn A).prod.trace =
      ∑ v : Fin (m + 1) → n,
        ∏ r : Fin (m + 1), A r (v r) (v (finRotate (m + 1) r)) := by
  rw [trace_list_ofFn_prod_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fin.prod_univ_castSucc, finRotate_last]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  have hr : finRotate (m + 1) r.castSucc = r.succ := finRotate_of_lt r.isLt
  rw [hr]

/-- Rotating an ordered matrix list preserves its actual ordinary trace.
No nonempty dimension or list assumption is needed. Source: trace cyclicity. -/
theorem trace_list_prod_rotate {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
    (L : List (Matrix n n R)) (s : ℕ) :
    (L.rotate s).prod.trace = L.prod.trace := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append, Matrix.trace_mul_comm,
    List.prod_take_mul_prod_drop]

end Matrix
