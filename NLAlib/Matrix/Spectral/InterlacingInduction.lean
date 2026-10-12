import NLAlib.ForMathlib.Order.InterlacingDeletion
import NLAlib.Matrix.Spectral.InterlacingRestoration
/-!
# Extending strict-spectrum constructions to weak repeated interlacing

An equal adjacent original eigenvalue forces one target root. Remove that
pair, use induction, and restore the coordinate with zero coupling.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A rank-one converse construction for strictly increasing original
spectra extends to arbitrary weakly increasing spectra. Repeated target
roots and empty lists are retained. Horn–Johnson 2013, Theorem 4.3.26;
the supplied strict-case construction is used only after all forced
repeated original roots have been removed. -/
theorem rank_one_interlacing_converse_of_strict_cases
    (hstrict : ∀ (n : ℕ) (d b : Fin n → ℝ), StrictMono d → Monotone b →
      (∀ i, d i ≤ b i) → (∀ i j, i.val + 1 = j.val → b i ≤ d j) →
      ∃ v : Fin n → ℝ, (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
        ∏ j, (X - C (b j))) :
    ∀ (n : ℕ) (d b : Fin n → ℝ), Monotone d → Monotone b →
      (∀ i, d i ≤ b i) → (∀ i j, i < j → b i ≤ d j) →
      ∃ v : Fin n → ℝ, (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
        ∏ j, (X - C (b j)) := by
  intro n
  induction n with
  | zero =>
    intro d b _ _ _ _
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro d b hd hb hlo hhi
    by_cases hs : StrictMono d
    · exact hstrict (n + 1) d b hs hb hlo (fun i j hij => hhi i j (by omega))
    · obtain ⟨i, hi⟩ := exists_adjacent_eq_of_monotone_not_strictMono d hd hs
      let p := i.castSucc
      have hroot : b p = d p := rank_one_interlacing_forced_root d b hlo hhi i hi
      obtain ⟨v, hv⟩ := ih (d ∘ p.succAbove) (b ∘ p.succAbove)
        (hd.comp (Fin.strictMono_succAbove p).monotone)
        (hb.comp (Fin.strictMono_succAbove p).monotone)
        (fun j => hlo (p.succAbove j))
        (fun j l hjl => hhi _ _ (Fin.strictMono_succAbove p hjl))
      refine ⟨p.insertNth 0 v, ?_⟩
      rw [charpoly_diagonal_add_vecMulVec_insertNth, hv,
        Fin.prod_univ_succAbove (fun j => X - C (b j)) p, hroot]
      rfl

/-- A bordered converse construction for strictly increasing original
spectra extends to arbitrary weak interlacing with repeated roots.
The deleted target root is exactly the repeated original root, and its
coordinate is restored with zero coupling. Horn–Johnson 2013,
Theorem 4.3.21; empty and singleton cases are included. -/
theorem bordered_interlacing_converse_of_strict_cases
    (hstrict : ∀ (n : ℕ) (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ),
      StrictMono d → Monotone b → (∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) →
      ∃ v : Fin n → ℝ, ∃ a : ℝ,
        (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
          (Matrix.replicateRow (Fin 1) v) (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
          ∏ j, (X - C (b j))) :
    ∀ (n : ℕ) (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ),
      Monotone d → Monotone b → (∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) →
      ∃ v : Fin n → ℝ, ∃ a : ℝ,
        (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
          (Matrix.replicateRow (Fin 1) v) (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
          ∏ j, (X - C (b j)) := by
  intro n
  induction n with
  | zero =>
    intro d b _ hb h
    exact hstrict 0 d b (by intro i; exact Fin.elim0 i) hb h
  | succ n ih =>
    intro d b hd hb h
    by_cases hs : StrictMono d
    · exact hstrict (n + 1) d b hs hb h
    · obtain ⟨i, hi⟩ := exists_adjacent_eq_of_monotone_not_strictMono d hd hs
      let p := i.castSucc
      have hroot : b p.succ = d p := bordered_interlacing_forced_root d b h i hi
      obtain ⟨v, a, hva⟩ := ih (d ∘ p.succAbove) (b ∘ p.succ.succAbove)
        (hd.comp (Fin.strictMono_succAbove p).monotone)
        (hb.comp (Fin.strictMono_succAbove p.succ).monotone)
        (bordered_interlacing_succAbove d b hb h p)
      refine ⟨p.insertNth 0 v, a, ?_⟩
      rw [charpoly_bordered_diagonal_insertNth, hva,
        Fin.prod_univ_succAbove (fun j => X - C (b j)) p.succ, hroot]
      rfl

end NLAlib
