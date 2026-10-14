import NLAlib.Sketching.Structured.KhatriRaoGrowth
import NLAlib.Sketching.Structured.KhatriRaoSigns
import NLAlib.Sketching.Structured.KhatriRaoLowerGrowth

/-! Audit the complete dependencies of the sharp-growth public contracts. -/

open Lean Elab Command

run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names := [
    ``NLAlib.measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le,
    ``NLAlib.measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le_of_rank_log_budget,
    ``NLAlib.measureReal_not_isSubspaceEmbedding_khatriRaoSketch_rademacher_le,
    ``NLAlib.one_sub_exp_neg_sqrt_le_measureReal_not_isSubspaceEmbedding_of_le_lower_growth,
    ``NLAlib.hasOrthonormalCols_khatriRaoCommonIsometry,
    ``NLAlib.measurePreserving_khatriRaoCommonFactors]
  for name in names do
    let axioms ← collectAxioms name
    let extra := axioms.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do
      logError m!"{name} depends on forbidden axioms {extra}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"audited {names.length} sharp Khatri-Rao contracts; no deferred assumptions"
