/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

import Solution
import Lean

/-!
Print statements and audit the transitive axioms of every declaration originating
in the authored library, including definitions, instances and generated
auxiliaries. Reject any axiom outside the three standard logical axioms.
Challenge is excluded from this proof environment.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      if (`LpSelfSimilar).isPrefixOf env.header.moduleNames[idx]! then acc.push name else acc
  if names.isEmpty then throwError "The authored proof library was not imported."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Forbidden axioms in {name}: {unexpected}"
    if let some declaration := env.find? name then
      logInfo m!"DECLARATION {name}: {declaration.type}"
    logInfo m!"AXIOM_AUDIT {name}: {axioms}"
  logInfo m!"AXIOM_AUDIT_PASS {names.size} authored declarations"

#print LpSelfSimilar.self_similar_higher_integrability
#print LpSelfSimilar.algebraic_bernoulli_convolution_continuous_density_non_strict
#print LpSelfSimilar.algebraic_bernoulli_convolution_cubic
#print LpSelfSimilar.rational_bernoulli_convolution_continuous_density_cubic
#print LpSelfSimilar.bernoulli_convolution_one_sub_inv_continuous_density_cubic_int
#print LpSelfSimilar.Space
#print LpSelfSimilar.Similarity
#print LpSelfSimilar.Bernoulli.sign
#print LpSelfSimilar.Bernoulli.series
#print LpSelfSimilar.Bernoulli.fairDigit
#print LpSelfSimilar.Bernoulli.digitSpace
#print LpSelfSimilar.Bernoulli.convolution
#print LpSelfSimilar.Algebraic.primitiveRepresentative
#print LpSelfSimilar.Algebraic.integerMinimalPolynomial
#print LpSelfSimilar.Algebraic.algebraicDegree
#print LpSelfSimilar.Algebraic.mahlerMeasure
