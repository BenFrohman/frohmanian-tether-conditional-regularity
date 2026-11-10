-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
-- Axiom audit for: (i) the LEGACY refutation and vacuity checks, (ii) the genuine
-- classical Navier–Stokes encoding `ClassicalNS`, (iii) the lifespan-corrected triple
-- architecture. Every listed declaration must depend only on propext,
-- Classical.choice, Quot.sound. The OPEN target
-- `ClassicalNS.analytic_bridge_unconditional` is intentionally NOT listed.
import FrohmanianTetherConditional.AnalyticBridgeRefutation
import FrohmanianTetherConditional.ClassicalNS
import FrohmanianTetherConditional.FrohmanianTripleArchitectureLifespan

-- (i) LEGACY file: sound lemmas, refutation, vacuity witnesses
#print axioms clayB_implies_bkm_integrable
#print axioms integral_gronwall_bound
#print axioms AnalyticBridgeRefutation.analytic_bridge_unconditional_false
#print axioms AnalyticBridgeRefutation.analytic_bridge_target_statement_false
#print axioms AnalyticBridgeRefutation.analytic_bridge_fails_at_zero
#print axioms AnalyticBridgeRefutation.not_nonempty_BKMCriterion
#print axioms AnalyticBridgeRefutation.BKMCriterion_elim
#print axioms AnalyticBridgeRefutation.hypothesisB_holds
#print axioms AnalyticBridgeRefutation.clayStatementB_holds

-- (ii) Genuine encoding: non-vacuity
#print axioms ClassicalNS.isCompact_cube
#print axioms ClassicalNS.gradLinf_nonneg
#print axioms ClassicalNS.const_isClassicalNS
#print axioms ClassicalNS.zeroSolution_global
#print axioms ClassicalNS.nonempty_NSSolution_zero
#print axioms ClassicalNS.zero_field_is_global
#print axioms ClassicalNS.old_counterexample_invalid
#print axioms ClassicalNS.linear_in_time_not_NS
#print axioms ClassicalNS.gradLinf_continuousOn
#print axioms ClassicalNS.bkm_conclusion_of_global
#print axioms ClassicalNS.kp_trivial
#print axioms ClassicalNS.analyticBridge_conclusion_zeroSolution
-- (ii) Genuine encoding: proved and conditional theorems
#print axioms ClassicalNS.global_implies_gradIntegral_finite
#print axioms ClassicalNS.gradIntegral_finite_implies_global
#print axioms ClassicalNS.clayB_iff_gradIntegral_finite
#print axioms ClassicalNS.formB_implies_clayB
#print axioms ClassicalNS.analyticBridge_of_formB
#print axioms ClassicalNS.gronwall_differential_bound
#print axioms ClassicalNS.integral_gronwall_bound
#print axioms ClassicalNS.formB_Hs_bound

-- (iii) Lifespan-corrected triple architecture
#print axioms FrohmanianTripleArchitectureLifespan.primitive_bounded
#print axioms FrohmanianTripleArchitectureLifespan.hypothesisB_implies_clayStatementB
#print axioms FrohmanianTripleArchitectureLifespan.three_way_equivalence
#print axioms FrohmanianTripleArchitectureLifespan.clayStatementB_zeroModel
#print axioms FrohmanianTripleArchitectureLifespan.integral_inv_one_sub
#print axioms FrohmanianTripleArchitectureLifespan.blowupModel_not_clay
#print axioms FrohmanianTripleArchitectureLifespan.clayStatementB_not_automatic
#print axioms FrohmanianTripleArchitectureLifespan.hypothesisB_not_automatic
#print axioms FrohmanianTripleArchitectureLifespan.old_trivialization_fails
