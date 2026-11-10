-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
-- Axiom audit for the analytic-bridge refutation and vacuity checks.
-- Every listed declaration must depend only on propext, Classical.choice, Quot.sound.
-- (The open target `analytic_bridge_unconditional` itself is intentionally NOT listed:
-- it still carries its marked open-target placeholder proof.)
import FrohmanianTetherConditional.AnalyticBridgeRefutation

#print axioms clayB_implies_bkm_integrable
#print axioms integral_gronwall_bound
#print axioms AnalyticBridgeRefutation.analytic_bridge_unconditional_false
#print axioms AnalyticBridgeRefutation.analytic_bridge_target_statement_false
#print axioms AnalyticBridgeRefutation.analytic_bridge_fails_at_zero
#print axioms AnalyticBridgeRefutation.not_nonempty_BKMCriterion
#print axioms AnalyticBridgeRefutation.BKMCriterion_elim
#print axioms AnalyticBridgeRefutation.hypothesisB_holds
#print axioms AnalyticBridgeRefutation.clayStatementB_holds
