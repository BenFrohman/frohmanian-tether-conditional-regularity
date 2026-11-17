/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Kernel/axiom audit: every listed declaration must depend only on
-- propext, Classical.choice and Quot.sound.
import FrohmanianTetherConditional

/-!
# scripts.PrintAxioms

Machine-checked Lean 4 module.
-/

open FrohmanianTripleArchitecture

#print axioms projPerp_self
#print axioms inner_projPerp_self
#print axioms tether_degenerate_H
#print axioms tether_symmetric
#print axioms tether_nonpos
#print axioms totalMetriplectic_symm
#print axioms totalMetriplectic_flow_equals_unmodified_NS
#print axioms abs_dot3_le
#print axioms triple_product_cycle
#print axioms abs_alignmentKernel_le
#print axioms constantin_fefferman_desingularization
#print axioms gronwall_differential_bound
#print axioms hypothesisB_implies_clayStatementB
#print axioms three_way_equivalence
#print axioms ClassicalEstimatePieces.sym_part_frobenius_le
#print axioms ClassicalEstimatePieces.sym_part_frobenius_le_sqrt
#print axioms ClassicalEstimatePieces.antisym_mul_curl_eq_zero
#print axioms ClassicalEstimatePieces.grad_mul_curl_eq_sym_mul_curl
#print axioms ClassicalEstimatePieces.quadform_le_frobenius_mul_sq
#print axioms ClassicalEstimatePieces.gronwall_linear
#print axioms ClassicalEstimatePieces.cutoff_nonneg
#print axioms ClassicalEstimatePieces.cutoff_le_one
#print axioms ClassicalEstimatePieces.hasFDerivAt_cutoff
#print axioms ClassicalEstimatePieces.norm_fderiv_cutoff_le
#print axioms ClassicalEstimatePieces.comoving_cutoff_bound
#print axioms ClassicalEstimatePieces.holder_triple_pasted_sum
#print axioms ClassicalEstimatePieces.holder_pair
#print axioms ClassicalEstimatePieces.interp_theta
#print axioms ClassicalEstimatePieces.young_pair
#print axioms ClassicalEstimatePieces.serrin_scaling
#print axioms ClassicalEstimatePieces.amplitude_refutes_rate_sup
#print axioms ClassicalEstimatePieces.amplitude_refutes_rate_enstrophy
#print axioms ClassicalEstimatePieces.amplitude_refutes_rate_enstrophy_U
#print axioms ClassicalEstimatePieces.deriv_le_of_touch
#print axioms ClassicalEstimatePieces.rate_false_of_touch
#print axioms ClassicalEstimatePieces.not_uniform_rate_sup
