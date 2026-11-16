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
