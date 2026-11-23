/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.AnalyticBridgeRefutation
import FrohmanianTetherConditional.ClassicalNS
import FrohmanianTetherConditional.FrohmanianTripleArchitectureLifespan

/-!
# Truth Gate: semantics lock for the Vacuity note (see `TRUTH_GATE.md`)

PAPER_PATH: paper/vacuity-audit/vacuity_audit.tex
PAPER_SHA256: 257ae064898a8451dc7fad4fd1fa558aaa51320e8ca54358c4e6c02e4df1e1a2
PAPER_SECTION: Sections 3--5, the stated theorems, propositions and the lemma on gradLinf

Locked paper claims: every theorem and proposition the Vacuity note states, independently
transcribed from the English of those environments.

PAPER_QUOTE_BEGIN
\begin{theorem}[\lean{analytic\_bridge\_target\_statement\_false}]
The legacy target statement is false.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[\lean{not\_nonempty\_BKMCriterion}]
For every $N$, the legacy type \lean{BKMCriterion N} is empty.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[\lean{hypothesisB\_holds}, \lean{clayStatementB\_holds}]
Every \lean{NavierStokesUnifiedData} satisfies Hypothesis~B and \lean{clayStatementB}.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{proposition}[non-vacuity; all proved in Lean]\leavevmode
\begin{enumerate}
\item \lean{const\_isClassicalNS}, \lean{nonempty\_NSSolution\_zero}: for every
$c\in\R^3$, $u\equiv c$, $p\equiv 0$ is a classical solution with $\Tstar=\top$;
in particular \lean{NSSolution ν 0} is inhabited for $\nu>0$.
\item \lean{zero\_field\_is\_global}: a solution with zero data that vanishes on its
lifespan has $\Tstar=\top$. Hence \lean{old\_counterexample\_invalid}: there is no
\lean{NSSolution} with $u_0=0$, $u\equiv 0$ and $\Tstar=1$.
\item \lean{linear\_in\_time\_not\_NS}: for any $\Tstar>0$, $u(t,x)=t\,e_0$, $p\equiv 0$
is \emph{not} a classical solution. (At any $r\in(0,\Tstar)$ the time derivative of the
first component is $1$, while every spatial derivative of the $x$-independent field
vanishes, so the right-hand side is $0$; uniqueness of derivatives gives $1=0$.)
\end{enumerate}
\end{proposition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{lemma}[\lean{gradLinf\_continuousOn}]
If $0\le T$ and $T<\Tstar$, then $t\mapsto\|\nabla u(t)\|_\infty$ is continuous on
$[0,T]$.
\end{lemma}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[\lean{global\_implies\_gradIntegral\_finite}]
If $\Tstar=\top$ then $\int_{[0,T)}\|\nabla u(t)\|_\infty\,dt<\infty$ for every $T$.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[\lean{BKMCriterion}, cited]
For every maximal classical solution with $\Tstar\neq\top$:
$\int_{[0,\Tstar)}\|\nabla u(t)\|_\infty\,dt = \infty$.
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[conditional; proved in Lean]\leavevmode
\begin{enumerate}
\item \lean{gradIntegral\_finite\_implies\_global}: BKM and finiteness of
$\int_{[0,T)\cap L}\|\nabla u\|_\infty$ for all $T>0$ imply $\Tstar=\top$.
\item \lean{clayB\_iff\_gradIntegral\_finite}: under BKM, $\Tstar=\top$ iff those
integrals are finite for all $T>0$.
\item \lean{formB\_implies\_clayB}, \lean{analyticBridge\_of\_formB}: Hypothesis~B
(a uniform bound $\int_{[0,T)\cap L}\|\nabla u\|_\infty\le C_\star(T)$ over all
solutions) and BKM imply every maximal solution is global.
\item \lean{formB\_Hs\_bound}: adding the cited Kato--Ponce inequality
$\|u(t)\|_{H^s}\le\|u_0\|_{H^s}+\int_0^t C_s\|\nabla u\|_\infty\|u\|_{H^s}$
gives $\|u(t)\|_{H^s}\le\|u_0\|_{H^s}\exp(C_s\max(C_\star(T),0))$ on $[0,T]$.
\end{enumerate}
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{proposition}[\lean{blowupModel}; proved]
$\Tstar=1$, $\|\omega\|_\infty(t)=\|S\|_\infty(t)=(1-t)^{-1}$ satisfies every field, and
\lean{clayStatementB} fails. Hence \lean{clayStatementB\_not\_automatic},
\lean{hypothesisB\_not\_automatic} and \lean{old\_trivialization\_fails}.
\end{proposition}
PAPER_QUOTE_END

Each `formal_claim_X` is the statement of the corresponding Lean theorem.
Each `paper_claim_X` is an independent transcription: named repository hypothesis
Props are expanded, and the logical form is equivalent but not definitionally
equal (binder order, contrapositive BKM, or an expanded negation).
-/

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace TruthGateVacuity

-- TRUTH-GATE LOCK BEGIN

/-- Legacy target is false. -/
def formal_claim_target_false : Prop :=
  ¬ analytic_bridge_unconditional_statement

def paper_claim_target_false : Prop :=
  ∃ (N : NormData) (ν : ℝ) (_hν : 0 < ν) (s : ℝ) (_hs : 5 / 2 < s)
    (u0 : R3 → Vec3) (_hper : IsPeriodic u0) (_hu0 : N.Hs s u0 < ⊤)
    (sol : NSSolution N ν u0),
      sol.Tstar ≠ ⊤ ∨
        ¬ ∀ T : ℝ, 0 < T →
          IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T

theorem intended_correspondence_target_false :
    formal_claim_target_false ↔ paper_claim_target_false := by
  constructor
  · intro h
    unfold formal_claim_target_false analytic_bridge_unconditional_statement at h
    push_neg at h
    obtain ⟨N, ν, hν, s, hs, u0, hper, hu0, sol, hconc⟩ := h
    refine ⟨N, ν, hν, s, hs, u0, hper, hu0, sol, ?_⟩
    exact not_and_or.mp hconc
  · intro ⟨N, ν, hν, s, hs, u0, hper, hu0, sol, hdisj⟩
    intro hall
    have hconc := hall N ν hν s hs u0 hper hu0 sol
    exact (not_and_or.mpr hdisj) hconc

def formal_claim_bkm_empty : Prop :=
  ∀ N : NormData, ¬ Nonempty (BKMCriterion N)

def paper_claim_bkm_empty : Prop :=
  ∀ N : NormData,
    (∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0),
      (∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T) →
      sol.Tstar = ⊤) → False

theorem intended_correspondence_bkm_empty :
    formal_claim_bkm_empty ↔ paper_claim_bkm_empty := by
  constructor
  · intro h N hcont
    exact h N ⟨⟨hcont⟩⟩
  · intro h N ⟨bkm⟩
    exact h N bkm.continuation

def formal_claim_hypB_holds : Prop :=
  ∀ sol : FrohmanianTripleArchitecture.NavierStokesUnifiedData,
    FrohmanianTripleArchitecture.HypothesisB sol

def paper_claim_hypB_holds : Prop :=
  ∀ sol : FrohmanianTripleArchitecture.NavierStokesUnifiedData,
    ∀ T : ℝ, 0 < T →
      ∃ C_star : ℝ, ∀ t ∈ Icc 0 T,
        (∫ τ in (0 : ℝ)..t, sol.strainSup τ) ≤ C_star

theorem intended_correspondence_hypB_holds :
    formal_claim_hypB_holds ↔ paper_claim_hypB_holds := by
  constructor
  · intro h sol T hT
    exact h sol T hT
  · intro h sol T hT
    exact h sol T hT

def formal_claim_clayB_holds : Prop :=
  ∀ sol : FrohmanianTripleArchitecture.NavierStokesUnifiedData, sol.clayStatementB

def paper_claim_clayB_holds : Prop :=
  ∀ sol : FrohmanianTripleArchitecture.NavierStokesUnifiedData, sol.clayStatementB ↔ True

theorem intended_correspondence_clayB_holds :
    formal_claim_clayB_holds ↔ paper_claim_clayB_holds := by
  constructor
  · intro h sol
    exact iff_true_intro (h sol)
  · intro h sol
    exact (h sol).mp trivial

def formal_claim_const_ns : Prop :=
  ∀ (ν : ℝ) (c : ClassicalNS.E3),
    ClassicalNS.IsClassicalNS ν (fun _ => c) (fun _ _ => c) (fun _ _ => 0) ⊤

def paper_claim_const_ns : Prop :=
  ∀ (c : ClassicalNS.E3) (ν : ℝ),
    ClassicalNS.IsClassicalNS ν (fun _ => c) (fun _ _ => c) (fun _ _ => 0) ⊤

theorem intended_correspondence_const_ns :
    formal_claim_const_ns ↔ paper_claim_const_ns := by
  constructor
  · intro h c ν; exact h ν c
  · intro h ν c; exact h c ν

def formal_claim_nonempty_zero : Prop :=
  ∀ (ν : ℝ), 0 < ν → Nonempty (ClassicalNS.NSSolution ν (fun _ => 0))

def paper_claim_nonempty_zero : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∃ _sol : ClassicalNS.NSSolution ν (fun _ => 0), True

theorem intended_correspondence_nonempty_zero :
    formal_claim_nonempty_zero ↔ paper_claim_nonempty_zero := by
  constructor
  · intro h ν hν
    obtain ⟨sol⟩ := h ν hν
    exact ⟨sol, trivial⟩
  · intro h ν hν
    obtain ⟨sol, _⟩ := h ν hν
    exact ⟨sol⟩

def formal_claim_zero_global : Prop :=
  ∀ {ν : ℝ} (sol : ClassicalNS.NSSolution ν (fun _ => 0)),
    (∀ t ∈ ClassicalNS.lifespan sol.Tstar, sol.u t = fun _ => 0) → sol.Tstar = ⊤

def paper_claim_zero_global : Prop :=
  ∀ (ν : ℝ) (sol : ClassicalNS.NSSolution ν (fun _ => 0)),
    (∀ t ∈ ClassicalNS.lifespan sol.Tstar, sol.u t = fun _ => 0) → sol.Tstar ≠ ⊤ → False

theorem intended_correspondence_zero_global :
    formal_claim_zero_global ↔ paper_claim_zero_global := by
  constructor
  · intro h ν sol hu hne
    exact hne (h sol hu)
  · intro h sol hu
    by_contra hne
    exact h _ sol hu hne

def formal_claim_old_invalid : Prop :=
  ∀ ν : ℝ,
    ¬ ∃ sol : ClassicalNS.NSSolution ν (fun _ => 0),
      sol.Tstar = 1 ∧ ∀ t, sol.u t = fun _ => 0

def paper_claim_old_invalid : Prop :=
  ∀ (ν : ℝ) (sol : ClassicalNS.NSSolution ν (fun _ => 0)),
    sol.Tstar = 1 → (∀ t, sol.u t = fun _ => 0) → False

theorem intended_correspondence_old_invalid :
    formal_claim_old_invalid ↔ paper_claim_old_invalid := by
  constructor
  · intro h ν sol hT hu
    exact h ν ⟨sol, hT, hu⟩
  · intro h ν ⟨sol, hT, hu⟩
    exact h ν sol hT hu

def formal_claim_linear_not : Prop :=
  ∀ (ν : ℝ) (Tstar : ENNReal), 0 < Tstar →
    ¬ ClassicalNS.IsClassicalNS ν (fun _ => 0) (fun t _ => t • ClassicalNS.e 0)
      (fun _ _ => 0) Tstar

def paper_claim_linear_not : Prop :=
  ∀ (Tstar : ENNReal) (ν : ℝ), 0 < Tstar →
    ¬ ClassicalNS.IsClassicalNS ν (fun _ => 0) (fun t _ => t • ClassicalNS.e 0)
      (fun _ _ => 0) Tstar

theorem intended_correspondence_linear_not :
    formal_claim_linear_not ↔ paper_claim_linear_not := by
  constructor
  · intro h Tstar ν hT; exact h ν Tstar hT
  · intro h ν Tstar hT; exact h Tstar ν hT

def formal_claim_grad_cont : Prop :=
  ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
    (sol : ClassicalNS.NSSolution ν u0) {T : ℝ},
    0 ≤ T → ENNReal.ofReal T < sol.Tstar →
      ContinuousOn (fun t => ClassicalNS.gradLinf (sol.u t)) (Icc 0 T)

def paper_claim_grad_cont : Prop :=
  ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
    (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
    0 ≤ T → ENNReal.ofReal T < sol.Tstar →
      ContinuousOn (fun t => ClassicalNS.gradLinf (sol.u t)) {t | 0 ≤ t ∧ t ≤ T}

theorem intended_correspondence_grad_cont :
    formal_claim_grad_cont ↔ paper_claim_grad_cont := by
  constructor
  · intro h ν u0 sol T hT hlt
    simpa [Set.Icc, Set.mem_setOf] using h (sol := sol) hT hlt
  · intro h sol T hT hlt
    have := h _ _ sol T hT hlt
    simpa [Set.Icc, Set.mem_setOf] using this

def formal_claim_glob_fin : Prop :=
  ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
    (sol : ClassicalNS.NSSolution ν u0),
    sol.Tstar = ⊤ → ∀ T : ℝ, ClassicalNS.gradIntegral sol T < ⊤

def paper_claim_glob_fin : Prop :=
  ∀ (T : ℝ) (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
    (sol : ClassicalNS.NSSolution ν u0),
    sol.Tstar = ⊤ → ClassicalNS.gradIntegral sol T < ⊤

theorem intended_correspondence_glob_fin :
    formal_claim_glob_fin ↔ paper_claim_glob_fin := by
  constructor
  · intro h T ν u0 sol hg; exact h sol hg T
  · intro h sol hg T; exact h T _ _ sol hg

def formal_claim_fin_glob : Prop :=
  ClassicalNS.BKMCriterion →
    ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
      (sol : ClassicalNS.NSSolution ν u0),
      (∀ T : ℝ, 0 < T → ClassicalNS.gradIntegral sol T < ⊤) → sol.Tstar = ⊤

def paper_claim_fin_glob : Prop :=
  (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
        sol.Tstar = ⊤) →
    ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∀ T : ℝ, 0 < T → ClassicalNS.gradIntegral sol T < ⊤) → sol.Tstar = ⊤

theorem intended_correspondence_fin_glob :
    formal_claim_fin_glob ↔ paper_claim_fin_glob := by
  constructor
  · intro h hBKM' ν u0 sol hf
    have bkm : ClassicalNS.BKMCriterion := fun {ν} {u0} sol' hne => by
      by_contra hfin
      exact hne (hBKM' ν u0 sol' hfin)
    exact h bkm sol hf
  · intro h bkm ν u0 sol hf
    refine h ?_ ν u0 sol hf
    intro ν' u0' sol' hfin
    by_contra hne
    exact hfin (bkm sol' hne)

def formal_claim_clay_iff : Prop :=
  ClassicalNS.BKMCriterion →
    ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
      (sol : ClassicalNS.NSSolution ν u0),
      sol.Tstar = ⊤ ↔ ∀ T : ℝ, 0 < T → ClassicalNS.gradIntegral sol T < ⊤

def paper_claim_clay_iff : Prop :=
  (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
        sol.Tstar = ⊤) →
    ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∀ T : ℝ, 0 < T → ClassicalNS.gradIntegral sol T < ⊤) ↔ sol.Tstar = ⊤

theorem intended_correspondence_clay_iff :
    formal_claim_clay_iff ↔ paper_claim_clay_iff := by
  constructor
  · intro h hBKM' ν u0 sol
    have bkm : ClassicalNS.BKMCriterion := fun {ν} {u0} sol' hne => by
      by_contra hfin
      exact hne (hBKM' ν u0 sol' hfin)
    exact (h bkm sol).symm
  · intro h bkm ν u0 sol
    have hBKM' : ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
        (sol : ClassicalNS.NSSolution ν u0),
        (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
          sol.Tstar = ⊤ := by
      intro ν' u0' sol' hfin
      by_contra hne
      exact hfin (bkm sol' hne)
    exact (h hBKM' ν u0 sol).symm

def formal_claim_formB_clay : Prop :=
  ∀ {C_star : ℝ → ℝ}, ClassicalNS.HypothesisB C_star → ClassicalNS.BKMCriterion →
    ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
      (sol : ClassicalNS.NSSolution ν u0), sol.Tstar = ⊤

def paper_claim_formB_clay : Prop :=
  ∀ (C_star : ℝ → ℝ),
    (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
      0 < T → ClassicalNS.gradIntegral sol T ≤ ENNReal.ofReal (C_star T)) →
    (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
        sol.Tstar = ⊤) →
    ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0), sol.Tstar = ⊤

theorem intended_correspondence_formB_clay :
    formal_claim_formB_clay ↔ paper_claim_formB_clay := by
  constructor
  · intro h C_star hB' hBKM' ν u0 sol
    have hB : ClassicalNS.HypothesisB C_star := by
      exact fun {ν} {u0} sol' T' hT' => hB' ν u0 sol' T' hT'
    have bkm : ClassicalNS.BKMCriterion := by
      exact fun {ν} {u0} sol' hne => by
        by_contra hfin
        exact hne (hBKM' ν u0 sol' hfin)
    exact h hB bkm sol
  · intro h C_star hB bkm ν u0 sol
    refine h C_star ?_ ?_ ν u0 sol
    · intro ν' u0' sol' T' hT'; exact hB sol' T' hT'
    · intro ν' u0' sol' hfin; by_contra hne; exact hfin (bkm sol' hne)

def formal_claim_formB_bridge : Prop :=
  ∀ {C_star : ℝ → ℝ}, ClassicalNS.HypothesisB C_star → ClassicalNS.BKMCriterion →
    ClassicalNS.AnalyticBridgeStatement

def paper_claim_formB_bridge : Prop :=
  ∀ (C_star : ℝ → ℝ),
    (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
      0 < T → ClassicalNS.gradIntegral sol T ≤ ENNReal.ofReal (C_star T)) →
    (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
      (sol : ClassicalNS.NSSolution ν u0),
      (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
        sol.Tstar = ⊤) →
    ∀ (ν : ℝ), 0 < ν → ∀ (u0 : ClassicalNS.E3 → ClassicalNS.E3),
      ContDiff ℝ ∞ u0 → ClassicalNS.IsPeriodic u0 → (∀ x, ClassicalNS.divergence u0 x = 0) →
      ∀ sol : ClassicalNS.NSSolution ν u0,
        sol.Tstar = ⊤ ∧ ∀ T : ℝ, 0 < T → ClassicalNS.gradIntegral sol T < ⊤

theorem intended_correspondence_formB_bridge :
    formal_claim_formB_bridge ↔ paper_claim_formB_bridge := by
  constructor
  · intro h C_star hB' hBKM'
    have hB : ClassicalNS.HypothesisB C_star := by
      exact fun {ν} {u0} sol' T' hT' => hB' ν u0 sol' T' hT'
    have bkm : ClassicalNS.BKMCriterion := by
      exact fun {ν} {u0} sol' hne => by
        by_contra hfin
        exact hne (hBKM' ν u0 sol' hfin)
    exact h hB bkm
  · intro h C_star hB bkm
    refine h C_star ?_ ?_
    · intro ν' u0' sol' T' hT'; exact hB sol' T' hT'
    · intro ν' u0' sol' hfin; by_contra hne; exact hfin (bkm sol' hne)

def formal_claim_formB_Hs : Prop :=
  ∀ {HsR : ℝ → (ClassicalNS.E3 → ClassicalNS.E3) → ℝ} {s C_s : ℝ},
    ClassicalNS.KatoPonceEnergy HsR s C_s →
    ∀ {C_star : ℝ → ℝ}, ClassicalNS.HypothesisB C_star → ClassicalNS.BKMCriterion →
      ∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
        (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
        0 < T → ∀ t ∈ Icc 0 T,
          HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max (C_star T) 0)

def paper_claim_formB_Hs : Prop :=
  ∀ (HsR : ℝ → (ClassicalNS.E3 → ClassicalNS.E3) → ℝ) (s C_s : ℝ),
    (∀ f, 0 ≤ HsR s f) → 0 ≤ C_s →
    (∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
      (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
      0 ≤ T → ENNReal.ofReal T < sol.Tstar →
        ContinuousOn (fun t => HsR s (sol.u t)) (Icc 0 T)) →
    (∀ {ν : ℝ} {u0 : ClassicalNS.E3 → ClassicalNS.E3}
      (sol : ClassicalNS.NSSolution ν u0) (t : ℝ),
      t ∈ ClassicalNS.lifespan sol.Tstar →
        HsR s (sol.u t) ≤
          HsR s u0 + ∫ τ in (0 : ℝ)..t,
            C_s * ClassicalNS.gradLinf (sol.u τ) * HsR s (sol.u τ)) →
    ∀ (C_star : ℝ → ℝ),
      (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
        (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
        0 < T → ClassicalNS.gradIntegral sol T ≤ ENNReal.ofReal (C_star T)) →
      (∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
        (sol : ClassicalNS.NSSolution ν u0),
        (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (ClassicalNS.gradLinf (sol.u t))) ≠ ⊤ →
          sol.Tstar = ⊤) →
      ∀ (ν : ℝ) (u0 : ClassicalNS.E3 → ClassicalNS.E3)
        (sol : ClassicalNS.NSSolution ν u0) (T : ℝ),
        0 < T → ∀ t : ℝ, 0 ≤ t ∧ t ≤ T →
          HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max (C_star T) 0)

theorem intended_correspondence_formB_Hs :
    formal_claim_formB_Hs ↔ paper_claim_formB_Hs := by
  constructor
  · intro hf HsR s C_s hnn hC hcont hE C_star hB' hBKM' ν u0 sol T hTpos t ht
    have kp : ClassicalNS.KatoPonceEnergy HsR s C_s :=
      { HsR_nonneg := hnn, C_s_nonneg := hC, HsR_cont := hcont, energy := hE }
    have hB : ClassicalNS.HypothesisB C_star := by
      exact fun {ν} {u0} sol' T' hT' => hB' ν u0 sol' T' hT'
    have bkm : ClassicalNS.BKMCriterion := by
      exact fun {ν} {u0} sol' hne => by
        by_contra hfin
        exact hne (hBKM' ν u0 sol' hfin)
    exact hf kp hB bkm sol T hTpos t ⟨ht.1, ht.2⟩
  · intro hp HsR s C_s kp C_star hB bkm ν u0 sol T hTpos t ht
    refine hp HsR s C_s kp.HsR_nonneg kp.C_s_nonneg kp.HsR_cont kp.energy C_star ?_ ?_
        ν u0 sol T hTpos t ⟨ht.1, ht.2⟩
    · intro ν' u0' sol' T' hT'; exact hB sol' T' hT'
    · intro ν' u0' sol' hfin; by_contra hne; exact hfin (bkm sol' hne)

def formal_claim_clay_not_auto : Prop :=
  ∃ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    ¬ FrohmanianTripleArchitectureLifespan.clayStatementB sol

def paper_claim_clay_not_auto : Prop :=
  ∃ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    sol.Tstar ≠ ⊤

theorem intended_correspondence_clay_not_auto :
    formal_claim_clay_not_auto ↔ paper_claim_clay_not_auto := by
  constructor
  · intro ⟨sol, h⟩
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.clayStatementB] using h
  · intro ⟨sol, h⟩
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.clayStatementB] using h

def formal_claim_hyp_not_auto : Prop :=
  ∃ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    ¬ FrohmanianTripleArchitectureLifespan.HypothesisB sol

def paper_claim_hyp_not_auto : Prop :=
  ∃ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    ¬ ∀ T : ℝ, 0 < T →
      ∃ C_star : ℝ, ∀ t ∈ Icc 0 T, ENNReal.ofReal t < sol.Tstar →
        (∫ τ in (0 : ℝ)..t, sol.strainSup τ) ≤ C_star

theorem intended_correspondence_hyp_not_auto :
    formal_claim_hyp_not_auto ↔ paper_claim_hyp_not_auto := by
  constructor
  · intro ⟨sol, h⟩
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.HypothesisB] using h
  · intro ⟨sol, h⟩
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.HypothesisB] using h

def formal_claim_old_triv_fails : Prop :=
  ¬ ∀ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    FrohmanianTripleArchitectureLifespan.HypothesisB sol

def paper_claim_old_triv_fails : Prop :=
  ∃ sol : FrohmanianTripleArchitectureLifespan.NavierStokesUnifiedData,
    ¬ ∀ T : ℝ, 0 < T →
      ∃ C_star : ℝ, ∀ t ∈ Icc 0 T, ENNReal.ofReal t < sol.Tstar →
        (∫ τ in (0 : ℝ)..t, sol.strainSup τ) ≤ C_star

theorem intended_correspondence_old_triv_fails :
    formal_claim_old_triv_fails ↔ paper_claim_old_triv_fails := by
  constructor
  · intro h
    obtain ⟨sol, hs⟩ := not_forall.mp h
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.HypothesisB] using hs
  · intro ⟨sol, hs⟩
    apply not_forall.mpr
    refine ⟨sol, ?_⟩
    simpa [FrohmanianTripleArchitectureLifespan.HypothesisB] using hs
-- TRUTH-GATE LOCK END

theorem formal_claim_target_false_holds : formal_claim_target_false :=
  AnalyticBridgeRefutation.analytic_bridge_target_statement_false

theorem paper_claim_target_false_holds : paper_claim_target_false :=
  intended_correspondence_target_false.mp formal_claim_target_false_holds

theorem formal_claim_bkm_empty_holds : formal_claim_bkm_empty :=
  AnalyticBridgeRefutation.not_nonempty_BKMCriterion

theorem paper_claim_bkm_empty_holds : paper_claim_bkm_empty :=
  intended_correspondence_bkm_empty.mp formal_claim_bkm_empty_holds

theorem formal_claim_hypB_holds_holds : formal_claim_hypB_holds :=
  AnalyticBridgeRefutation.hypothesisB_holds

theorem paper_claim_hypB_holds_holds : paper_claim_hypB_holds :=
  intended_correspondence_hypB_holds.mp formal_claim_hypB_holds_holds

theorem formal_claim_clayB_holds_holds : formal_claim_clayB_holds :=
  AnalyticBridgeRefutation.clayStatementB_holds

theorem paper_claim_clayB_holds_holds : paper_claim_clayB_holds :=
  intended_correspondence_clayB_holds.mp formal_claim_clayB_holds_holds

theorem formal_claim_const_ns_holds : formal_claim_const_ns :=
  ClassicalNS.const_isClassicalNS

theorem paper_claim_const_ns_holds : paper_claim_const_ns :=
  intended_correspondence_const_ns.mp formal_claim_const_ns_holds

theorem formal_claim_nonempty_zero_holds : formal_claim_nonempty_zero :=
  ClassicalNS.nonempty_NSSolution_zero

theorem paper_claim_nonempty_zero_holds : paper_claim_nonempty_zero :=
  intended_correspondence_nonempty_zero.mp formal_claim_nonempty_zero_holds

theorem formal_claim_zero_global_holds : formal_claim_zero_global :=
  fun {_} => ClassicalNS.zero_field_is_global

theorem paper_claim_zero_global_holds : paper_claim_zero_global :=
  intended_correspondence_zero_global.mp formal_claim_zero_global_holds

theorem formal_claim_old_invalid_holds : formal_claim_old_invalid :=
  ClassicalNS.old_counterexample_invalid

theorem paper_claim_old_invalid_holds : paper_claim_old_invalid :=
  intended_correspondence_old_invalid.mp formal_claim_old_invalid_holds

theorem formal_claim_linear_not_holds : formal_claim_linear_not :=
  ClassicalNS.linear_in_time_not_NS

theorem paper_claim_linear_not_holds : paper_claim_linear_not :=
  intended_correspondence_linear_not.mp formal_claim_linear_not_holds

theorem formal_claim_grad_cont_holds : formal_claim_grad_cont :=
  fun {_} {_} => ClassicalNS.gradLinf_continuousOn

theorem paper_claim_grad_cont_holds : paper_claim_grad_cont :=
  intended_correspondence_grad_cont.mp formal_claim_grad_cont_holds

theorem formal_claim_glob_fin_holds : formal_claim_glob_fin :=
  fun {_} {_} => ClassicalNS.global_implies_gradIntegral_finite

theorem paper_claim_glob_fin_holds : paper_claim_glob_fin :=
  intended_correspondence_glob_fin.mp formal_claim_glob_fin_holds

theorem formal_claim_fin_glob_holds : formal_claim_fin_glob :=
  ClassicalNS.gradIntegral_finite_implies_global

theorem paper_claim_fin_glob_holds : paper_claim_fin_glob :=
  intended_correspondence_fin_glob.mp formal_claim_fin_glob_holds

theorem formal_claim_clay_iff_holds : formal_claim_clay_iff :=
  ClassicalNS.clayB_iff_gradIntegral_finite

theorem paper_claim_clay_iff_holds : paper_claim_clay_iff :=
  intended_correspondence_clay_iff.mp formal_claim_clay_iff_holds

theorem formal_claim_formB_clay_holds : formal_claim_formB_clay :=
  fun {_} => ClassicalNS.formB_implies_clayB

theorem paper_claim_formB_clay_holds : paper_claim_formB_clay :=
  intended_correspondence_formB_clay.mp formal_claim_formB_clay_holds

theorem formal_claim_formB_bridge_holds : formal_claim_formB_bridge :=
  fun {_} => ClassicalNS.analyticBridge_of_formB

theorem paper_claim_formB_bridge_holds : paper_claim_formB_bridge :=
  intended_correspondence_formB_bridge.mp formal_claim_formB_bridge_holds

theorem formal_claim_formB_Hs_holds : formal_claim_formB_Hs :=
  fun {_} {_} {_} => ClassicalNS.formB_Hs_bound

theorem paper_claim_formB_Hs_holds : paper_claim_formB_Hs :=
  intended_correspondence_formB_Hs.mp formal_claim_formB_Hs_holds

theorem formal_claim_clay_not_auto_holds : formal_claim_clay_not_auto :=
  FrohmanianTripleArchitectureLifespan.clayStatementB_not_automatic

theorem paper_claim_clay_not_auto_holds : paper_claim_clay_not_auto :=
  intended_correspondence_clay_not_auto.mp formal_claim_clay_not_auto_holds

theorem formal_claim_hyp_not_auto_holds : formal_claim_hyp_not_auto :=
  FrohmanianTripleArchitectureLifespan.hypothesisB_not_automatic

theorem paper_claim_hyp_not_auto_holds : paper_claim_hyp_not_auto :=
  intended_correspondence_hyp_not_auto.mp formal_claim_hyp_not_auto_holds

theorem formal_claim_old_triv_fails_holds : formal_claim_old_triv_fails :=
  FrohmanianTripleArchitectureLifespan.old_trivialization_fails

theorem paper_claim_old_triv_fails_holds : paper_claim_old_triv_fails :=
  intended_correspondence_old_triv_fails.mp formal_claim_old_triv_fails_holds

end TruthGateVacuity
