# Truth Gate

This repository locks the Lean-certified claims of three papers against
the official kernel certificate. There is no author-approval job, and
PENDING is not a failure. `draft_dirs` is empty: no Lean file is exempt
from the forbidden-token scan. File lists for every build scan come from
`git ls-files '*.lean'` (omitting only `.lake/`). Any `sorry` in the official
`lake build` log fails the check.

Scope: the main lock certifies only the implication
`Hypothesis B → BKMCriterion → AnalyticBridgeStatement`. The two hypotheses
are assumptions, not theorems. An independent review of whether those
encodings are faithful, and whether they are vacuous, is in progress.
Clay Millennium Problem Statement (B) remains open.

## Unified paper

- Path: `paper/Frohmanian_Tether_Unified.tex`
- SHA-256: `e8723c81b7d94f595b053e8e260c8037f349960951a6612f18b98b73f46703f4`
- Main theorem: `ClassicalNS.analyticBridge_of_formB_forall`
- Companion theorem (additional lock `unified-formB-Hs`): `ClassicalNS.formB_Hs_bound`

Verbatim locked quotes:

```
\begin{definition}[Hypothesis~B, Lean \texttt{HypothesisB}]\label{def:hypB}
For a bound \(C_\star:\R\to\R\), Hypothesis~B says: for every viscosity \(\nu\), every initial datum \(\uvec_0\), every maximal classical solution \(\mathrm{sol}\), and every \(T>0\),
\[
\texttt{gradIntegral}(\mathrm{sol},T)\le \texttt{ENNReal.ofReal}(C_\star(T)).
\]
\end{definition}
```

```
\begin{definition}[Named BKM hypothesis, Lean \texttt{BKMCriterion}]\label{def:bkm}
\texttt{BKMCriterion} says: for every maximal classical solution with \(T^\star\neq\top\),
\[
\int_{[0,T^\star)}^\texttt{-}\texttt{ENNReal.ofReal}(\texttt{gradLinf}(\uvec(t)))\,dt=\top.
\]
This is a named hypothesis in the Lean development, written after the Beale--Kato--Majda continuation criterion~\cite{BKM1984}. It is not proved in Lean.
\end{definition}
```

```
\begin{definition}[Analytic bridge statement, Lean \texttt{AnalyticBridgeStatement}]\label{def:bridge}
The analytic bridge statement says: for every \(\nu>0\) and every smooth, periodic, divergence-free initial datum \(\uvec_0\), every maximal classical solution satisfies \(T^\star=\top\) and \(\texttt{gradIntegral}(\mathrm{sol},T)<\top\) for every \(T>0\).
\end{definition}
```

```
\begin{theorem}[Conditional implication, Lean \texttt{analyticBridge\_of\_formB} / \texttt{analyticBridge\_of\_formB\_forall}]\label{thm:A}
For every bound \(C_\star:\R\to\R\), if Hypothesis~B holds for \(C_\star\) and if \texttt{BKMCriterion} holds, then the analytic bridge statement holds.
\end{theorem}
```

```
A companion Lean theorem, \texttt{formB\_Hs\_bound}, gives a direct \(H^s\)-style bound under the additional named hypothesis \texttt{KatoPonceEnergy} (a cited Kato--Ponce energy inequality on genuine solutions, not proved in Lean): on \([0,T]\),
\[
\texttt{HsR}(s,\uvec(t))\le \texttt{HsR}(s,\uvec_0)\exp\bigl(C_s\max(C_\star(T),0)\bigr).
\]
The content of that bound for a zero dummy norm is trivial (\texttt{kp\_trivial}); its intended content is for a true \(H^s\) norm, which Mathlib does not yet supply on \(\T^3\).
```

## Vacuity note

- Path: `paper/vacuity-audit/vacuity_audit.tex`
- SHA-256: `257ae064898a8451dc7fad4fd1fa558aaa51320e8ca54358c4e6c02e4df1e1a2`
- Additional lock `vacuity-audit`: every theorem and proposition the note states.

Verbatim locked quotes:

```
\begin{theorem}[\lean{analytic\_bridge\_target\_statement\_false}]
The legacy target statement is false.
\end{theorem}
```

```
\begin{theorem}[\lean{not\_nonempty\_BKMCriterion}]
For every $N$, the legacy type \lean{BKMCriterion N} is empty.
\end{theorem}
```

```
\begin{theorem}[\lean{hypothesisB\_holds}, \lean{clayStatementB\_holds}]
Every \lean{NavierStokesUnifiedData} satisfies Hypothesis~B and \lean{clayStatementB}.
\end{theorem}
```

```
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
```

```
\begin{lemma}[\lean{gradLinf\_continuousOn}]
If $0\le T$ and $T<\Tstar$, then $t\mapsto\|\nabla u(t)\|_\infty$ is continuous on
$[0,T]$.
\end{lemma}
```

```
\begin{theorem}[\lean{global\_implies\_gradIntegral\_finite}]
If $\Tstar=\top$ then $\int_{[0,T)}\|\nabla u(t)\|_\infty\,dt<\infty$ for every $T$.
\end{theorem}
```

```
\begin{definition}[\lean{BKMCriterion}, cited]
For every maximal classical solution with $\Tstar\neq\top$:
$\int_{[0,\Tstar)}\|\nabla u(t)\|_\infty\,dt = \infty$.
\end{definition}
```

```
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
```

```
\begin{proposition}[\lean{blowupModel}; proved]
$\Tstar=1$, $\|\omega\|_\infty(t)=\|S\|_\infty(t)=(1-t)^{-1}$ satisfies every field, and
\lean{clayStatementB} fails. Hence \lean{clayStatementB\_not\_automatic},
\lean{hypothesisB\_not\_automatic} and \lean{old\_trivialization\_fails}.
\end{proposition}
```

## Three Pillars note

- Path: `paper/Three_Pillars_NS.tex`
- SHA-256: `6d3d04b27fddb11547df6a72a08473eb281618957258ec06f8ac01705fb7d8b4`
- Additional lock `three-pillars`: `ClassicalNS.analyticBridge_of_formB_forall`

Verbatim locked quotes:

```
\begin{theorem}[Conditional implication]\label{thm:conditional}
For every bound \(C_\star:\mathbb{R}\to\mathbb{R}\), if Lean's \texttt{HypothesisB} holds for \(C_\star\) and if Lean's \texttt{BKMCriterion} holds, then for every viscosity \(\nu>0\) and every smooth, periodic, divergence-free initial datum, every maximal classical solution (an object of type \texttt{NSSolution}) is global (\(T^\star=\top\)) and has finite \(\int_0^T\|\nabla\mathbf{u}(t)\|_{L^\infty}\,dt\) for every finite \(T>0\).
\end{theorem}
```
