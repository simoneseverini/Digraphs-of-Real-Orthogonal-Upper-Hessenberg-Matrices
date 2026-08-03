---
id: 0b597253c93d
status: proved
type: lemma
lean:
  - decl: HessenbergDigraphs.loop_iff_mem_activeRows_and_activeCols
    module: HessenbergDigraphs.Combinatorial.Loop
    line: 42
    state: proven
  - decl: HessenbergDigraphs.loop_at_first
    module: HessenbergDigraphs.Combinatorial.Loop
    line: 55
    state: proven
  - decl: HessenbergDigraphs.loop_at_last
    module: HessenbergDigraphs.Combinatorial.Loop
    line: 80
    state: proven
  - decl: HessenbergDigraphs.loop_at_mid
    module: HessenbergDigraphs.Combinatorial.Loop
    line: 109
    state: proven
---

# Lemma — a loop sits exactly where an active row meets an active column

Loops are the one local feature of $D_n(S)$, and they are decided by $S$ alone. Reading the three cases backwards gives the loopless condition of [[cor-loopless-characterization]].

## Statement

> [!lemma] Loops in the model
> Let $n \ge 2$ and $S \subseteq [n-1]$, and write $R = R(S)$, $C = C(S)$. The [[def-active-set|combinatorial digraph]] $D_n(S)$ has a loop at $v$ if and only if $v \in R \cap C$. Explicitly:
> - $1 \to 1$ is an arc if and only if $1 \in S$;
> - $n \to n$ is an arc if and only if $n - 1 \in S$;
> - for $2 \le v \le n-1$, $v \to v$ is an arc if and only if $\{v-1, v\} \subseteq S$.

## Proof

> [!note]- Proof (click to expand)
> A spine arc runs $j+1 \to j$ and so is never a loop. A loop is therefore an [[def-active-set|overlay arc]] $v \to v$, which exists exactly when $v \in R$ and $v \in C$ (the condition $i \le j$ being satisfied trivially).
>
> Substituting $R = \{1\} \cup \{k+1 : k \in S\}$ and $C = S \cup \{n\}$ gives the three cases: $1 \in R$ always, so a loop at $1$ needs $1 \in C$, i.e. $1 \in S$; $n \in C$ always, so a loop at $n$ needs $n \in R$, i.e. $n - 1 \in S$; and for $2 \le v \le n-1$, $v \in R$ means $v - 1 \in S$ while $v \in C$ means $v \in S$. $\square$
