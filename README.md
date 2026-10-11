# Strong Holevo Additivity for Qubit Channels

The strong additivity problem for qubit channels asks for the following statement.

> [!NOTE]
> **Conjecture (Strong Holevo additivity for qubit channels).**
>
> For every completely positive, trace-preserving map
>
> ```math
> \Phi:M_2(\mathbb{C})\longrightarrow M_2(\mathbb{C})
> ```
>
> and every completely positive, trace-preserving map $`\Omega:M_n(\mathbb{C})\to M_m(\mathbb{C})`$, with arbitrary positive integers $`n,m`$,
>
> ```math
> \chi(\Phi\otimes\Omega)=\chi(\Phi)+\chi(\Omega).
> ```

Here $`\chi`$ is the optimized Holevo information,

```math
\chi(\Phi)=\sup_{\{p_i,\rho_i\}}
\left[S\left(\Phi\left(\sum_i p_i\rho_i\right)\right)
-\sum_i p_iS(\Phi(\rho_i))\right],
```

where the supremum is over finite ensembles of density matrices and $`S(\rho)=-\mathrm{Tr}(\rho\log\rho)`$. Both the input and output of $`\Phi`$ have dimension two. No unitality, pure-output, Kraus-rank, or symmetry condition is imposed; the partner $`\Omega`$ is arbitrary and finite-dimensional.

This repository presents a proposed proof of this conjecture. A proof sketch follows; the [PDF manuscript](PDF/qubit-strong-additivity.pdf) contains the detailed proof. The manuscript is a public draft for mathematical review and has not been formally verified in Lean.

## Proof sketch

### 1. Establish a four-block entropy inequality

For compatible complex rectangular blocks, set

```math
M=\begin{pmatrix}A&B&0\\C&0&D\end{pmatrix},
\qquad
(x,y,z,w)=(\|A\|_F^2,\|B\|_F^2,\|C\|_F^2,\|D\|_F^2),
```

with $`x+y+z+w=1`$, and put

```math
L=\begin{pmatrix}x+y&\sqrt{xz}\\\sqrt{xz}&z+w\end{pmatrix}.
```

The matrix inequality used in the proof is

```math
\begin{aligned}
S(MM^{*})\ge S(L)
&+xS(AA^{*}/x)+yS(BB^{*}/y)\\
&+zS(CC^{*}/z)+wS(DD^{*}/w).
\end{aligned}
```

Zero-weight terms are defined as zero. The inequality applies in arbitrary finite block dimensions.

### 2. Prove the matrix inequality through a concave dual value

A stationary Gram identity gives a positive matrix curve $`F`$ satisfying

```math
F''\succeq F'F^{-1}F'.
```

A noncommutative comparison lemma bounds this curve by the weighted geometric mean of its endpoints. Integrating the resulting operator inequality controls the Hessian of a dual value function with fixed block-scalar multipliers.

The dual value is concave. A rank-one decomposition preserving the two central masses reduces its lower bound to a scalar problem. Choosing the multipliers at the prescribed outer masses then gives the four-block inequality. The manuscript includes existence and interiority of the minimizer, removal of unused directions, and the singular boundary.

### 3. Put every qubit channel into a Kraus normal form

A projective quartic has a zero that selects an output basis in which the off-diagonal dual image has rank at most one. Positivity of the Choi matrix then gives Kraus operators of the form

```math
K=\begin{pmatrix}a^{*}\\c^{*}\end{pmatrix},
\qquad
K_{0j}=\begin{pmatrix}b_j^{*}\\0\end{pmatrix},
\qquad
K_{1k}=\begin{pmatrix}0\\d_k^{*}\end{pmatrix},
```

with

```math
aa^{*}+cc^{*}+\sum_jb_jb_j^{*}+\sum_kd_kd_k^{*}=I.
```

Supported inverses handle singular Choi blocks, so this reduction includes every qubit-to-qubit channel.

### 4. Match the scalar bound and the partner marginal

Write $`\widehat S_\Phi`$ for the convex roof of the output entropy over finite pure-state ensembles. Every qubit state $`\rho`$ has a pure-state decomposition preserving the two expectations $`x=a^{*}\rho a`$ and $`z=c^{*}\rho c`$. Entropy concavity gives

```math
\widehat S_\Phi(\rho)\le S(L(\rho)),
```

where $`L(\rho)`$ is the scalar matrix from Step 1 with the masses of the Kraus branches at $`\rho`$.

For a pure bipartite input $`\psi`$, the coefficient matrix of the joint output has the four-block form. The branch vectors $`\eta_f=(\langle f|\otimes I)\psi`$ satisfy

```math
\sum_f|\eta_f\rangle\langle\eta_f|=\rho_B.
```

Thus the internal entropy terms bound $`\widehat S_\Omega`$ at the actual partner marginal, giving

```math
S((\Phi\otimes\Omega)(|\psi\rangle\langle\psi|))
\ge\widehat S_\Phi(\rho_A)+\widehat S_\Omega(\rho_B).
```

### 5. Complete the Holevo argument

Convexity extends the pure-input bound to

```math
\widehat S_{\Phi\otimes\Omega}(\omega)
\ge\widehat S_\Phi(\omega_A)+\widehat S_\Omega(\omega_B).
```

Combining this with subadditivity of the output entropy yields $`\chi(\Phi\otimes\Omega)\le\chi(\Phi)+\chi(\Omega)`$. Product ensembles give the reverse inequality. The partner channel is arbitrary throughout, so the result also implies $`\chi(\Phi^{\otimes k})=k\chi(\Phi)`$ for every positive integer $`k`$.

## Detailed manuscript

- [PDF manuscript](PDF/qubit-strong-additivity.pdf)

Public draft 1, 11 October 2026.
