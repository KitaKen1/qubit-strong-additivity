# Lean proof of strong Holevo additivity for qubit channels

For the Holevo information of qubit channels, the additivity problem is the following.

> **Conjecture.** For every completely positive trace-preserving map
> $`\Phi:M_2(\mathbb C)\to M_2(\mathbb C)`$ and every completely positive trace-preserving map
> $`\Omega:M_n(\mathbb C)\to M_m(\mathbb C)`$ with $`n,m\ge1`$,
>
> ```math
> \chi(\Phi\otimes\Omega)=\chi(\Phi)+\chi(\Omega).
> ```
>
> Here $`\chi`$ is the Holevo information
>
> ```math
> \chi(\Lambda)=\sup_{\{p_i,\rho_i\}}\Bigl[S\Bigl(\Lambda\Bigl(\sum_ip_i\rho_i\Bigr)\Bigr)
> -\sum_ip_iS(\Lambda(\rho_i))\Bigr],
> ```
>
> where the supremum is over finite ensembles of density matrices and
> $`S(\rho)=-\mathrm{Tr}(\rho\log\rho)`$ with the natural logarithm. No unitality, pure-output,
> Kraus-rank or symmetry condition is imposed on $`\Phi`$, and the optimization for
> $`\Phi\otimes\Omega`$ includes entangled inputs.

This repository presents a complete Lean proof of this conjecture.

Earlier results for a qubit channel $`\Phi`$ need a condition on $`\Phi`$ or on the partner:

| Result | Qubit channel $`\Phi`$ | Partner $`\Omega`$ |
|---|---|---|
| [King (2002)](https://arxiv.org/abs/quant-ph/0103156) | unital | any |
| [Tang, Zhu, Bai and Wang (2026)](https://arxiv.org/abs/2609.28592) | with a pure output | any |
| [Fang (2026)](https://arxiv.org/abs/2609.14621), [OpenAI (2026)](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/276.md) | generalized amplitude damping | the same channel, repeated |
| **This repository** | **any** | **any** |

Note that the partner $`\Omega`$ is arbitrary. Hence the conjecture also gives
$`\chi(\Phi^{\otimes n})=n\,\chi(\Phi)`$ for every qubit channel $`\Phi`$, which is proved here
as well.

**Main contribution.**

1. **Formal Conjectures statement.**
2. **Lean proof of the conjecture.**

**Subcontribution** (see the [Formal Conjectures target](#formal-conjectures-target)):

1. **Lean proof of additivity over independent uses.**

<!-- BEGIN PUBLICATION LINKS -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fqubit-strong-additivity%2Fmain%2Flean4web%2FQubitStrongAdditivityLean4Web.lean) (Lean **v4.34**).
<!-- END PUBLICATION LINKS -->

## Formal Conjectures target

[FClikelean/QubitHolevoAdditivity.lean](FClikelean/QubitHolevoAdditivity.lean) states the
conjecture with `category research solved, AMS 81 94`.
[QubitAdditivity/FCPresentation.lean](lean/QubitAdditivity/FCPresentation.lean) proves both
theorems below, with the same definitions.

### Target theorem

```lean
theorem strong_additivity {r s n m : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (L : Fin s → Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) (hL : IsKraus L) :
    holevo (tensorKraus K L) = holevo K + holevo L
```

A channel is given by a finite Kraus family: `IsKraus K` means $`\sum_iK_i^*K_i=1`$, and the
channel is $`\rho\mapsto\sum_iK_i\rho K_i^*`$. Every completely positive trace-preserving map
between matrix algebras has this form. `holevo K` is $`\chi`$ of that channel, and
`tensorKraus K L` is the Kraus family $`(K_i\otimes L_j)`$ of the tensor product.

### Consequence: independent uses

```lean
theorem power_additivity {r : ℕ} (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (n : ℕ) : holevo (powerKraus K n) = n * holevo K
```

`powerKraus K n` is the Kraus family $`(K_{i_1}\otimes\dots\otimes K_{i_n})`$ of $`n`$
independent uses of the channel. The case $`n=0`$ is included.

## Mathematical explanation (AI generated)

This sketch follows the Lean proof.

**Setting.** For a channel $`\Lambda`$ and a finite ensemble $`E=\{p_i,\rho_i\}`$, put
$`\chi(\Lambda;E)=S(\Lambda(\sum_ip_i\rho_i))-\sum_ip_iS(\Lambda(\rho_i))`$, so that
$`\chi(\Lambda)=\sup_E\chi(\Lambda;E)`$ ([Ensemble.lean](lean/QubitAdditivity/Ensemble.lean),
[Holevo.lean](lean/QubitAdditivity/Holevo.lean)). Product ensembles give
$`\chi(\Phi\otimes\Omega)\ge\chi(\Phi)+\chi(\Omega)`$ for all channels, so only the upper bound
has to be shown ([Target.lean](lean/QubitAdditivity/Target.lean)). Steps 1–4 prove it when
$`\Phi`$ is a qubit channel.

**1. Reduction to pure inputs.** Suppose that for every pure state $`\psi`$ of the joint input
there are finite ensembles $`\{p_i,\sigma_i\}`$ of the marginal $`\rho_A`$ and
$`\{q_j,\tau_j\}`$ of the marginal $`\rho_B`$ with

```math
\sum_ip_iS(\Phi(\sigma_i))+\sum_jq_jS(\Omega(\tau_j))\le S\bigl((\Phi\otimes\Omega)(\psi)\bigr).\qquad(*)
```

Then $`\chi(\Phi\otimes\Omega)\le\chi(\Phi)+\chi(\Omega)`$
([UpperBound.lean](lean/QubitAdditivity/UpperBound.lean)):
- **Mixed inputs.** A spectral decomposition extends $`(*)`$ to every joint input state.
- **Subadditivity.** The marginals of $`(\Phi\otimes\Omega)(\rho)`$ are $`\Phi(\rho_A)`$ and
  $`\Omega(\rho_B)`$, also for entangled $`\rho`$, so
  $`S((\Phi\otimes\Omega)(\rho))\le S(\Phi(\rho_A))+S(\Omega(\rho_B))`$
  ([Marginal.lean](lean/QubitAdditivity/Marginal.lean)).
- **Ensembles.** For an ensemble of joint states, the ensembles from $`(*)`$ for its members
  combine into ensembles of the two marginals, and the two facts above bound its Holevo
  quantity by $`\chi(\Phi)+\chi(\Omega)`$.

**2. Normal form of a qubit channel.** For every qubit channel $`\Phi`$ there is a unitary
$`U`$ such that the rotated channel $`\rho\mapsto U\Phi(\rho)U^*`$ has Kraus operators

```math
K=\begin{pmatrix}a^*\\c^*\end{pmatrix},\qquad
K_{0j}=\begin{pmatrix}b_j^*\\0\end{pmatrix},\qquad
K_{1k}=\begin{pmatrix}0\\d_k^*\end{pmatrix},
```

with $`a,c,b_j,d_k\in\mathbb C^2`$: every operator other than $`K`$ maps into a single output
basis vector (`exists_normal_channel` in
[NormalChannel.lean](lean/QubitAdditivity/NormalChannel.lean)). The steps are:
- **Rotation.** Under an output rotation with first row $`(s,t)`$, the determinant of the
  off-diagonal block of the dual map is a binary quartic in $`(s,t)`$. It has a zero on the
  unit sphere by the fundamental theorem of algebra, and there the block has rank at most one
  ([NormalForm.lean](lean/QubitAdditivity/NormalForm.lean)).
- **Common operator.** A Schur complement gives the operator $`K`$ when the diagonal blocks
  are positive definite ([NormalSchur.lean](lean/QubitAdditivity/NormalSchur.lean)). Singular
  blocks are reached by a compactness argument
  ([NormalCommonBranch.lean](lean/QubitAdditivity/NormalCommonBranch.lean)).
- **Remaining operators.** The positive semidefinite residuals are finite sums of outer
  products, which give $`b_j`$ and $`d_k`$
  ([NormalKraus.lean](lean/QubitAdditivity/NormalKraus.lean)).

Entropy and Holevo information do not change under an output rotation, also for a tensor
product ([RotationInvariant.lean](lean/QubitAdditivity/RotationInvariant.lean)). So it is
enough to prove $`(*)`$ for channels in normal form.

**3. A four-block entropy inequality.** For complex blocks $`A,B,C,D`$ of compatible sizes, put

```math
M=\begin{pmatrix}A&B&0\\C&0&D\end{pmatrix},\qquad
(x,y,z,w)=(\|A\|_F^2,\|B\|_F^2,\|C\|_F^2,\|D\|_F^2),\qquad
L=\begin{pmatrix}x+y&\sqrt{xz}\\\sqrt{xz}&z+w\end{pmatrix}.
```

If $`x+y+z+w=1`$, then

```math
S(MM^*)\ge S(L)+x\,S(AA^*/x)+y\,S(BB^*/y)+z\,S(CC^*/z)+w\,S(DD^*/w),
```

where a term with zero weight is zero (`TC4Bound` in [TC4.lean](lean/QubitAdditivity/TC4.lean),
proved as `tc4Bound` in [BetaTC4Boundary.lean](lean/QubitAdditivity/BetaTC4Boundary.lean)). The
proof uses a dual value function. Put $`\psi(X)=\mathrm{Tr}(X\log X)`$. For a positive
semidefinite $`J`$ on $`\mathbb C^r\oplus\mathbb C^s`$ and $`\lambda_0,\lambda_1<0`$, define

```math
F_J(W_0,W_1)=\psi(W_0)+\psi(W_1)-\psi\bigl(J+W_0\oplus W_1\bigr)
-\lambda_0\mathrm{Tr}\,W_0-\lambda_1\mathrm{Tr}\,W_1,
\qquad
V(J)=\psi(J_{00}\oplus J_{11})+\min_{W_0,W_1\succeq0}F_J(W_0,W_1),
```

where $`J_{00}`$ and $`J_{11}`$ are the diagonal blocks of $`J`$
([BetaDual.lean](lean/QubitAdditivity/BetaDual.lean),
[BetaDualValue.lean](lean/QubitAdditivity/BetaDualValue.lean)).
- **Minimizer.** For positive definite $`J`$, the function $`F_J`$ is strictly convex and
  coercive. Its minimizer over the positive semidefinite cone exists, is unique and is positive
  definite, so it satisfies the stationarity equations
  $`\log W_i-[\log(J+W_0\oplus W_1)]_{ii}=\lambda_i\,1`$
  ([BetaDualConvex.lean](lean/QubitAdditivity/BetaDualConvex.lean),
  [BetaDualExistence.lean](lean/QubitAdditivity/BetaDualExistence.lean),
  [BetaDualInterior.lean](lean/QubitAdditivity/BetaDualInterior.lean)).
- **Derivatives.** The derivative of the matrix logarithm is the inverse of the Kubo–Mori
  operator ([BetaLog.lean](lean/QubitAdditivity/BetaLog.lean),
  [BetaLogKM.lean](lean/QubitAdditivity/BetaLogKM.lean)). The minimizer depends differentiably
  on $`J`$, which gives the gradient and the Hessian of $`V`$
  ([BetaMinimizer.lean](lean/QubitAdditivity/BetaMinimizer.lean),
  [BetaValueHessian.lean](lean/QubitAdditivity/BetaValueHessian.lean)).
- **Concavity.** The Hessian of $`V`$ is a Schur complement of Kubo–Mori operators. It is
  nonpositive by a comparison of a curve of positive matrices with the weighted geometric mean
  of its endpoints ([BetaPWBound.lean](lean/QubitAdditivity/BetaPWBound.lean),
  [BetaHessian.lean](lean/QubitAdditivity/BetaHessian.lean)). So $`V`$ is concave on positive
  definite $`J`$ ([BetaDualConcave.lean](lean/QubitAdditivity/BetaDualConcave.lean)), and on all
  positive semidefinite $`J`$ by continuity
  ([BetaDualBoundary.lean](lean/QubitAdditivity/BetaDualBoundary.lean)).
- **Rank one.** $`V`$ is homogeneous of degree one, so concavity gives
  $`V(\sum_fJ_f)\ge\sum_fV(J_f)`$. The Gram matrix $`G`$ of the rows of $`A`$ and $`C`$ is a
  sum of rank-one terms, each with the same ratio of block traces as $`G`$
  ([BetaGramSplit.lean](lean/QubitAdditivity/BetaGramSplit.lean)). A rank-one term reduces to
  the scalar case by compressing to its support
  ([BetaSupportMinimum.lean](lean/QubitAdditivity/BetaSupportMinimum.lean),
  [BetaBalancedValue.lean](lean/QubitAdditivity/BetaBalancedValue.lean)).
- **Scalar case.** For $`J_0=\bigl(\begin{smallmatrix}x&\sqrt{xz}\\\sqrt{xz}&z\end{smallmatrix}\bigr)`$
  and the multipliers $`\lambda_0=\log y-(\log L)_{00}`$, $`\lambda_1=\log w-(\log L)_{11}`$,
  the point $`(W_0,W_1)=(y,w)`$ is stationary, hence the minimizer. Both multipliers are
  negative ([BetaScalarMinimum.lean](lean/QubitAdditivity/BetaScalarMinimum.lean),
  [BetaScalarValue.lean](lean/QubitAdditivity/BetaScalarValue.lean)).
- **Conclusion.** These give $`V(J_0)\le V(G)`$. Bounding the minimum in $`V(G)`$ by its value
  at $`(BB^*,DD^*)`$, where $`G+BB^*\oplus DD^*=MM^*`$, turns this into the inequality for
  positive $`x,y,z,w`$ ([BetaTC4Bridge.lean](lean/QubitAdditivity/BetaTC4Bridge.lean),
  [BetaPositiveTC4.lean](lean/QubitAdditivity/BetaPositiveTC4.lean)). Zero weights and empty
  blocks follow by a perturbation and continuity of the entropy
  ([BetaTC4Regularization.lean](lean/QubitAdditivity/BetaTC4Regularization.lean)).

**4. From the inequality to pure inputs.** Let $`N`$ be a channel in normal form, let $`\Omega`$
have Kraus operators $`W_\mu`$, and let $`\psi`$ be a pure joint input. For
$`u\in\{a,c,b_j,d_k\}`$ put $`\eta_u=(\langle u|\otimes1)\psi`$. Then $`(N\otimes\Omega)(\psi)`$
is $`MM^*`$ for the four-block matrix whose blocks $`A,B,C,D`$ have the columns
$`W_\mu\eta_a`$, $`W_\mu\eta_{b_j}`$, $`W_\mu\eta_c`$ and $`W_\mu\eta_{d_k}`$, and its weights
are $`x=\langle a,\rho_Aa\rangle`$, $`y=\sum_j\langle b_j,\rho_Ab_j\rangle`$,
$`z=\langle c,\rho_Ac\rangle`$ and $`w=\sum_k\langle d_k,\rho_Ad_k\rangle`$
([Partner.lean](lean/QubitAdditivity/Partner.lean)). The two sides of $`(*)`$ come from the
two parts of the inequality of step 3:
- **Partner side.** The normalized vectors $`\eta_u`$ form an ensemble of $`\rho_B`$ with
  weights $`\|\eta_u\|^2`$, and concavity of the entropy bounds its average output entropy
  under $`\Omega`$ by the four block terms.
- **Qubit side.** Every qubit state $`\rho`$ is a mixture of two singular states with the same
  values of $`\langle a,\cdot\,a\rangle`$ and $`\langle c,\cdot\,c\rangle`$. On a singular state
  the output of $`N`$ has the trace and the determinant of $`L`$, hence its entropy. Concavity
  bounds the average output entropy of this two-state ensemble by $`S(L)`$ at $`\rho_A`$
  ([TwoExpectation.lean](lean/QubitAdditivity/TwoExpectation.lean)).

Together these give $`(*)`$ for $`N`$ and $`\Omega`$
([PureInput.lean](lean/QubitAdditivity/PureInput.lean),
[TC4Result.lean](lean/QubitAdditivity/TC4Result.lean)). With steps 1 and 2 this proves the
conjecture ([GeneralResult.lean](lean/QubitAdditivity/GeneralResult.lean)).

**5. Kraus families and independent uses.** A Kraus family and its bundled channel have the
same action and the same Holevo information, and every bundled channel comes from a Kraus
family. This transfers the theorem to the Formal Conjectures statement. Additivity over
$`n`$ uses follows by induction on $`n`$ with the partner $`\Phi^{\otimes n}`$, since $`\chi`$
does not change when the systems are relabelled
([FCPresentation.lean](lean/QubitAdditivity/FCPresentation.lean)).

**In Lean.** The main choices are:
- explicit finite ensembles in $`(*)`$, instead of convex roofs or infima;
- limits for the degenerate cases: a perturbation for zero weights in step 3, and compactness
  for singular blocks in step 2;
- a statement that uses only Mathlib, with Physlib's bundled channels inside the proof.

The four-block inequality takes 53 of the 80 modules.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Complete proof: Mathlib `d13f23b7`, with the parts of Physlib `a4ef4612` and OpenAI math `fd4aeeb2` that it uses. Includes the Comparator challenge |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.34.1` | The same proof files without the Comparator challenge, checked byte for byte against `lean/` |
| [lean4web/](lean4web/) | `v4.34.1` | Complete proof in one Mathlib-only file, including the parts of Physlib and OpenAI math |
| [FClikelean/](FClikelean/) | FC `v4.33.1` | Formal Conjectures statement |
| [PDF/](PDF/) | — | Manuscript (public draft of 11 October 2026), with an OpenTimestamps proof (`.ots`) |
| [comparator/](comparator/) | Checks the proof with `v4.34.1` | Input pins, comparison scripts, runner preparation and verification guide |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Comparator verification workflow |
| [ComparatorLog20261012/](ComparatorLog20261012/) | — | Records of the public Comparator run: original artifacts, receipts and GitHub run data |
| [docs/](docs/) | — | Scope of each check, third-party sources and earlier notes |

Inside [lean/QubitAdditivity/](lean/QubitAdditivity/):

| Path | Content |
|---|---|
| `Target.lean`, `Holevo.lean`, `Ensemble.lean`, `Entropy.lean` | Definitions and the final proposition for bundled CPTP maps (the trusted statement) |
| `Presentation/Model.lean`, `FCPresentation.lean` | Definitions of the Formal Conjectures statement, its proof from the bundled statement, and independent uses |
| `UpperBound.lean`, `Marginal.lean` | Reduction of the upper bound to pure inputs |
| `Normal*.lean`, `RotationInvariant.lean` | Normal form of qubit channels and invariance under output rotations |
| `TC4.lean`, `Blocks.lean`, `Beta*.lean` | The four-block entropy inequality |
| `TwoExpectation.lean`, `Partner.lean`, `PureInput.lean`, `TC4Result.lean` | From the four-block inequality to pure inputs |
| `GeneralResult.lean` | Assembly of the final theorem |
| `Imported/` | Lemmas adapted from OpenAI math |

The project has 80 modules, about 11,800 lines. The vendored sources in
[lean/vendor/](lean/vendor/) are 51 files of Physlib and 14 files of OpenAI math.

## Verification

```bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The final theorems depend only on `[propext, Classical.choice, Quot.sound]`. The full audit
(`python3 lean/scripts/verify.py`) checks this for 741 theorems, compares both statements and
their definitions with the Comparator challenge, and records its results in
[lean/verification/](lean/verification/).

Further checks, run from the repository root unless noted:

```bash
(cd lean && lake env lean --run scripts/Replay.lean)
python3 lean/scripts/verify_lean4web.py
python3 lean/scripts/verify_lean_without_comparator.py
python3 lean/scripts/check_publication.py
```

They replay every declaration in a fresh environment, compile the one-file proof, check the
copy without Comparator files, and check that the Formal Conjectures statement agrees with the
proof. The Comparator workflow passed on the public repository; see the
[Appendix](#appendix-verification-by-lean-comparator-on-github-ci-runner).
[docs/verification.md](docs/verification.md) lists what each check covers.

## Status boundary

Proved here, for every qubit channel $`\Phi`$ and every channel $`\Omega`$ between systems of
positive finite dimension:

```text
χ(Φ ⊗ Ω) = χ(Φ) + χ(Ω), for Kraus families and for bundled CPTP maps.
χ(Φ^{⊗n}) = n χ(Φ) for every n ≥ 0.
The four-block entropy inequality, for all finite block sizes, including zero weights.
Every qubit channel has the normal form of step 2 after an output rotation.
```

The following are not claimed or not formalized:
- **Capacity.** The coding theorem that relates $`\chi`$ to the classical capacity is not
  formalized. The results are equalities of Holevo quantities.
- **Manuscript.** The Lean proof follows the strategy of the manuscript in [PDF/](PDF/), but it
  does not formalize the manuscript statement by statement. In particular, the convex-roof
  inequality of the manuscript is replaced by $`(*)`$ with explicit ensembles.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol,
and Claude Code using Claude Opus 5.5.

## Sources

- [King02] C. King, [Additivity for unital qubit channels](https://arxiv.org/abs/quant-ph/0103156),
  J. Math. Phys. 43 (2002), 4641: the case of unital qubit channels.
- [Has09] M. B. Hastings,
  [Superadditivity of communication capacity using entangled inputs](https://arxiv.org/abs/0809.3972),
  Nature Physics 5 (2009), 255: failure of additivity in high dimension.
- [TZBW26] Z. Tang, C. Zhu, G. Bai and X. Wang,
  [Classical Capacity and Entanglement Cost of the Amplitude Damping Channel](https://arxiv.org/abs/2609.28592),
  arXiv:2609.28592 (2026): the case of qubit channels with a pure output.
- [Fa26] K. Fang,
  [The classical capacity of generalized amplitude-damping channels and its strong-converse exponent](https://arxiv.org/abs/2609.14621),
  arXiv:2609.14621 (2026): generalized amplitude damping channels.
- [Physlib](https://github.com/leanprover-community/physlib) (revision `a4ef4612`, Apache 2.0):
  quantum states, channels and entropy lemmas. The proof depends on parts of Physlib, and the
  Lean4Web file includes them.
- [OpenAI math](https://github.com/openai/math) (revision `fd4aeeb2`, Apache 2.0): matrix
  entropy and matrix calculus lemmas, used in the same way. They come from its development on
  generalized amplitude damping channels
  ([result 276](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/276.md)).
- [Mathlib](https://github.com/leanprover-community/mathlib4).
- [Lean Comparator](https://github.com/leanprover/comparator/tree/ca04cfc72b550331658ec314bf47685281bfd4bf),
  at the pinned revision.

The original notices and licenses of Physlib and OpenAI math are kept in
[lean/vendor/](lean/vendor/); see [NOTICE](NOTICE) and
[docs/third-party.md](docs/third-party.md).

## Appendix: the CPTP-map statement and the Kraus-family statement

| | CPTP-map statement | Kraus-family statement |
|---|---|---|
| Channel | Physlib `CPTPMap` | finite family $`(K_i)`$ with $`\sum_iK_i^*K_i=1`$ |
| Input states | Physlib `MState` | positive semidefinite matrices of trace one |
| Ensembles | Physlib `MEnsemble` | finitely many probabilities and states |
| Statement depends on | Mathlib and Physlib | Mathlib only |
| Theorem | `generalQubitStrongAdditivity` | `QubitHolevo.strong_additivity` |

### Natural language comparison: CPTP-map statement vs Kraus-family statement

Both statements say that $`\chi(\Phi\otimes\Omega)=\chi(\Phi)+\chi(\Omega)`$ for every channel
$`\Phi`$ from a qubit to a qubit and every channel $`\Omega`$ from a system of dimension
$`n+1`$ to a system of dimension $`m+1`$.

The CPTP-map statement quantifies over the bundled completely positive trace-preserving maps
of Physlib. The Kraus-family statement quantifies over finite families of matrices with
$`\sum_iK_i^*K_i=1`$ and uses only Mathlib, which is the form needed for Formal Conjectures.

The two statements are equivalent. Every Kraus family defines a bundled channel with the same
action and the same Holevo information, and every bundled channel has a Kraus family. The Lean
proof establishes the CPTP-map statement first and derives the Kraus-family statement from it.

### Lean comparison: CPTP-map statement vs Kraus-family statement

The CPTP-map statement is `QubitAdditivity.GeneralQubitStrongAdditivity`
([Target.lean](lean/QubitAdditivity/Target.lean)), proved as
`QubitAdditivity.GeneralResult.generalQubitStrongAdditivity`
([GeneralResult.lean](lean/QubitAdditivity/GeneralResult.lean)).

```lean
def GeneralQubitStrongAdditivity : Prop :=
  ∀ (Φ : CPTPMap (Fin 2) (Fin 2)) (n m : ℕ),
    ∀ Ω : CPTPMap (Fin (n + 1)) (Fin (m + 1)),
      holevo (Φ ⊗ᶜᵖ Ω) = holevo Φ + holevo Ω
```

The Kraus-family statement is `QubitHolevo.strong_additivity`, shown in the
[Formal Conjectures target](#formal-conjectures-target). Its five definitions are the following
([Presentation/Model.lean](lean/QubitAdditivity/Presentation/Model.lean)).

```lean
def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.negMulLog P).trace.re

def IsKraus {ι κ ρ : Type*} [Fintype ι] [DecidableEq κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

def holevo {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : ℝ :=
  let Φ (P : Matrix κ κ ℂ) : Matrix ι ι ℂ := ∑ i, K i * P * (K i)ᴴ
  sSup {x | ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Matrix κ κ ℂ),
    (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ (∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1) ∧
    x = entropy (Φ (∑ a, p a • σ a)) - ∑ a, p a * entropy (Φ (σ a))}

def tensorKraus {ι κ ρ ι' κ' ρ' : Type*} (K : ρ → Matrix ι κ ℂ) (L : ρ' → Matrix ι' κ' ℂ) :
    ρ × ρ' → Matrix (ι × ι') (κ × κ') ℂ :=
  fun i ↦ K i.1 ⊗ₖ L i.2

def powerKraus {ι κ ρ : Type*} (K : ρ → Matrix ι κ ℂ) (n : ℕ) :
    (Fin n → ρ) → Matrix (Fin n → ι) (Fin n → κ) ℂ :=
  fun i a b ↦ ∏ k, K (i k) (a k) (b k)
```

The equivalence is proved in
[FCPresentation.lean](lean/QubitAdditivity/FCPresentation.lean): `channel` is the bundled
channel of a Kraus family, `channel_m` and `holevo_eq` say that it has the same action and the
same Holevo information, and `exists_channel_eq` says that every bundled channel arises in this
way.

## Appendix: Verification by Lean Comparator on GitHub CI runner

Lean Comparator checks the theorem statements and dependent definitions against the challenge,
audits permitted axioms and verifies kernel acceptance.

GitHub CI runs checks in a fresh environment and records their results;
pinned inputs support reproducibility.

The verification target is in
[ComparatorChallenges/QubitHolevoAdditivity.lean](lean/ComparatorChallenges/QubitHolevoAdditivity.lean),
and the proof is in [QubitAdditivity/FCPresentation.lean](lean/QubitAdditivity/FCPresentation.lean).
The challenge states `QubitHolevo.strong_additivity` and `QubitHolevo.power_additivity` with the
definitions of the Formal Conjectures statement, and it imports only Mathlib.

Lean Comparator and GitHub CI enable the following:

- **Verification in a web browser (within 90 days):** see [CI results](#certification-within-90-days-ci-results).
- **Verification from an archive (after 90 days):** see [archived records](#certification-after-90-days-archive).
- **Regenerate and verify the results yourself:** see [how to run the checks on your own CI runner](#reproduce-the-verification).

### Certification Within 90 days: CI results

Readers who want to inspect the verification results can check the Comparator execution
and axiom audit in the CI logs within 90 days. In particular, `#print axioms` reports the
three axioms for both targets and for the original theorem:

```text
'QubitHolevo.strong_additivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QubitHolevo.power_additivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QubitAdditivity.GeneralResult.generalQubitStrongAdditivity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [public CI run](https://github.com/KitaKen1/qubit-strong-additivity/actions/runs/38265719873)
on `main` passed on 12 October 2026 (UTC; tested commit `00e8210`); its logs and artifacts can be
inspected on GitHub until 10 January 2027.

### Certification After 90 days: archive

After the [90-day retention period](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts)
for CI logs and artifacts expires, readers can inspect the same results in the archive.
Archived CI run records, logs, artifacts and checksums also allow file integrity checks.
The archive is [ComparatorLog20261012/38265719873-attempt1/](ComparatorLog20261012/38265719873-attempt1/); see its
[guide](ComparatorLog20261012/38265719873-attempt1/README.md).

### Reproduce the verification

To run the verification yourself, clone the repository, push it to a GitHub repository
you control, and run the [verification workflow](.github/workflows/comparator.yml) from
**Actions → Run workflow**. Your CI runner executes the same checks; compare the Comparator
result and the three-axiom output with the recorded results.
Setup and commands are in [comparator/README.md](comparator/README.md).
