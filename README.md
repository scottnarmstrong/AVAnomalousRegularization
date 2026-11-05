# Anomalous regularization of passive scalars up to the Obukhov–Corrsin exponent, formalized in Lean 4

[![Build](https://github.com/scottnarmstrong/AVAnomalousRegularization/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/AVAnomalousRegularization/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/AVAnomalousRegularization/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/AVAnomalousRegularization/actions/workflows/comparators.yml)

A complete, machine-checked proof of the results of

> S. Armstrong and V. Vicol, *Anomalous regularization of passive scalars up to the
> Obukhov–Corrsin exponent*, 2026 ([doc/paper.pdf](doc/paper.pdf)).

The paper studies the advection–diffusion equation

```math
\partial_t\theta+\mathbf b\cdot\nabla\theta-\kappa\Delta\theta=0 \quad\text{in } (t_{\mathsf{in}},\infty)\times\mathbb T^2,\qquad \theta(t_{\mathsf{in}},\cdot)=\theta_{\mathsf{in}} \quad\text{on } \mathbb T^2,
```

on the torus $\mathbb T^2=\mathbb R^2/\mathbb Z^2$, where $\mathbf b$ is a velocity field constructed as in
[[AV25]](#references): a divergence-free field built from shear flows that alternate in direction at
infinitely many scales, Hölder continuous with an exponent $\alpha\lt\frac13$. It proves
*anomalous regularization*: for every $s$ below the Obukhov–Corrsin exponent $\frac12(1-\alpha)$,
with $\mathbf b$ depending on $s$, at positive times the solutions are bounded in
$C^{0,s}(\mathbb T^2)$ by a constant times the $L^2(\mathbb T^2)$ norm of the initial datum,
uniformly in the diffusivity $\kappa$ in a union of bands accumulating at $0$ (Theorem A). As a consequence, every solution
dissipates a fixed fraction of its variance in every unit of time, and the variance decays
exponentially, with constants independent of $\kappa$, of the datum in $L^2(\mathbb T^2)$ and of
the initial time (Theorem B). The paper also localizes Theorem A to space–time tubes that follow
the trajectories of a coarse velocity field $\mathbf b_m$ (Theorem C), and passes to the limit $\kappa\to0$
(Corollary D).

The formalization is written in Lean 4 on top of Mathlib and builds on the
[formalization of [AV25]](https://github.com/scottnarmstrong/AVAnomalousDiffusion). It contains
Theorems A, B and C, Corollary D and every statement of Part I of the paper; the propositions and
lemmas of Part II follow from its formal statements, directly or by elementary steps, or are
proved, where they are used, inside its formal proofs. The
[correspondence table](doc/correspondence.md) maps every numbered statement and display of the
paper to the Lean declarations that prove it, or says why none is needed (figures, attributions,
heuristics). The library contains no `sorry` and uses no axioms
beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

## The setting

Statement and equation numbers are those of the paper, [doc/paper.pdf](doc/paper.pdf), as in
[AVRegularityChallenge.lean](AVRegularityChallenge.lean),
[AVRegularitySolution.lean](AVRegularitySolution.lean) and the
[correspondence table](doc/correspondence.md). The comments of the library under
[AVRegularity](AVRegularity) cite earlier versions of the paper, whose numbers differ: there, for
example, the construction is Section 1 with the displays (1.1)–(1.18), which are Section 2 and
(2.1)–(2.18) here.

Fix

- $\alpha\in(0,\frac13)$, the Hölder exponent of the velocity field, and $\beta:=1+\alpha$;
- $s\in(0,\frac12(1-\alpha))$, the Hölder exponent obtained for the solutions;
- $q$ with
  $1\lt q\lt\min\bigl\lbrace\frac{17}{16},\frac{2-\beta}{2(\beta-1)},\frac{1-s}{\beta-1+s}\bigr\rbrace$
  (2.1), which holds for every $q\gt1$ close enough to $1$;
- an integer $\Lambda\ge128$;
- an even cutoff function $\zeta\in C^\infty_c((-\frac23,\frac23))$ with, as in (2.2),
  $0\le\zeta\le1$, $\sum_{k\in\mathbb Z}\zeta(\cdot-k)=1$ and $\int_{\mathbb R}\zeta^2=\frac9{10}$.

With $\gamma:=\frac{(q-1)\beta}{q+1}$ and
$\delta:=\frac14(q-1)\bigl(1-\frac{(2q+1)\beta}{2q+2}\bigr)$ (2.3), level $m\ge1$ has the
wavelength $\varepsilon_m$ and the renewal time $h_m$ of (2.4),

```math
\varepsilon_0:=1,\qquad \varepsilon_m:=\bigl\lceil\Lambda^{q^m/(q-1)}\bigr\rceil^{-1},\qquad h_m:=\frac{2^{-25}}{\bigl\lceil\varepsilon_{m-1}^{-(2-\beta+2\delta)}\bigr\rceil}.
```

Starting from $\phi_0:=0$, the stream functions and velocity fields are defined by the recursion
(2.12),

```math
\phi_m(t,x):=\phi_{m-1}(t,x)+\sum_{k\in\mathbb Z}\widetilde\zeta_{m,k}(t)\,\psi_{m,k}\bigl(X_{m-1}(l_{m,k}h_m,x,t)\bigr),\qquad \mathbf b_m:=\nabla^\perp\phi_m=(-\partial_2\phi_m,\partial_1\phi_m),
```

where $\psi_{m,k}(y)$ is the shear stream $\varepsilon_m^\beta\sin(2\pi y_1/\varepsilon_m)$ for
$k\in4\mathbb Z+1$, $\varepsilon_m^\beta\sin(2\pi y_2/\varepsilon_m)$ for $k\in4\mathbb Z+3$, and
$0$ for even $k$; the envelope $\widetilde\zeta_{m,k}$ switches pulse $k$ on for a time of order
$\tau_m=h_m/(4\lceil\varepsilon_{m-1}^{-\delta}\rceil+1)^2$ around $k\tau_m$, inside the renewal
block $[(l-\frac12)h_m,(l+\frac12)h_m]$ of its label $l=l_{m,k}$ and away from the ends of the
block; and $X_{m-1}(t',x,t)$ is the position at time $t'$ of the trajectory of $\mathbf b_{m-1}$
through $x$ at time $t$. The velocity fields $\mathbf b_m$ converge pointwise to a velocity field
$\mathbf b$ which is bounded, $\mathbb Z^2$-periodic in space, $1$-periodic in time, divergence
free, and Hölder continuous with exponent $\alpha$ jointly in time and space (2.15). It is the
velocity field of [[AV25]](#references), except that the parameter $q$, which [[AV25]](#references)
fixes in terms of $\alpha$, is free here, taken close to $1$ depending on $\alpha$ and $s$. The permitted diffusivities are the union of the bands
(2.18),

```math
\mathcal K_M:=\bigl[\tfrac12\varepsilon_M^{\beta-\gamma},\ 2\varepsilon_M^{\beta-\gamma}\bigr],\quad M\ge1,\qquad \mathcal K:=\bigcup_{M\ge1}\mathcal K_M ,
```

which are disjoint and accumulate at $0$. For a $\mathbb Z^2$-periodic function $g$, with
$\vert x-y\vert_{\mathbb T^2}$ the distance on the torus, (3.1) is

```math
\Vert g\Vert_{C^{0,s}(\mathbb T^2)}:=\sup_{\mathbb T^2}\vert g\vert+\sup_{x\ne y}\frac{\vert g(x)-g(y)\vert}{\vert x-y\vert_{\mathbb T^2}^s}.
```

A *weak solution* on $(t_{\mathsf{in}},t_{\mathsf{in}}+T)$ of the initial-value problem is a function
$\theta\in L^\infty((t_{\mathsf{in}},t_{\mathsf{in}}+T);L^2(\mathbb T^2))$ with $\nabla\theta\in L^2((t_{\mathsf{in}},t_{\mathsf{in}}+T)\times\mathbb T^2)$,
weakly continuous in $L^2(\mathbb T^2)$, which solves the equation in the sense of distributions
and takes the initial value; a weak solution on $(t_{\mathsf{in}},\infty)$ is a weak solution on $(t_{\mathsf{in}},t_{\mathsf{in}}+T)$ for
every $T\gt0$.

## The main results

All main results are in [AVRegularity/Statements/Main](AVRegularity/Statements/Main), one theorem
per file, in the namespace `AVRegularity`. Theorems A and B are stated twice: for the
construction itself, and in an existential form, which asserts that some velocity field with the
stated regularity and some bands have the property. Theorem C and Corollary D are stated for the
construction. The blocks below are the exact Lean statements.

### Theorem A (interior regularity)

> Let $\alpha\in(0,\frac13)$, $s\in(0,\frac12(1-\alpha))$, let $q$ satisfy (2.1) and $\zeta$
> satisfy (2.2). There exists $\Lambda_0(\alpha,s,q,\zeta)\ge128$ such that, for every integer
> $\Lambda\ge\Lambda_0$, the velocity field $\mathbf b$ has the following property. For every
> $0\lt t_0\lt T$ there exists $C(\alpha,s,q,\zeta,\Lambda,t_0,T)\lt\infty$ such that, for every
> $t_{\mathsf{in}}\in\mathbb R$, $\kappa\in\mathcal K$ and $\theta_{\mathsf{in}}\in L^2(\mathbb T^2)$, every weak solution $\theta$ of
>
> ```math
> \partial_t\theta+\mathbf b\cdot\nabla\theta-\kappa\Delta\theta=0 \quad\text{in } (t_{\mathsf{in}},t_{\mathsf{in}}+T)\times\mathbb T^2,\qquad \theta(t_{\mathsf{in}},\cdot)=\theta_{\mathsf{in}} \quad\text{on } \mathbb T^2,
> ```
>
> satisfies
>
> ```math
> \Vert\theta\Vert_{L^\infty([t_{\mathsf{in}}+t_0,t_{\mathsf{in}}+T];C^{0,s}(\mathbb T^2))}\le C\Vert \theta_{\mathsf{in}}\Vert_{L^2(\mathbb T^2)}.
> ```

For the construction: `AVRegularity.interior_regularity_construction`, in
[InteriorRegularityConstruction.lean](AVRegularity/Statements/Main/InteriorRegularityConstruction.lean).

```lean
theorem interior_regularity_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ,
            ∀ κ ∈ ocBandSet α q Λ,
            ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
                ∃ Θ : ℝ → Vec 2 → ℝ,
                  ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                    (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                  ∀ t ∈ Set.Icc (a + t₀) (a + T),
                    IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                    CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))
```

Existential form: `AVRegularity.interior_regularity`, in
[InteriorRegularity.lean](AVRegularity/Statements/Main/InteriorRegularity.lean). For every $\alpha$
and $s$ in these ranges there are a velocity field $\mathbf b\in C^\alpha$ and disjoint bands
$[\kappa_c(M)/2,2\kappa_c(M)]$, accumulating at $0$, with the property of Theorem A.

```lean
theorem interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))
```

### Theorem B (uniform anomalous dissipation)

> Let $\alpha$, $s$, $q$, $\zeta$ and $\Lambda_0$ be as in Theorem A, and let $\Lambda\ge\Lambda_0$ be
> an integer. For the velocity field $\mathbf b$, there exists $c(\alpha,s,q,\zeta,\Lambda)\gt0$ such
> that, for every $t_{\mathsf{in}}\in\mathbb R$, $\kappa\in\mathcal K$ and $\theta_{\mathsf{in}}\in L^2(\mathbb T^2)$, every weak
> solution $\theta$ of
>
> ```math
> \partial_t\theta+\mathbf b\cdot\nabla\theta-\kappa\Delta\theta=0 \quad\text{in } (t_{\mathsf{in}},\infty)\times\mathbb T^2,\qquad \theta(t_{\mathsf{in}},\cdot)=\theta_{\mathsf{in}} \quad\text{on } \mathbb T^2,
> ```
>
> satisfies
>
> ```math
> \kappa\Vert\nabla\theta\Vert_{L^2((t_{\mathsf{in}},t_{\mathsf{in}}+1)\times\mathbb T^2)}^2\ge c\,\bigl\Vert \theta_{\mathsf{in}}-(\theta_{\mathsf{in}})_{\mathbb T^2}\bigr\Vert_{L^2(\mathbb T^2)}^2
> ```
>
> and, for every $t\ge t_{\mathsf{in}}$,
>
> ```math
> \bigl\Vert\theta(t,\cdot)-(\theta_{\mathsf{in}})_{\mathbb T^2}\bigr\Vert_{L^2(\mathbb T^2)}\le2\exp(-c(t-t_{\mathsf{in}}))\bigl\Vert \theta_{\mathsf{in}}-(\theta_{\mathsf{in}})_{\mathbb T^2}\bigr\Vert_{L^2(\mathbb T^2)}.
> ```

Here $`(\theta_{\mathsf{in}})_{\mathbb T^2}`$ is the mean of $\theta_{\mathsf{in}}$. Since the bands accumulate at $0$, it follows that,
for every mean-zero $\theta_{\mathsf{in}}\in L^2(\mathbb T^2)$, the weak solutions $\theta^\kappa$ with datum $\theta_{\mathsf{in}}$ at
time $0$ satisfy
$\liminf_{\kappa\to0,\ \kappa\in\mathcal K}\kappa\Vert\nabla\theta^\kappa\Vert_{L^2((0,1)\times\mathbb T^2)}^2\ge c\Vert \theta_{\mathsf{in}}\Vert_{L^2(\mathbb T^2)}^2$.

For the construction: `AVRegularity.uniform_anomalous_dissipation_construction`, in
[UniformAnomalousDissipationConstruction.lean](AVRegularity/Statements/Main/UniformAnomalousDissipationConstruction.lean).

```lean
theorem uniform_anomalous_dissipation_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                    κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, a < t →
              (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
                l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
                  4 * Real.exp (-2 * c * (t - a)) *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y))
```

Existential form: `AVRegularity.uniform_anomalous_dissipation`, in
[UniformAnomalousDissipation.lean](AVRegularity/Statements/Main/UniformAnomalousDissipation.lean).

```lean
theorem uniform_anomalous_dissipation (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
            c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
              κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        ∀ t : ℝ, a < t →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
          l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
            4 * Real.exp (-2 * c * (t - a)) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y))
```

Theorems A and B hold for one and the same velocity field and bands:
`AVRegularity.interior_regularity_and_dissipation`, in
[InteriorRegularityAndDissipation.lean](AVRegularity/Statements/Main/InteriorRegularityAndDissipation.lean).

<details>
<summary>Lean statement of <code>interior_regularity_and_dissipation</code></summary>

```lean
theorem interior_regularity_and_dissipation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
            c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
              κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        ∀ t : ℝ, a < t →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
          l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
            4 * Real.exp (-2 * c * (t - a)) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y))
```

</details>

### Theorem C (local interior regularity)

For an integer $m\ge0$, a radius $r_{\mathrm{tube}}\gt0$ and a final time $t_{\mathrm f}\in\mathbb R$,
the *tube* (9.11) is the disc $D_{r_{\mathrm{tube}}}$ carried by the trajectories of
$\mathbf b_m$ over the time $8h_{m+1}$,

```math
\mathcal T:=\bigl\lbrace(t,X_m(t,y,t_{\mathrm f})) : t_{\mathrm f}-8h_{m+1}\lt t\lt t_{\mathrm f},\ \vert y\vert\lt r_{\mathrm{tube}}\bigr\rbrace .
```

For $\kappa\gt0$, a *local energy solution* (9.12) of
$\partial_t\theta+\mathbf b\cdot\nabla\theta-\kappa\Delta\theta=0$ in $\mathcal T$ is a function
$\theta\in L^2(\mathcal T)$ such that
$\int_{\mathcal T}\theta(\partial_tg+\mathbf b\cdot\nabla g+\kappa\Delta g)=0$ for every
$g\in C^\infty_c(\mathcal T)$, and such that $U(t,y):=\theta(t,X_m(t,y,t_{\mathrm f}))$ satisfies
$U\in L^\infty((t_{\mathrm f}-8h_{m+1},t_{\mathrm f});L^2(D_{r_{\mathrm{tube}}}))$ and
$\nabla_yU\in L^2((t_{\mathrm f}-8h_{m+1},t_{\mathrm f})\times D_{r_{\mathrm{tube}}})$. No lateral
data are prescribed.

> In the setting of Theorem A, with $\Lambda_0$ as there, let $\Lambda\ge\Lambda_0$ be an integer.
> There exists $C_1(\alpha,s,q,\zeta,\Lambda)\ge1$ with the following property. Let $m\ge0$ be an
> integer and let $r_{\mathrm{tube}}$ satisfy
>
> ```math
> C_1\max\bigl\lbrace\varepsilon_{m+1}^\alpha h_{m+1},\ (h_{m+1}\sup\mathcal K)^{1/2}\bigr\rbrace\le r_{\mathrm{tube}}\le\frac18 .
> ```
>
> For every $0\lt r_{\mathrm{obs}}\lt\frac18r_{\mathrm{tube}}$ and $4h_{m+1}\lt t_0\lt8h_{m+1}$ there
> exists $C(\alpha,s,q,\zeta,\Lambda,m,r_{\mathrm{tube}},r_{\mathrm{obs}},t_0)\lt\infty$ such that, for
> every $t_{\mathrm f}\in\mathbb R$, every $\kappa\in\mathcal K$ and every local energy solution
> $\theta$ in the tube $\mathcal T$, with $U(t,y):=\theta(t,X_m(t,y,t_{\mathrm f}))$, the following
> hold. For every $t\in[t_{\mathrm f}-8h_{m+1}+t_0,t_{\mathrm f}]$, $U(t',\cdot)$ converges in
> $L^2(D_{r_{\mathrm{obs}}})$ as $t'\uparrow t$ to a continuous function $U(t,\cdot)$. Moreover,
>
> ```math
> \Vert U\Vert_{L^\infty([t_{\mathrm f}-8h_{m+1}+t_0,\,t_{\mathrm f}];C^{0,s}(D_{r_{\mathrm{obs}}}))}\le C\Bigl(\frac1{\vert\mathcal T\vert}\int_{\mathcal T}\theta(t,x)^2\,\mathrm dt\,\mathrm dx\Bigr)^{1/2}.
> ```

Lean: `AVRegularity.local_interior_regularity`, in
[LocalInteriorRegularity.lean](AVRegularity/Statements/Main/LocalInteriorRegularity.lean). The
dictionary is under [Reading the Lean statements](#reading-the-lean-statements).

<details>
<summary>Lean statement of <code>local_interior_regularity</code></summary>

```lean
theorem local_interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R ϱ ϑ : ℝ), 2 ≤ n → 0 < T → 0 < R → 0 < ϱ → ϱ < 1 / 8 →
              0 < ϑ → ϑ < 4 →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
                  IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
                  ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
                    Tendsto (fun r => ∫ y in euclidBall 0 (ϱ * R),
                        (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
                      (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
                        C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2)
```

</details>

### Corollary D (vanishing-diffusivity limits)

> In the setting of Theorem A, with $\Lambda_0$ as there, let $\Lambda\ge\Lambda_0$ be an integer.
>
> (a) There exist constants $C(\alpha,s,q,\zeta,\Lambda,t_0,T)$, $0\lt t_0\lt T$, with the following
> property. Let $t_{\mathsf{in}}\in\mathbb R$, let $\mathcal K'\subset\mathcal K$ be an infinite subset with $0$ as its only
> accumulation point, and, for $\kappa\in\mathcal K'$, let $\theta_{\mathsf{in}}^\kappa\in L^2(\mathbb T^2)$ with
> $\sup_{\kappa\in\mathcal K'}\Vert \theta_{\mathsf{in}}^\kappa\Vert_{L^2(\mathbb T^2)}\lt\infty$, let $\theta^\kappa$ be
> the weak solution on $(t_{\mathsf{in}},\infty)$ with datum $\theta_{\mathsf{in}}^\kappa$ at time $t_{\mathsf{in}}$, and, with $M$ such that
> $\kappa\in\mathcal K_M$, let $\widetilde\theta^\kappa$ be the weak solution of the same problem with
> $\mathbf b_M$ in place of $\mathbf b$. Then every $\theta^\kappa$ is continuous on
> $(t_{\mathsf{in}},\infty)\times\mathbb T^2$, and there exist an infinite subset $\mathcal K''\subset\mathcal K'$,
> $\theta_{\mathsf{in},\ast}\in L^2(\mathbb T^2)$ and a continuous function $\theta_\ast$ on $(t_{\mathsf{in}},\infty)\times\mathbb T^2$
> such that:
>
> - (i) $\theta_{\mathsf{in}}^\kappa\rightharpoonup \theta_{\mathsf{in},\ast}$ weakly in $L^2(\mathbb T^2)$, and $\theta^\kappa\to\theta_\ast$
>   locally uniformly on $(t_{\mathsf{in}},\infty)\times\mathbb T^2$, as $\kappa\to0$ in $\mathcal K''$;
> - (ii) $\partial_t\theta_\ast+\nabla\cdot(\mathbf b\theta_\ast)=0$ in the sense of distributions on
>   $(t_{\mathsf{in}},\infty)\times\mathbb R^2$, and $\theta_\ast(t,\cdot)\rightharpoonup \theta_{\mathsf{in},\ast}$ weakly in
>   $L^2(\mathbb T^2)$ as $t\downarrow t_{\mathsf{in}}$;
> - (iii) for every $0\lt t_0\lt T$,
>   $\Vert\theta_\ast\Vert_{L^\infty([t_{\mathsf{in}}+t_0,t_{\mathsf{in}}+T];C^{0,s}(\mathbb T^2))}\le C(t_0,T)\sup_{\kappa\in\mathcal K'}\Vert \theta_{\mathsf{in}}^\kappa\Vert_{L^2(\mathbb T^2)}$,
>   and $\theta_\ast$ is Hölder continuous in time on $[t_{\mathsf{in}}+t_0,t_{\mathsf{in}}+T]\times\mathbb T^2$, uniformly in
>   space, with exponent $s/(1+s)$;
> - (iv) $\theta^\kappa-\widetilde\theta^\kappa\to0$ in the sense of distributions on
>   $(t_{\mathsf{in}},\infty)\times\mathbb R^2$ as $\kappa\to0$ in $\mathcal K'$.
>
> (b) Let $C_1$, $m$, $r_{\mathrm{tube}}$, $t_{\mathrm f}$ and the tube $\mathcal T$ be as in
> Theorem C, and let
> $\mathcal T':=\lbrace(t,X_m(t,y,t_{\mathrm f})) : t_{\mathrm f}-4h_{m+1}\lt t\le t_{\mathrm f},\ \vert y\vert\lt\frac18r_{\mathrm{tube}}\rbrace$.
> There exist constants $C(\alpha,s,q,\zeta,\Lambda,m,r_{\mathrm{tube}},r_{\mathrm{obs}},t_0)$,
> $0\lt r_{\mathrm{obs}}\lt\frac18r_{\mathrm{tube}}$ and $4h_{m+1}\lt t_0\lt8h_{m+1}$, with the
> following property. Let $\mathcal K'\subset\mathcal K$ be an infinite subset with $0$ as its only
> accumulation point, and let $\theta^\kappa$, $\kappa\in\mathcal K'$, be local energy solutions in
> $\mathcal T$ with
> $\sup_{\kappa\in\mathcal K'}\frac1{\vert\mathcal T\vert}\int_{\mathcal T}(\theta^\kappa)^2\lt\infty$.
> Then every $\theta^\kappa$ is continuous on $\mathcal T'$, and there exist an infinite subset
> $\mathcal K''\subset\mathcal K'$ and a continuous function $\theta_\ast$ on $\mathcal T'$ such that
> $\theta^\kappa\to\theta_\ast$ uniformly on the compact subsets of $\mathcal T'$ as $\kappa\to0$ in
> $\mathcal K''$; the function $\theta_\ast$ satisfies
> $\partial_t\theta_\ast+\nabla\cdot(\mathbf b\theta_\ast)=0$ in the sense of distributions in the
> interior of $\mathcal T'$ and, for every $0\lt r_{\mathrm{obs}}\lt\frac18r_{\mathrm{tube}}$ and
> $4h_{m+1}\lt t_0\lt8h_{m+1}$, with $U_\ast(t,y):=\theta_\ast(t,X_m(t,y,t_{\mathrm f}))$,
>
> ```math
> \Vert U_\ast\Vert_{L^\infty([t_{\mathrm f}-8h_{m+1}+t_0,\,t_{\mathrm f}];C^{0,s}(D_{r_{\mathrm{obs}}}))}\le C\sup_{\kappa\in\mathcal K'}\Bigl(\frac1{\vert\mathcal T\vert}\int_{\mathcal T}\theta^\kappa(t,x)^2\,\mathrm dt\,\mathrm dx\Bigr)^{1/2}.
> ```

The conclusion is subsequential: for the velocity field of [[AV25]](#references) with $\alpha\ge\frac1{67}$, vanishing
diffusivity does not select a unique limit ([[AV25]](#references), Proposition 5.5).

Lean: part (a) is `AVRegularity.vanishing_diffusivity_limits`, in
[VanishingDiffusivityLimits.lean](AVRegularity/Statements/Main/VanishingDiffusivityLimits.lean);
part (b) is `AVRegularity.vanishing_diffusivity_limits_local`, in
[VanishingDiffusivityLimitsLocal.lean](AVRegularity/Statements/Main/VanishingDiffusivityLimitsLocal.lean).

<details>
<summary>Lean statement of <code>vanishing_diffusivity_limits</code></summary>

```lean
theorem vanishing_diffusivity_limits (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∃ Cthm : ℝ → ℝ → ℝ,
          ∀ (a F : ℝ) (κ : ℕ → ℝ) (f : ℕ → Vec 2 → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
            (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
            (∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F) →
            (∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i)) →
            ∃ (σ : ℕ → ℕ) (fstar : Vec 2 → ℝ) (Θ : ℕ → ℝ → Vec 2 → ℝ)
                (θstar : ℝ → Vec 2 → ℝ),
              StrictMono σ ∧ MemL2On unitCube fstar ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
                ∀ t, a < t → IsZ2Periodic (Θ i t) ∧ Θ i t =ᵐ[volume.restrict unitCube] θ i t) ∧
              TendstoLocallyUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) ∧
              (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                ∫ p, θstar p.1 p.2 *
                  (fderiv ℝ φ p (1, 0) + ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j))
                  = 0) ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun t => ∫ x in unitCube, θstar t x * g x) (𝓝[>] a)
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
                IsZ2Periodic (θstar t) ∧ CsNormLe s (θstar t) (Cthm t₀ T * F)) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C' : ℝ,
                ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T), ∀ x : Vec 2,
                  |θstar t x - θstar t' x| ≤ C' * |t - t'| ^ (s / (1 + s))) ∧
              (∀ (Mi : ℕ → ℕ) (θ' : ℕ → ℝ → Vec 2 → ℝ),
                (∀ i, 1 ≤ Mi i ∧ κ i ∈ Set.Icc
                  (ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q) / 2)
                  (2 * ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q))) →
                (∀ i, ∀ T : ℝ, 0 < T →
                  IsWeakSolutionOn (streamVel (Φ (Mi i))) (κ i) a (a + T) (f i) (θ' i)) →
                ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                  tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0))
```

</details>

<details>
<summary>Lean statement of <code>vanishing_diffusivity_limits_local</code></summary>

```lean
theorem vanishing_diffusivity_limits_local (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R : ℝ), 2 ≤ n → 0 < T → 0 < R →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
                  (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
                  (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i)) →
                  (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F) →
                  ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
                    StrictMono σ ∧
                    (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2)
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                      (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}]
                        (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
                    (∀ K ⊆ {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}, IsCompact K →
                      TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
                    ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2)
                      {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                        ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                    (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                      tsupport φ ⊆ interior {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} →
                      ∫ p, θstar p.1 p.2 *
                        (fderiv ℝ φ p (1, 0) +
                          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
                    ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
                    ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |θstar t x| + |θstar t y - θstar t z| /
                        Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ϱ ϑ * F
```

</details>

### Reading the Lean statements

In the Lean statements, the initial time and the initial datum are the binders `a` and `f`, the
paper's $t_{\mathsf{in}}$ and $\theta_{\mathsf{in}}$.

- **Space and the torus.** Space is `Vec 2 = Fin 2 → ℝ`. Functions on $\mathbb T^2$ are
  $\mathbb Z^2$-periodic functions on $\mathbb R^2$ (`IsZ2Periodic`), and integrals over
  $\mathbb T^2$ are integrals over the open unit square `unitCube`: `l2NormSq f` is
  $\Vert f\Vert_{L^2(\mathbb T^2)}^2$, and `∫ y in unitCube, f y` is the mean
  $`(f)_{\mathbb T^2}`$. A datum is a function `f` with `MemL2On unitCube f`; only its values on the
  unit square enter. The norm `‖·‖` of `Vec 2` is the maximum of the moduli of the coordinates;
  it enters only the boundedness and the Hölder bound of the velocity field, where every norm
  gives the same class.
- **The velocity field.** In the forms for the construction, `IsOCStreamSeq α q Λ ζ Φ` says that
  `Φ m` is the stream function $\phi_m$ of the recursion (2.12) for every $m$, so that
  `streamVel (Φ M)` is $\mathbf b_M$, and `b` is the pointwise limit of the $\mathbf b_M$. The
  recursion determines `Φ`. The forms of Theorems A and B for the construction also assert that it
  can be carried out for every $\Lambda\ge\Lambda_0$; for Theorem C and Corollary D this is
  [`exists_isOCStreamSeq`](AVRegularity/Statements/Construction/ExistsOCStreamSeq.lean), which holds
  for every integer $\Lambda\ge128$.
- **Existential forms.** `interior_regularity`, `uniform_anomalous_dissipation` and
  `interior_regularity_and_dissipation` assume only the range of $\alpha$, and that of $s$ where
  it appears. They assert that some `b` with `IsHolderDivFreeVelocity α b` and some band centres
  $\kappa_c(M)\gt0$ with $4\kappa_c(M+1)\lt\kappa_c(M)$, so that the bands
  $[\kappa_c(M)/2,2\kappa_c(M)]$ are disjoint and accumulate at $0$, have the property of the
  theorem.
- **Bounds at every time.** Where the paper bounds a norm in $L^\infty$ in time, the Lean
  statement gives the bound at every time: for every $t\in[a+t_0,a+T]$, a periodic function
  `Θ t`, equal to `θ t` almost everywhere and jointly continuous in $(t,x)$, with
  `CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))`. Theorems A and B also assert that the weak
  solutions exist.
- **Theorem B.** The dissipation bound is stated on $[a,a+1]$ for every weak solution with its
  gradient `Dθ` named (`IsWeakSolutionOnGrad`). The decay bound is stated squared,
  $`\Vert\theta(t)-(f)_{\mathbb T^2}\Vert^2\le4e^{-2c(t-a)}\Vert f-(f)_{\mathbb T^2}\Vert^2`$, for
  every $t\gt a$ and every weak solution on $[a,t]$; at $t=a$ it is trivial.
- **Theorem C.** The Lean statement is the paper's with $n=m+2$, $T=h_{m+1}$
  (`ocTauPP α q Λ (n - 1)`), $R=r_{\mathrm{tube}}$, $\varrho=r_{\mathrm{obs}}/r_{\mathrm{tube}}$,
  $\vartheta=8-t_0/h_{m+1}$, $t_1=t_{\mathrm f}$, and `X` a flow of $\mathbf b_m$ (`IsFlow`), so
  that `outerPipe (fun t y => X t y t₁) t₁ T R` is the tube $\mathcal T$. More generally it allows
  every $T$ with $c_Th_{m+1}\le T\le C_Th_{m+1}$ and $8Ta_m\le c_\ast$, where
  $a_m=\varepsilon_m^{\beta-2}$ (`ocA`) and $c_\ast$ is the absolute constant `ocCStar`; for
  $T=h_{m+1}$ the last condition holds, since (2.13) gives $8h_{m+1}a_m\le2^{-22}$ and
  $2^{-22}\lt c_\ast$. The bound is stated for $\theta(t,\cdot)$ on
  the moving disc $X_m(t,D_{r_{\mathrm{obs}}},t_{\mathrm f})$, with Euclidean distances; since
  $X_m(t,\cdot,t_{\mathrm f})$ is $2$-Lipschitz, it gives the paper's bound for $U$ with $2C$ in
  place of $C$. The convergence of $U(t',\cdot)$ as $t'\uparrow t$ is along $t'$ outside a null
  set.
- **Corollary D.** The sequence $\mathcal K'$ is a sequence `κ i → 0` in $\mathcal K$, and the
  subsequence is given by a strictly increasing `σ`. The data, or the root mean squares over the
  tube, are bounded by a number `F`, and the constants multiply `F`. The convergence is that of
  continuous versions `Θ i` of the solutions. The transport equation is tested against smooth,
  compactly supported functions on $(a,\infty)\times\mathbb R^2$, or on the interior of
  $\mathcal T'$. In (a)(iv), the solutions $\widetilde\theta^\kappa$ come with any choice of `Mi i`
  such that `κ i` lies in $\mathcal K_{M_i}$.

## Definitions

The definitions that the main results use, with the paper's notation. Those of this library are in
[AVRegularity/Statements/Definitions](AVRegularity/Statements/Definitions) and
[AVRegularity/Statements/Construction](AVRegularity/Statements/Construction).

**Solutions and norms.**

| Lean | Meaning |
|---|---|
| [`IsHolderDivFreeVelocity α b`](AVRegularity/Statements/Definitions/IsHolderDivFreeVelocity.lean) | $\mathbf b$ is bounded, $\mathbb Z^2$-periodic in space and $1$-periodic in time, satisfies $\vert\mathbf b(t,x)-\mathbf b(u,y)\vert\le C(\vert t-u\vert+\vert x-y\vert)^\alpha$ as in (2.15), and is divergence free in the sense of distributions on every time slice |
| [`IsWeakSolutionOn b κ t₁ t₂ f θ`](AVRegularity/Statements/Definitions/IsWeakSolutionOn.lean) | $\theta$ is a weak solution on $[t_1,t_2]$ with datum $f$ at $t_1$: $\theta(t)$ is periodic and in $L^2(\mathbb T^2)$, bounded uniformly in $t$; $\theta$ has a spatial weak gradient in $L^2$ and $\theta(t)\in H^1(\mathbb T^2)$ for almost every $t$; the drift term is integrable; $t\mapsto\int\theta(t)\psi$ is continuous on $[t_1,t_2]$ for every smooth periodic $\psi$; and the weak form of the equation holds against every window test function |
| [`IsWeakSolutionOnGrad b κ t₁ t₂ f θ Dθ`](AVRegularity/Statements/Definitions/IsWeakSolutionOnGrad.lean) | the same, with the gradient `Dθ` named |
| [`IsWindowTestFunction t₂ φ`](AVRegularity/Statements/Definitions/IsWindowTestFunction.lean) | $\varphi$ is smooth on $\mathbb R\times\mathbb R^2$, periodic in space, and vanishes for $t\ge t_2$ |
| [`CsNormLe s g K`](AVRegularity/Statements/Definitions/CsNormLe.lean) | $\vert g(x)\vert+\vert g(y)-g(z)\vert/\vert y-z\vert_{\mathbb T^2}^s\le K$ for all $x$ and all $y$, $z$ at positive torus distance, that is, $\Vert g\Vert_{C^{0,s}(\mathbb T^2)}\le K$ in the norm (3.1) |
| [`torusDist x y`](AVRegularity/Statements/Definitions/TorusDist.lean) | the distance $\vert x-y\vert_{\mathbb T^2}$ on the torus |
| [`euclidBall c r`](AVRegularity/Statements/Definitions/EuclidBall.lean) | the open disc $D_r(c)$ |
| [`outerPipe F t₁ T R`](AVRegularity/Statements/Definitions/OuterPipe.lean) | $\lbrace(t,F_t(y)) : t_1-8T\lt t\lt t_1,\ \vert y\vert\lt R\rbrace$, the tube (9.11) for $F_t=X_m(t,\cdot,t_{\mathrm f})$ and $T=h_{m+1}$ |
| [`IsLocalEnergySolution b κ F t₁ T R θ`](AVRegularity/Statements/Definitions/IsLocalEnergySolution.lean) | $\theta$ is a local energy solution (9.12) in that tube |

**The construction.**

| Lean | Meaning |
|---|---|
| [`IsAdmissibleQ α s q`](AVRegularity/Statements/Construction/IsAdmissibleQ.lean) | the bounds (2.1) on $q$ |
| [`IsFastProfile ζ`](AVRegularity/Statements/Construction/IsFastProfile.lean) | the conditions (2.2) on the cutoff function $\zeta$ |
| [`ocGamma`](AVRegularity/Statements/Construction/OcGamma.lean), [`ocDelta`](AVRegularity/Statements/Construction/OcDelta.lean) | the exponents $\gamma$ and $\delta$ of (2.3) |
| [`ocEpsilon q Λ m`](AVRegularity/Statements/Construction/OcEpsilon.lean) | the wavelength $\varepsilon_m$ |
| [`ocTauPP`](AVRegularity/Statements/Construction/OcTauPP.lean), [`ocTauP`](AVRegularity/Statements/Construction/OcTauP.lean), [`ocTau`](AVRegularity/Statements/Construction/OcTau.lean), [`ocL`](AVRegularity/Statements/Construction/OcL.lean) | the renewal time $h_m$, the margin length $`\tau'_m`$, the pulse time $\tau_m$ and the factor $4\lceil\varepsilon_{m-1}^{-\delta}\rceil+1$ of (2.4) |
| [`ocShear`](AVRegularity/Statements/Construction/OcShear.lean), [`ocLabel`](AVRegularity/Statements/Construction/OcLabel.lean), [`slowEnvelope`](AVRegularity/Statements/Construction/SlowEnvelope.lean) | the shear streams $\psi_{m,k}$ (2.6), the labels $l_{m,k}$ (2.8) and the slow cutoffs (2.9) |
| [`ocNextStream`](AVRegularity/Statements/Construction/OcNextStream.lean) | one step $\phi_{m-1}\mapsto\phi_m$ of the recursion (2.12) |
| [`IsOCStreamSeq α q Λ ζ Φ`](AVRegularity/Statements/Construction/IsOCStreamSeq.lean) | $\Phi$ is the sequence $`(\phi_m)_{m\ge0}`$ of stream functions: $\phi_0=0$, and $\phi_m$ is obtained from $\phi_{m-1}$ by the recursion |
| [`ocBandSet α q Λ`](AVRegularity/Statements/Construction/OcBandSet.lean) | the permitted diffusivities $\mathcal K$ of (2.18) |
| [`ocA`](AVRegularity/Statements/Construction/OcA.lean), [`ocCStar`](AVRegularity/Statements/Construction/OcCStar.lean) | $a_m=\varepsilon_m^{\beta-2}$, and an explicit absolute constant $c_\ast$ (in the Lean form of Theorem C) |

The hypotheses can be met: [`exists_isFastProfile`](AVRegularity/Statements/Construction/ExistsFastProfile.lean)
gives a cutoff function with (2.2), and
[`exists_isOCStreamSeq`](AVRegularity/Statements/Construction/ExistsOCStreamSeq.lean) shows that the
recursion can be carried out for every integer $\Lambda\ge128$.

**From the formalization of [AV25]** (namespaces `AVenhance` and `Homogenization`, at the pinned
commit).

| Lean | Meaning |
|---|---|
| [`Vec d`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/Homogenization/Ambient/Basic.lean), [`vecDot`, `vecNormSq`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/Homogenization/Ambient/Basic.lean), [`basisVec`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/Homogenization/Sobolev/WeakDerivatives.lean) | `Fin d → ℝ`; the dot product and the squared Euclidean norm; the coordinate vectors |
| [`MemL2On U f`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/Homogenization/Sobolev/H1/Definitions.lean), [`HasWeakGradientOn U u Du`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/Homogenization/Sobolev/WeakDerivatives.lean) | $f\in L^2(U)$; `Du` is the weak gradient of $u$ on $U$ |
| [`unitCube`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/UnitCube.lean), [`IsZ2Periodic f`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/IsZ2Periodic.lean), [`latticeShift n`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/LatticeShift.lean) | the open unit square $(0,1)^2$, a fundamental cell of $\mathbb T^2$; $\mathbb Z^2$-periodicity; the lattice vector $n\in\mathbb Z^2$ |
| [`l2NormSq f`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/L2NormSq.lean), [`IsPeriodicH1With u Du`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/IsPeriodicH1With.lean), [`spaceGrad f`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Roots/SpaceGrad.lean) | $\int_{(0,1)^2}f^2$; $u\in H^1(\mathbb T^2)$ with weak gradient `Du`; the classical gradient |
| [`streamVel φ`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Construction/StreamVel.lean), [`IsAdmissibleStream φ`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Construction/IsAdmissibleStream.lean) | the velocity field $\nabla^\perp\phi=(-\partial_2\phi,\partial_1\phi)$; $\phi$ is smooth and $\mathbb Z\times\mathbb Z^2$-periodic |
| [`IsFlow b X`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Flow/IsFlow.lean), [`flow`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/FlowDefs/Flow.lean), [`flowInv`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/FlowDefs/FlowInv.lean) | $X(t,x,s)$ solves $\partial_tX=\mathbf b(t,X)$ with $X(s,x,s)=x$; the flow, chosen as the unique such $X$ (`existsUnique_flow`); its inverse, used in the recursion |
| [`psi0`](https://github.com/scottnarmstrong/AVAnomalousDiffusion/blob/d4dbc7b11fbf350667013d5ac98a3686f44093f5/AVenhance/Statements/Ingredients/Psi0.lean) | the profiles $\sin(2\pi y_1)$, $\sin(2\pi y_2)$ and $0$ of the shear streams |

## The formalization of [AV25]

This library builds on the Lean formalization of [[AV25]](#references),
[AVAnomalousDiffusion](https://github.com/scottnarmstrong/AVAnomalousDiffusion), at the commit
pinned in [lake-manifest.json](lake-manifest.json) (`d4dbc7b1`). That formalization supplies the
ambient space and the Sobolev notions used here (`Vec`, `MemL2On`, weak gradients and $H^1$,
taken there from the [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining)
formalization of Armstrong and Kuusi), the conventions for functions on the torus, stream
functions and their flows, the existence and uniqueness of weak solutions of the
advection–diffusion equation, and parts of the analysis of [[AV25]](#references) on which the paper
relies: flows of the stream functions and their derivatives, the Faà di Bruno formula, the cell
problems and correctors of the shear pulses, and energy and Galerkin methods on the torus. Since
[[AV25]](#references) fixes the parameter $q$ in terms of $\alpha$, the velocity field of the paper
is constructed in this library.

## Repository layout

| Path | Contents |
|---|---|
| [AVRegularity/Statements/Main](AVRegularity/Statements/Main) | The main results, one theorem per file |
| [AVRegularity/Statements/Definitions](AVRegularity/Statements/Definitions), [AVRegularity/Statements/Construction](AVRegularity/Statements/Construction) | The definitions that the main results use, and the existence of the construction |
| [AVRegularity/Statements/Intermediate](AVRegularity/Statements/Intermediate) | Statements of intermediate results of the paper and the notions they use |
| [AVRegularity/Proofs](AVRegularity/Proofs) | The proofs of the public statements |
| [AVRegularity](AVRegularity) (other directories) | The supporting library, organized by topic: the construction and its velocity fields, well-posedness, the energy of coupled systems, the cell problem, the cycle (preparation and comparison), the passage and the cascade, the entry, and the applications to the main results |
| [AVRegularityChallenge.lean](AVRegularityChallenge.lean), [AVRegularitySolution.lean](AVRegularitySolution.lean), [comparator.json](comparator.json) | The independent statement check (below) |
| [doc/paper.pdf](doc/paper.pdf), [doc/correspondence.md](doc/correspondence.md) | The paper and the correspondence table |
| [scripts](scripts) | The source, metadata, axiom and comparator checks |

The library has about 1,660 Lean files and 1.1 million lines, all in Lean's module system and none
longer than 1,500 lines.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then, from the repository root:

```sh
lake exe cache get   # download the Mathlib build cache
lake build           # build the library, the Challenge and the Solution
```

The build prints eleven `declaration uses sorry` warnings, one for each theorem of
[AVRegularityChallenge.lean](AVRegularityChallenge.lean), whose proofs are left as `sorry` by design
(see [Independent statement check](#independent-statement-check)), and no other warning.

The toolchain is `leanprover/lean4:v4.35.0-rc2` (from [lean-toolchain](lean-toolchain)) with
Mathlib `v4.35.0-rc2`. The Mathlib cache covers Mathlib only: the first build compiles this library
and the formalization of [AV25] from source. This takes about 9.6 CPU-hours in all (about 8.7 for
this library and 0.9 for the formalization of [AV25]), about 1.5 hours of wall time with six
parallel compiles, and about 4 to 6 hours on a 4-core GitHub runner; the first CI build after
release may therefore need one re-run, which resumes from its saved cache. A single compile uses up
to 5 GB of memory. Keep the committed `lake-manifest.json`, and do not run `lake update`.

To print the axioms of every theorem listed above, and to check that each depends only on
`propext`, `Classical.choice` and `Quot.sound`:

```sh
lake env lean scripts/Axioms.lean    # print the axioms
python3 scripts/check-axioms.py      # print and check them
```

To check the source requirements (every file a module; no `sorry`, `admit`, `axiom` or heartbeat
override outside the comparator challenge; file sizes) and the metadata (`CITATION.cff`,
`formalization.yaml`, the license, the workflows, and the Lean blocks of this README):

```sh
python3 scripts/check-lean-sources.py
python3 scripts/check-metadata.py
```

### Independent statement check

[AVRegularityChallenge.lean](AVRegularityChallenge.lean) restates the main results using only Mathlib, with
every notion they use defined in the file, and leaves the proof of each of its eleven theorems (namespace
`AVRegularityChallenge`) as an intentional `sorry`. Its first part, about 270 lines, is a self-contained statement
of Theorems A and B in their existential forms (`interior_regularity`, `uniform_anomalous_dissipation`,
`interior_regularity_and_dissipation`). The second part defines the construction of Section 2 and states, for it,
Theorems A and B (`interior_regularity_construction`, `uniform_anomalous_dissipation_construction`), Theorem C
(`local_interior_regularity`) and Corollary D (`vanishing_diffusivity_limits`,
`vanishing_diffusivity_limits_local`). Three further theorems certify that the objects of the construction
exist: a cutoff function as in (2.2) (`exists_isFastProfile`), the stream functions of the recursion for every
integer $\Lambda\ge128$ (`exists_isOCStreamSeq`), and the flow of the velocity field of an admissible stream
function, which is unique (`existsUnique_streamFlow`); the flow that the recursion uses is defined from the last.
The weak solutions on a time window are asserted to exist by Theorems A and B themselves. The weak solutions on
$(a,\infty)$ that Corollary D(a) takes as hypotheses exist by the standard theory of weak solutions, which the
library proves on every window (`exists_unique_isWeakSolutionOn`); the Challenge does not restate it. The file has
about 700 lines.

[AVRegularitySolution.lean](AVRegularitySolution.lean) contains the same text and proves each theorem from the
statement of the same name in [AVRegularity/Statements](AVRegularity/Statements), and `existsUnique_streamFlow`
from the existence and uniqueness of flows in the formalization of [[AV25]](#references); the definitions of the
Challenge agree with those of the library by unfolding. Lean's
[comparator](https://github.com/leanprover/comparator), configured by [comparator.json](comparator.json), checks
that the two files state the same theorems, that the Solution uses only the standard axioms, and replays the
Solution through Lean's kernel and the independent kernel checkers bundled with the toolchain. (The files are not
named `Challenge` and `Solution` because the dependency's own comparator files already have these names.)

To run the comparator as the Palomar registry does (requires `bubblewrap`):

```sh
scripts/verify-comparator.sh
```

After the build, this takes about two hours, about 5 GB of disk for the exported environments, and up
to about 24 GB of memory. On Ubuntu 24.04, `bubblewrap` also needs
`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`.

## The paper and the correspondence table

The paper ships as [doc/paper.pdf](doc/paper.pdf) (164 pages). Part I is a detailed outline of the
proof of Theorem A, which can be read on its own; Part II states the notions of Part I in full and
proves every statement. The [correspondence table](doc/correspondence.md) lists, for every numbered
statement and display of the paper, the Lean declarations that prove it, with their files, or why
none is needed, and how the two correspond (the same statement, a consequence of a stronger Lean statement, or an
elementary composition of Lean statements). In some places the paper states a result in a weaker
form than its formal version, the form that is natural for a reader: for example, where the paper
bounds a norm in $L^\infty$ in time, the formal statement gives the bound at every time.

## Authors and use of AI

Scott Armstrong and Vlad Vicol. The introduction of the paper states:

> The main ideas of this work were developed by the authors several years ago; the program was
> announced in [AV25, Section 1.3] and described in [AV26, Section 4.1]. Starting from a detailed
> outline of the proof written by the authors, a very long and unpolished manuscript (612 pages of
> slop), in which every detail of the proof was filled in, was first produced by the authors
> together with AI agents (Claude Opus 5.5 and GPT-6.1 Sol). This manuscript was then formalized in
> Lean by AI agents directed by the authors: Claude Opus 5.5 orchestrated the development
> throughout, and the Lean code was written by Claude Opus 5.5 and Claude Sonnet 5.5, with parts
> written by GPT-6.1 Sol and GPT-6 Luna. Only then was the present paper written. Its first draft
> was written by Claude Opus 5.5 following the formalization, and Claude Sonnet 5.5 and GPT-6-Astra
> checked its statements against the formal ones and reviewed it. The authors checked this draft
> and rewrote parts of it themselves; the rest was rewritten by Claude Opus 5.5 agents under the
> direction of the authors, over several rounds of revision and audit.

## How to cite

Please cite the paper, and, if you use the formalization, this repository
([CITATION.cff](CITATION.cff)):

```bibtex
@unpublished{ArmstrongVicol2026,
  author = {Armstrong, Scott and Vicol, Vlad},
  title  = {Anomalous regularization of passive scalars up to the {Obukhov--Corrsin} exponent},
  year   = {2026},
  note   = {Preprint}
}

@software{AVAnomalousRegularization,
  author  = {Armstrong, Scott and Vicol, Vlad},
  title   = {{AVAnomalousRegularization}: a {Lean} 4 formalization of anomalous regularization
             of passive scalars up to the {Obukhov--Corrsin} exponent},
  year    = {2026},
  version = {1.0},
  url     = {https://github.com/scottnarmstrong/AVAnomalousRegularization}
}
```

## Acknowledgements

S. Armstrong was supported by NSF grant DMS-2350340 and by the European Research Council (ERC)
under the European Union's Horizon Europe research and innovation programme, grant agreement
number 101200828. V. Vicol was supported by the Collaborative NSF grant DMS-2307681 and by a Simons
Investigator Award. Built on Lean 4 and Mathlib, and on the formalization of
[[AV25]](#references), whose Sobolev notions are taken from the CoarseGraining formalization of
Scott Armstrong and Tuomo Kuusi.

## License

The Lean code, the scripts and the documentation are licensed under Apache 2.0; see [LICENSE](LICENSE).
The paper [doc/paper.pdf](doc/paper.pdf) is © the authors and is included for reference; it is not
covered by the Apache 2.0 license.

## References

- [AV25] S. Armstrong and V. Vicol, *Anomalous diffusion by fractal homogenization*, Ann. PDE **11**
  (2025), Paper No. 2, [doi:10.1007/s40818-024-00189-6](https://doi.org/10.1007/s40818-024-00189-6),
  [arXiv:2305.05048](https://arxiv.org/abs/2305.05048). Lean formalization:
  [AVAnomalousDiffusion](https://github.com/scottnarmstrong/AVAnomalousDiffusion).
- [AV26] S. Armstrong and V. Vicol, *Anomalous diffusion via iterative quantitative
  homogenization: An overview of the main ideas*, in European Congress of Mathematics, EMS Press,
  2026, pp. 125–167, [doi:10.4171/9ECM/5](https://doi.org/10.4171/9ECM/5),
  [arXiv:2503.11744](https://arxiv.org/abs/2503.11744).
