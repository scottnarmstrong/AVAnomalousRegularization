-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.CellMean

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The forward (transposed) stage transforms, statements

`StageSourceHsStatement` needs the stage transforms in their FORWARD form. The transform bounds (`SameLevelTransformBoundStatement`,
`LetterTransformBoundAEStatement`) say that the
operators `ψ ↦ T_{i,i'}ψ` of the TESTS are bounded `H^N → H^n` with `N ≥ n + loss`. Here the
pairing is with the stage values `X_{i'} ∈ H^N` and the output is an `H^n` element `Y_i` that
represents the functional `φ ↦ ∑_{i'} (c_i/c_{i'}) ∫ X_{i'} T_{i,i'} φ`: the transposed operator
`T^T`, obtained by integration by parts on the torus (the derivatives of `T` move onto `X`; the
real smooth coefficients stay).

* `FwdBody`: the common shape of the two bounds, for a transform family `T`.
* `FwdSameStatement`: the same level, loss `1`.
* `FwdLetterStatement`: the letter `l`, loss `d_l`, at almost every time.
* `H1DensityStatement`: every `H^1` function is an `H^1` limit of smooth periodic ones. -/

universe u v

section Body

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- **The forward bound of a transform family `T`** between the stage orders `k'` and `k`: for
every family `X` of `H^N` stage values there is a family `Y` in `H^n` representing the tested
transforms, `∫ Y_i φ = ∑_{i' ∈ stage k'} (c_i/c_{i'}) ∫ X_{i'} T_{i,i'} φ` for every smooth periodic
test `φ`, with `∑_i ‖Y_i‖² ≤ C² ∑_{i'} ‖X_{i'}‖²`. -/
def FwdBody (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (k k' n N : ℕ)
    (C : ℝ) (T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → (Vec 2 → ℂ) → Vec 2 → ℂ)
    (dmax : ℕ) : Prop :=
  ∀ X : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∃ Y : B1WIndex ι h Nw m Ks → TorusHk n ℂ,
    (∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ (dmax + 1) φ →
      AVenhance.IsZ2Periodic φ →
      ∫ y in AVenhance.unitCube, (torusHkValueCLM (Y i) : Vec 2 → ℂ) y * φ y =
        ∑ i' ∈ stageSet b1wSt k', b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y * T i i' φ y) ∧
    ∑ i ∈ stageSet b1wSt k, ‖Y i‖ ^ 2 ≤ C ^ 2 * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2

end Body

/-- **The forward same-level bound**, `H^N → H^n` for `N ≥ n + 1` (transpose of
`SameLevelTransformBoundStatement`; the transform is `b1wSameTransform`).

For `|β| = 0` or no lower moment, `T = 0` and `Y = 0`. For `v = 0`, `G = I`, `T φ` is `ϖ²` or `ϖ`
times a constant and first derivatives of `φ`; the transpose is `ϖ` times first derivatives of `X`
(a gain of one order is spent), `‖Y‖_{H^n} ≤ C ‖X‖_{H^{n+1}}`. The drift enters as `ϖ v X`, with
`ϖ |D^l v| ≤ C_{vj}(l)` (`S ≥ 1`), the same coefficient bounds as for the tests. The basis vectors
are paired through `b1wSameVec` (an orthogonal projection, norm `≤ 1`). -/
def FwdSameStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ),
  ∃ C : ℝ, 0 ≤ C ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ k, |θ k| ≤ ρ) →
  ∀ r ∈ Icc F.a F.b, ∀ (k k' : ℕ),
    (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        i'.1 = i.1) →
  ∀ N : ℕ, n + 1 ≤ N →
    FwdBody (m := m) (Ks := Ks) F k k' n N C
      (fun i i' φ => b1wSameTransform θ (F.G r) (F.v r) i i' φ) (Finset.univ.sup d)

open Classical in
/-- **The forward same-level operators** (transpose of `SameLevelOpsStatement`, pair by pair).
For every pair of stages `(i, i')` there is a bounded real-linear map `A : H^N → H^n` (`N ≥ n + 1`)
with `‖A‖ ≤ C₀` when `i, i'` are related by one of the five moment shifts (`SameRel`) and `A = 0`
otherwise, representing `X ↦ φ ↦ (c_i/c_{i'}) ∫ X T^{same}_{i,i'} φ` against `C¹` periodic tests.

Proof: `A` is `sameOp n N hnN θ M (-a4) (-a5) e123 e4 e5` with the coefficients of `sameLevelOps`
(`sameOp_norm_le` applies verbatim since `|-a| ≤ 4`): the transpose of `φ ↦ D_{-θ,k} φ` is
`-(∂_k + iθ_k)`, the multiplications by `v` and by the real constants are self-transposed. The
pairing identity is `same_star_eff` (with `f = star φ`) plus the integration by parts
`∫ X D_{-θ,k} φ = -∫ (tbTwist n θ k X) φ` for `X ∈ H^N`, `φ` smooth periodic (no classical
representative of `X` is available when `N` is small: approximate `X` in `H^N` by the Fourier
lifts `smoothFourierLift` and pass to the limit, both sides being continuous in `X`). -/
def FwdSameOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ k, |θ k| ≤ ρ) →
  ∀ r ∈ Icc F.a F.b, ∀ N : ℕ, n + 1 ≤ N →
  ∀ i i' : B1WIndex ι h Nw m Ks,
    ∃ A : TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
      ‖A‖ ≤ (if SameRel i i' then C0 else 0) ∧
      ∀ (X : TorusHk N ℂ) (φ : Vec 2 → ℂ), ContDiff ℝ 1 φ → AVenhance.IsZ2Periodic φ →
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (A X) : Vec 2 → ℂ) y * φ y =
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
              b1wSameTransform θ (F.G r) (F.v r) i i' φ y

/-- **The forward letter bound**, `H^N → H^n` for `N ≥ n + d_l`, from level `l` to level `l + 1`,
at almost every time (transpose of `LetterTransformBoundAEStatement`; the transform is
`b1wLetterTransform`).

For a letter with no edges, `T = 0` and `Y = 0`. For one constituent of order `d` with coefficient
`c(z)`, `T φ = D^{α}(c D_k φ)` up to the Taylor factors and the transpose is `D_k(c D^α X)` with
`|α| ≤ d - 1`: at most `d` derivatives fall on `X`, and `c` is differentiated at most `n` times
(`n + d_max ≤ J`). The stage scale ratio supplies the powers of `ϖ` as in the test form. -/
def FwdLetterStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C : ℝ, 0 ≤ C ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    (∀ k, |θ k| ≤ ρ) →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (k k' : ℕ),
    (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      i.1 = l.succ) →
    (∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
      i'.1 = l.castSucc) →
  ∀ N : ℕ, n + d l ≤ N →
    FwdBody (m := m) (Ks := Ks) F k k' n N C
      (fun i i' φ => b1wLetterTransform F θ i i' r φ) (Finset.univ.sup d)

open Classical in
/-- **The forward letter operators** (transpose of `LetterOpsStatement`). For a letter `l` there are
bounded real-linear maps `A_{i,i'} : H^N → H^n` (`N ≥ n + d_l`; `i` at level `l + 1`, `i'` at level
`l`) representing `X ↦ φ ↦ (c_i/c_{i'}) ∫ X T^{letter}_{i,i'} φ`, with the block bounds of the test
form, summed over the INPUT stages `i'` of one component and moment and measured on the output
stages `i` of another: the weights `LetterMomRel` and `letterCompWeight` are the same, and their row
and column sums are bounded in both directions (`letterMom_row/col`, `letterCompWeight_row/col`).

Proof: as for `LetterOpsStatement` (`letterOps`): the coefficient, ratio and Parseval
estimates are index-level and direction-free; the term operators are `D^b (c ·)` for the tests
(`unitOp`, `powOp`) and become `c · (D^b)^T` (derivatives first, `powOp` after `tbMulCLM`, with
`θ` unchanged: the transpose of `fibreCovDeriv (-θ)` is `-(∂ + iθ) = -tbTwist θ`), losing at most
`d_l` derivatives of `X` and differentiating `c` at most `n` times (`n + d_max ≤ J`). The pairing
identity is the integration by parts `∫ X D φ = -∫ (D' X) φ` of `FwdSameOpsStatement`. -/
def FwdLetterOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    (∀ k, |θ k| ≤ ρ) →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
  ∃ A : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc →
      ∀ (X : TorusHk N ℂ) (φ : Vec 2 → ℂ), ContDiff ℝ ((Finset.univ.sup d : ℕ) + 1) φ →
        AVenhance.IsZ2Periodic φ →
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (A i i' X) : Vec 2 → ℂ) y * φ y =
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
              b1wLetterTransform F θ i i' r φ y) ∧
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i ∈ S, ‖∑ i' ∈ S', A i i' (f i')‖ ^ 2 ≤
          (C0 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x') ^ 2 *
            ∑ i' ∈ S', ‖f i'‖ ^ 2

/-- **Density of smooth periodic functions in `H^1` of the torus.** -/
def H1DensityStatement : Prop :=
  ∀ z : TorusHk 1 ℂ, ∃ zs : ℕ → TorusHk 1 ℂ, Filter.Tendsto zs Filter.atTop (nhds z) ∧
    ∀ N : ℕ, ∃ φ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ AVenhance.IsZ2Periodic φ ∧
      (torusHkValueCLM (zs N) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] φ

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # Forced-curve and negative-smoothing bounds for `ℓ²` families of fibre curves (statements)

`FullFieldFibreStatement` fixes its constants before the component type `ι`. The terminal pass
handles the stages of one order as a family whose size `card (B1WIndex ι h …)` depends on `ι` and
on the fibre dimensions; `StageSourceHsStatement` bounds the forcing of the family in `ℓ²`.
Per-curve `CellForcedHsStatement` needs an integrable majorant `f_i ≥ ‖σ_i(t)‖` per curve, and
the representatives `σ_i(t)` chosen at each time are not measurable in `t`; constant per-curve
majorants cost `card`. The family forms below take ONE scalar majorant of the `ℓ²` norm of the
family, and give `ℓ²` bounds with constants independent of the family.

Both are re-runs of the duality proofs of the per-curve statements (`CellForcedHsStatement`,
`CellNegativeSmoothingStatement` and the dual criterion) with families: test against a family `g_i`
at the final time, run the adjoint curves `Ψ_i` from each `g_i`, pair, and use Cauchy–Schwarz over
the family inside the time integral
(`∑_i ⟨σ_i(r), Ψ_i(r)⟩ ≤ (∑‖σ_i(r)‖²)^{1/2} (∑‖Ψ_i(r)‖²)^{1/2}`); then a family dual criterion (`ℓ²`
of the per-curve dual norms) produces the `H^{j_i}` elements.

For one curve these are the forced-curve and negative-smoothing bounds, and for `σ = 0` and zero
data everything is `0`. The orders `j_i ≤ j_max` vary, and the constant depends on `j_max`. The
constants `C, Q` are chosen after `j_max` (and `s`) and `ρ`, and before the window, the
coefficients, the family and its size. -/

universe w

/-- Forced fibre curves on a unit window, with an `ℓ²` majorant of their
`H^{j_i}` forcings, stay in `H^{j_i}` with an `ℓ²` bound. -/
def CellForcedHsFamilyStatement : Prop :=
  ∀ (jmax : ℕ) (ρ : ℝ), 0 ≤ ρ → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → b ≤ a + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ jmax + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ {I : Type w} [Fintype I] (j : I → ℕ), (∀ i, j i ≤ jmax) →
  ∀ (u : I → ℝ → ComplexCellL2) (slice : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2),
    (∀ i, CellWeakHilbertCurve a b (u i) (slice i) (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice i t) (S i t) (F i t))) →
  ∀ (σ : ∀ i, ℝ → TorusHk (j i) ℂ) (f : ℝ → ℝ), IntegrableOn f (Set.Icc a b) →
    (∀ᵐ t ∂volume.restrict (Set.Icc a b), Real.sqrt (∑ i, ‖σ i t‖ ^ 2) ≤ f t ∧
      ∀ i (z : TorusHk 1 ℂ), cellComplexSource (fun k => (θ k : ℂ)) (S i t) (F i t) z =
        cellComplexPair (torusHkValueCLM (σ i t)) (torusHkValueCLM z)) →
  ∀ w₀ : ∀ i, TorusHk (j i) ℂ, (∀ i, torusHkValueCLM (w₀ i) = u i a) → ∀ t ∈ Set.Icc a b,
    ∃ w : ∀ i, TorusHk (j i) ℂ, (∀ i, torusHkValueCLM (w i) = u i t) ∧
      Real.sqrt (∑ i, ‖w i‖ ^ 2) ≤
        C * (1 + L) ^ Q * (Real.sqrt (∑ i, ‖w₀ i‖ ^ 2) + ∫ r in a..t, f r)

/-- Homogeneous fibre curves on a unit window whose initial values are
bounded in `ℓ²` against families of `H^s` tests by `M` are in `H^{j_i}` after a time `τ`, with an
`ℓ²` bound `C(1+L)^Q τ^{-(j_max+s)/2} M`. -/
def CellNegativeSmoothingFamilyStatement : Prop :=
  ∀ (jmax s : ℕ) (ρ : ℝ), 0 ≤ ρ → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → b ≤ a + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ jmax + s + 1 → t ∈ Set.Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ {I : Type w} [Fintype I] (j : I → ℕ), (∀ i, j i ≤ jmax) →
  ∀ (u : I → ℝ → ComplexCellL2) (slice : I → ℝ → TorusHk 1 ℂ),
    (∀ i, CellWeakHilbertCurve a b (u i) (slice i) (fun t =>
      cellDualDerivative ⟨fun s' _ => G s', v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice i t) 0 0)) →
  ∀ M : ℝ, 0 ≤ M →
    (∀ ψ : I → TorusHk s ℂ, ‖∑ i, cellComplexPair (u i a) (torusHkValueCLM (ψ i))‖ ≤
      M * Real.sqrt (∑ i, ‖ψ i‖ ^ 2)) →
  ∀ τ : ℝ, 0 < τ → ∀ t ∈ Set.Icc a b, a + τ ≤ t →
    ∃ w : ∀ i, TorusHk (j i) ℂ, (∀ i, torusHkValueCLM (w i) = u i t) ∧
      Real.sqrt (∑ i, ‖w i‖ ^ 2) ≤ C * (1 + L) ^ Q * τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the output norm of a positive-order fibre (statement)

`TorusHkBandBoundStatement`: an `H^N` element of the cell has the shifted Fourier weights of order
`k ≤ N` bounded by its norm, at every frequency of the zone:
`∑_n (1 + |2πn + θ|²)^k |f̂(n)|² ≤ C ‖w‖²_{H^N}` (`cellBandSq k 0 θ`).

Proof: real and imaginary parts (`mapTorusHk Complex.reCLM`, `imCLM`); per jet component
Parseval (`torusJetComponentParseval`) with the jet coefficients `realJetFourier_word_norm`,
`realJetFourier_eq_cellCoeff` and `frequencyPower_eq_word_sum` (the sum over the ordered words of
length `a` of `∏|2πn_{w_i}|²` is `|2πn|^{2a}`); then `(1 + |2πn + θ|²)^k ≤ C_k(1 + |2πn|²)^k` for
`|θ_i| ≤ π`, and `(1 + |y|²)^k ≤ C_k ∑_{a ≤ k} |y|^{2a}`.

For `k = 0` this is Parseval, `∑|f̂(n)|² = ‖f‖²_{L²(cell)} ≤ ‖w‖²`. For `w` a single mode
`e^{2πin·z}`, `(1+|2πn+θ|²)^k ≤ C (1+|2πn|²)^k ≍ ‖w‖²_{H^k}`. The constant `C` is chosen after
`k, N` and before `w` and `θ`. -/

/-- **The shifted Fourier weights of an `H^N` element.** -/
def TorusHkBandBoundStatement : Prop :=
  ∀ (k N : ℕ), k ≤ N → ∃ C : ℝ, 0 ≤ C ∧
  ∀ (w : TorusHk N ℂ) (θ : Vec 2), θ ∈ freqCube →
    cellBandSq k 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (C * ‖w‖ ^ 2)

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The plain kernel

At a real frequency the constant `1` is an `L²` decay kernel of the homogeneous fibre equation:
`cellDriftWeakContraction`. -/

/-- The plain kernel. -/
theorem plainKernel : PlainKernelStatement := by
  intro a b G hG v hv V hb θ
  refine ⟨fun _ _ => by norm_num, fun _ _ => le_rfl, fun _ => rfl,
    fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp,
    fun _ _ _ _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro r s hr hrs hsb u slice hu
  have h := cellDriftWeakContraction G hG hv V hb θ hrs u slice hu r ⟨le_rfl, hrs⟩ s
    ⟨hrs, le_rfl⟩ hrs
  simpa using h

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the interface of the three component assemblies

`QuietHighFibreAssembly` is proved from three named assemblies:
* `QuietEntranceAssembly` (entrance bound): the plain pass at the entrance of the quiet stretch, as a weighted
  `ℓ²` bound of the cell Fourier modes of the stages;
* `QuietModeAssembly` (mode equation): on the quiet stretch each mode of each stage solves a scalar
  triangular Duhamel system, with coupling polynomial in the wavevector;
* `QuietAbsorbAssembly` (absorption): the absorption of the polynomial factors by the heat decay, the sum
  over the modes, the composition.

Here: the statements and `quietHighFibreAssembly_of_parts`. -/

universe u v

/-- The squared plane frequency `|2πn + θ|²` of the cell mode `n`. -/
def quietYSq (θ : Vec 2) (n : Fin 2 → ℤ) : ℝ := ∑ j, quietFourierFrequency θ n j ^ 2

/-- The cell Fourier coefficient of the scaled stage `i` at time `t`. -/
def stageMode {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {K : ScalarConstants} {g₁ : ℝ} {D Nw m : ℕ} {Ks : Fin Nw → ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i : B1WIndex ι h Nw m Ks) (n : Fin 2 → ℤ) (t : ℝ) : ℂ :=
  cellFourierCoeff (stageScaled F θ i t) n

/-- The damping exponent of the cell mode `n` on the quiet stretch (zero drift). -/
def quietLam (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Vec 2) (n : Fin 2 → ℤ) (t : ℝ) : ℂ :=
  -(∑ j, ∑ k, (G t j k : ℂ) * (quietFourierFrequency θ n j : ℂ) *
    (quietFourierFrequency θ n k : ℂ))

/-- The plain pass with the constant kernel `1` at the entrance `t₁ = b - D_q` of the
quiet stretch: the weighted `ℓ²` norm of the cell modes of all stages, with weight
`(1 + |2πn+θ|²)^{-S}` (`S` a shape constant, the top of the ladder), is at most
`C P_e^Q (1 + (t₁ - a))^Q` times the `L²` norms of the stage values at the start. -/
def QuietEntranceStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q S : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ F.J →
    θ ∈ freqCube →
  ∀ t₁ : ℝ, F.a ≤ t₁ → t₁ ≤ F.b →
    ∑ i : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i n t₁‖ ^ 2) ≤
    ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q) ^ 2) * stageDatumSq F m Ks θ

/-- On a quiet stretch `[t₁, b]` (zero drift, quiet times) every cell mode `n` of the
stages solves the Duhamel equation of its heat exponential with a forcing
`∑_{i'} τ_{i,i'}(r) c_{i'}(r)`. The coupling matrix `τ(r)` has `ℓ²` operator norm at most
`B (1 + |2πn+θ|²)^p` (uniform in the number of components) and is triangular:
`τ_{i,i'} = 0` unless `st i' < st i`. The integrands are interval integrable. -/
def QuietModeStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (B : ℝ) (p : ℕ), 0 ≤ B ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ F.J →
    θ ∈ freqCube →
  ∀ t₁ : ℝ, F.a ≤ t₁ → t₁ ≤ F.b → Icc t₁ F.b ⊆ F.reg.quiet →
    (∀ t ∈ Icc t₁ F.b, ∀ z, F.v t z = 0) →
  ∀ n : Fin 2 → ℤ, ∃ τ : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → ℝ → ℂ,
    (∀ r (w : B1WIndex ι h Nw m Ks → ℂ),
      ∑ i, ‖∑ i', τ i i' r * w i'‖ ^ 2 ≤ (B * (1 + quietYSq θ n) ^ p) ^ 2 * ∑ i', ‖w i'‖ ^ 2) ∧
    (∀ i i' r, ¬ b1wSt i' < b1wSt i → τ i i' r = 0) ∧
    (∀ t ∈ Icc t₁ F.b, ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
        ∑ i', τ i i' r * stageMode F θ i' n r) volume t₁ t) ∧
    ∀ t ∈ Icc t₁ F.b, ∀ i,
      stageMode F θ i n t =
        Complex.exp (∫ r in t₁..t, quietLam F.G θ n r) * stageMode F θ i n t₁ +
        ∫ r in t₁..t, Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', τ i i' r * stageMode F θ i' n r

/-- The entrance bound as an assembly. -/
def QuietEntranceAssembly : Prop :=
  PlainStageStatement.{u, v} → PlainKernelStatement → QuietEntranceStatement.{u, v}

/-- The mode equation as an assembly. -/
def QuietModeAssembly : Prop :=
  StageFamilyZoneStatement.{u, v} → QuietModeStatement.{u, v}

/-- The absorption of the polynomial factors by the heat decay, the sum over the modes
with `|y| ≥ π/4`, and the composition of the mode equation and the entrance bound. -/
def QuietAbsorbAssembly : Prop :=
  QuietEntranceStatement.{u, v} → QuietModeStatement.{u, v} → QuietHighFibreStatement.{u, v}

/-- The quiet stretch at the fibre level, from the entrance, mode and absorption parts. -/
theorem quietHighFibreAssembly_of_parts (hC : QuietEntranceAssembly.{u, v})
    (hB : QuietModeAssembly.{u, v}) (hD : QuietAbsorbAssembly.{u, v}) :
    QuietHighFibreAssembly.{u, v} :=
  fun hPS hPK hSF => hD (hC hPS hPK) (hB hSF)

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Discard

/-! # The transform families at every frequency of the zone

`StageFamilyZoneStatement` is `b1w_family_provider_zone` with the zone bounds
(`sameLevelTransformBoundZone`, `letterTransformBoundAEZone`); the frequency
hypothesis `|θ_k| ≤ ρ` in place of `|ξ| ≤ ρ`. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The transform families at every frequency of the zone. -/
theorem stageFamilyZone : StageFamilyZoneStatement.{u, v} :=
  fun K Nw D m d Ks pos ρ s₀ hs₀ =>
    b1w_family_provider_zone sameLevelTransformBoundZone.{u, v} letterTransformBoundAEZone.{u, v}
      K Nw D m d Ks pos ρ s₀ hs₀

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the bridge from the plane to the fibres (`BridgeStatement`)

`cellFourierCoeff (planeBlochC θ g) n = ĝ(2πn + θ)` for integrable `g` (periodization with the
lattice character), the tiling of the plane by the boxes `2πn + [-π, π)²`, and the resulting
identity of the zone integral of the band norms with the plane integral of the band integrand. -/

theorem charPhase_periodic (n : Fin 2 → ℤ) :
    AVenhance.IsZ2Periodic (fun y : Vec 2 =>
      Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℂ) * (y 0 : ℂ) + (n 1 : ℂ) * (y 1 : ℂ))))) := by
  intro l x
  simp only [AVenhance.latticeShift, Pi.add_apply]
  push_cast
  have : -(2 * (Real.pi : ℂ) * Complex.I * ((n 0 : ℂ) * ((x 0 : ℂ) + (l 0 : ℂ)) +
      (n 1 : ℂ) * ((x 1 : ℂ) + (l 1 : ℂ)))) =
    -(2 * (Real.pi : ℂ) * Complex.I * ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) +
      ((-(n 0 * l 0 + n 1 * l 1) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cellCoeff_eq (θ : Vec 2) (n : Fin 2 → ℤ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    cellFourierCoeff (planeBlochC θ g) n = planeTransform g (quietFourierFrequency θ n) := by
  have h := integral_phase_mul_eq_cell_planeBlochC θ hg
    (φ := fun y : Vec 2 => Complex.exp (-(2 * Real.pi * Complex.I *
      ((n 0 : ℂ) * (y 0 : ℂ) + (n 1 : ℂ) * (y 1 : ℂ)))))
    (by fun_prop) (B := 1) (fun z => by
      rw [Complex.norm_exp]
      simp) (charPhase_periodic n)
  unfold cellFourierCoeff planeTransform
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [quietFourierFrequency, vecDot, Fin.sum_univ_two]
  rw [mul_assoc, ← mul_assoc _ (g y : ℂ), mul_comm _ (g y : ℂ), mul_assoc, ← Complex.exp_add]
  rw [mul_comm]
  congr 2
  push_cast
  ring

def latticeCellBox (n : Fin 2 → ℤ) : Set (Vec 2) :=
  Set.univ.pi fun i => Set.Ico (2 * Real.pi * (n i : ℝ) - Real.pi) (2 * Real.pi * (n i : ℝ) + Real.pi)

theorem Box_measurable (n : Fin 2 → ℤ) : MeasurableSet (latticeCellBox n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem mem_Ico_iff (x : ℝ) (k : ℤ) :
    x ∈ Set.Ico (2 * Real.pi * (k : ℝ) - Real.pi) (2 * Real.pi * (k : ℝ) + Real.pi) ↔
      ⌊(x + Real.pi) / (2 * Real.pi)⌋ = k := by
  have hp : 0 < 2 * Real.pi := by positivity
  rw [Int.floor_eq_iff, le_div_iff₀ hp, div_lt_iff₀ hp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩

theorem Box_disjoint : Pairwise (Function.onFun Disjoint latticeCellBox) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  intro ξ h1 h2
  apply hnm
  funext i
  have a := (mem_Ico_iff (ξ i) (n i)).1 (h1 i (Set.mem_univ i))
  have b := (mem_Ico_iff (ξ i) (m i)).1 (h2 i (Set.mem_univ i))
  rw [← a, ← b]

theorem Box_cover : (⋃ n, latticeCellBox n) = Set.univ := by
  refine Set.eq_univ_of_forall fun ξ => Set.mem_iUnion.2 ⟨fun i => ⌊(ξ i + Real.pi) / (2 * Real.pi)⌋, ?_⟩
  intro i _
  exact (mem_Ico_iff _ _).2 rfl

theorem Box_zero_ae : latticeCellBox 0 =ᵐ[volume] freqCube := by
  rw [freqCube_eq_pi, volume_pi]
  have := (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (s := Set.univ)
    (f := fun _ => -Real.pi) (g := fun _ => Real.pi))
  convert this using 2
  simp [latticeCellBox]

theorem box_translate (F : Vec 2 → ℝ≥0∞) (n : Fin 2 → ℤ) :
    ∫⁻ ξ in latticeCellBox n, F ξ = ∫⁻ θ in latticeCellBox 0, F (quietFourierFrequency θ n) := by
  have hpre : (fun θ : Vec 2 => θ + fun i => 2 * Real.pi * (n i : ℝ)) ⁻¹' latticeCellBox n = latticeCellBox 0 := by
    ext θ
    simp only [latticeCellBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Pi.add_apply, Pi.zero_apply, Int.cast_zero, mul_zero]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have h := (measurePreserving_add_right (volume : Measure (Vec 2))
    (fun i => 2 * Real.pi * (n i : ℝ))).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight _) F (latticeCellBox n)
  rw [hpre] at h
  rw [← h]
  refine setLIntegral_congr_fun (Box_measurable 0) (fun θ _ => ?_)
  congr 1
  funext i
  simp only [quietFourierFrequency, Pi.add_apply]
  ring

theorem tiling (F : Vec 2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ξ, F ξ = ∫⁻ θ in freqCube, ∑' n : Fin 2 → ℤ, F (quietFourierFrequency θ n) := by
  have h1 : ∫⁻ ξ, F ξ = ∑' n : Fin 2 → ℤ, ∫⁻ ξ in latticeCellBox n, F ξ := by
    rw [← lintegral_iUnion Box_measurable Box_disjoint, Box_cover, Measure.restrict_univ]
  rw [h1, ← setLIntegral_congr Box_zero_ae, lintegral_tsum]
  · exact tsum_congr fun n => box_translate F n
  · intro n
    refine Measurable.aemeasurable (hF.comp ?_)
    unfold quietFourierFrequency
    fun_prop

theorem Ft_continuous {g : Vec 2 → ℝ} (hg : Integrable g) : Continuous (planeTransform g) := by
  unfold planeTransform
  refine continuous_of_dominated (bound := fun y => ‖g y‖) (fun ξ => ?_) (fun ξ => ?_) hg.norm ?_
  · have h1 : Continuous fun y : Vec 2 => vecDot ξ y := by unfold vecDot; fun_prop
    have h2 : Continuous fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot ξ y : ℂ))) := by
      fun_prop
    exact h2.aestronglyMeasurable.mul hg.ofReal.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  · refine Filter.Eventually.of_forall fun y => ?_
    have : Continuous fun ξ : Vec 2 => vecDot ξ y := by unfold vecDot; fun_prop
    fun_prop

theorem Band_measurable (k : ℕ) (ρ : ℝ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Measurable (BandIntegrand k ρ g) := by
  unfold BandIntegrand
  have hc := Ft_continuous hg
  have hv : Continuous fun ξ : Vec 2 => vecDot ξ ξ := by unfold vecDot; fun_prop
  refine Measurable.ite (measurableSet_le measurable_const hv.measurable) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp ((by fun_prop : Continuous fun ξ : Vec 2 =>
    (1 + vecDot ξ ξ) ^ k * ‖planeTransform g ξ‖ ^ 2).measurable)

theorem bridge : BridgeStatement := by
  intro k ρ g hg
  rw [tiling _ (Band_measurable k ρ hg)]
  refine setLIntegral_congr_fun measurableSet_freqCube (fun θ _ => ?_)
  unfold cellBandSq BandIntegrand
  refine tsum_congr fun n => ?_
  rw [cellCoeff_eq θ n hg]

end AVRegularity.CycleWords.Discard
end
end
