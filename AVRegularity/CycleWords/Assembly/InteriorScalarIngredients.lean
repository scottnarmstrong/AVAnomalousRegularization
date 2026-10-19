-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WH3Abstract
public import AVRegularity.CycleWords.MixedWords.B1WLadder
import AVRegularity.CycleWords.InteriorBufferedGraphRowData
public import AVRegularity.CycleWords.ConstructedScalarFibreConstants
public import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing

section
section
/-! # Sharp pass: weighted sharp decay of the adjoint tests (statement)

The sharp H4 of the word fibre facts measures tests by the activity-weighted norm (`b1wNuW`).
This is `‖U_T‖ + Ω(r)‖U_N‖`, minimized over the splittings
with `U_T` transverse to the orientation `e(r)` of the last activity, and
`Ω(r) = max(1, Λ e^{-c(r − τ(r))})`. The statement (`WeightedSharpDecayStatement`) is two-level.
An actual-fast reversed curve, measured at its start `t` with the weight `Λ₁`, decays at `π²/8` to
every earlier time `s`, measured there with a smaller weight `Λ₂`, `Λ₂ P_e^{Q′} ≤ Λ₁`. The
constant is independent of `P_e` and `S`. The regime is the well-buffered one, `Λ₁` included.

Why two levels: inside a shear window the non-transverse part of the curve keeps its `L²` decay
(the drift is skew), but its `H^j` norm grows by a one-time crude factor `C P_e^{Q_c}`. The drop
`Λ₁/Λ₂ ≥ P_e^{Q′}` pays it. In the word fibre facts the drop is the stage drop (`Λ^{k+1}` at stage `k`, and the
intermediate decompositions go to lower stages). The endpoint is weighted by `1`, which is the
case `Λ₂ = 1`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- **Weighted sharp decay of the adjoint tests.**

For `t = s` take `V = U` (`C ≥ 1`, and `Ω_{Λ₂} ≤ Ω_{Λ₁}` since `Λ₂ ≤ Λ₁`). For `t` just after a
window, `t = hi_p + D/2 + ε`, in no zone, one has `t − τ(t) ≥ D/2`, so `Ω_{Λ₁}(t) = 1` in the
regime, and the datum is arbitrary (`U_T = 0`); behind `t` there is a zero-drift stretch of length
`≥ D/2`, which gives the surplus that pays a crude crossing. For two overlapping windows of
different orientations the drift vanishes on the overlap of their enlarged intervals; active times
of different orientations are `> D` apart, so `e(r)` is unique wherever `Ω > 1`. A degenerate window
carries no active time, since its enlarged interval lies in its buffers. For `ξ = 0` one has
`r = 0`, and fast means mean zero. For a single window covering `[s, t]` and active throughout,
`U_T` decays by the sharp fast decay (local transversality), while `U_N` decays at `π²/2` in `L²`
with the crude factor `P_e^{Q_c}` in `H^j`, paid by `Λ₂ P_e^{Q′} ≤ Λ₁`. With no activity at all,
`Ω ≡ 1` and this is the sharp fast decay with arbitrary data on a quiet piece. The constants
`C, C_b, c_b, Q, Q′` depend on `K, j, ρ` only. The rate of the weight is the numeral `3π²/8`,
because an existential rate chosen after `j` cannot be compared across the stages of the weighted
decay argument. -/
def WeightedSharpDecayStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb cb : ℝ) (Q Q' : ℕ), 1 ≤ C ∧ 0 < cb ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
  ∀ Λ₁ Λ₂ : ℝ, 1 ≤ Λ₂ → Λ₂ * peFactor η ^ Q' ≤ Λ₁ →
    Cb * Λ₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-cb * reg.buffer) ≤ 1 →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ}, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
    cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
  ∀ UT UN : TorusHk j ℂ, torusHkValueCLM (UT + UN) = u (-t) →
    cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
      torusHkValueCLM UT →
    ∃ VT VN : TorusHk j ℂ, torusHkValueCLM (VT + VN) = u (-s) ∧
      cellTransverseProjection (activityOrient reg v t₀ s) (torusHkValueCLM VT) =
        torusHkValueCLM VT ∧
      ‖VT‖ + activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s * ‖VN‖ ≤
        C * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
          (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖)

open Classical in
/-- The quiet lag of `[s, t]`: the zero-drift time behind `t` that the curve crosses before `s`,
`min(t − s, t − τ(t))`, or `t − s` without activity. -/
def quietLag (v : ℝ → Vec 2 → Vec 2) (t₀ s t : ℝ) : ℝ :=
  if (activeSet v t₀ t).Nonempty then min (t - s) (t - lastActive v t₀ t) else t - s

/-- **The surplus decay.** An actual-fast reversed curve with an arbitrary
datum decays in `H^j` at `π²/8`. It carries the surplus `e^{-(3π²/8)·lag}` of the zero-drift
stretch behind `t` (rate `π²/2`), at the price of a crude factor `C P_e^Q`. Route (the part `B` of the
decay estimate):
* the quiet lemma (`sharpQuiet_decay`) on `[τ(t) + ε, t]` (the drift may be nonzero at the single
  time `τ(t)`);
* then `revCurve_crude_decay` (actual-fast data) on `[s, τ(t)]`;
* if `s > τ(t)`, the quiet lemma alone.

This is the bound case 1 of 29b needs: the weight `Ω_{Λ₂}(s)` is paid by the surplus, since
`Λ₂ e^{-c g_s} e^{-(3π²/8) lag} ≤ Λ₂ e^{-(3π²/8) g_t}`.

For `s = t` the lag is `0` and `C ≥ 1`. With no activity the decay is a pure quiet decay at
`π²/2 = 3π²/8 + π²/8`. For `s ≤ τ(t)` the lag is `g_t`. The constants `C, Q` depend on `K, j, ρ`
only, and no regime is needed. -/
def SurplusDecayStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ}, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
    cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
  ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
      ‖w‖ ≤ C * peFactor η ^ Q * Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s t) *
        Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖

/-- **Estimate (a) of the weighted sharp decay: the plain decay from a weighted datum**.
The same setting, with the weight `Λ₁ ≥ P_e^{Q′}` at the start only. The `H^j` norm of `u(−s)` is
bounded by `C e^{-π²(t−s)/8}(‖U_T‖ + Ω_{Λ₁}(t)‖U_N‖)` at every earlier time `s`. Route:
* correct by the constant `1`: `A = U_T + P U_N − κ·1` is actual-fast;
* the sharp fast decay for `A`;
* the quiet lemma on `(τ(t), t]`, then the crude decay, for `B = (1 − P)U_N + κ·1`;
* if `Ω_{Λ₁}(t) = 1`, all of `u` is `B`.

For `t = s` one has `‖U_T + U_N‖ ≤ ‖U_T‖ + Ω‖U_N‖` (`Ω ≥ 1`). With no activity before `t`, `Ω = 1`
and this is the quiet lemma. For a single window active throughout, `Ω_{Λ₁}(t) = Λ₁ ≥ P_e^{Q′}`
pays the crude factor of `B`. The constants `C, C_b, c_b, Q, Q′` depend on `K, j, ρ` only. -/
def WeightedPlainDecayStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb cb : ℝ) (Q Q' : ℕ), 1 ≤ C ∧ 0 < cb ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
  ∀ Λ₁ : ℝ, peFactor η ^ Q' ≤ Λ₁ →
    Cb * Λ₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-cb * reg.buffer) ≤ 1 →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ}, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
    cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
  ∀ UT UN : TorusHk j ℂ, torusHkValueCLM (UT + UN) = u (-t) →
    cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
      torusHkValueCLM UT →
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
      ‖w‖ ≤ C * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
        (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The stage expansion of the tested sources (statement)

The letter Bloch identity writes the tested source of a stage `i = (j, x, β, b)` as cell pairings of
Bloch parts of earlier values against transforms of the test. Indexed by the stages
(`B1WIndex`: level, component, moment, basis vector `b` of `h x`), this reads
`b1wTestedSource_i(φ) = ∑_{i'} ∫_cell Stage_{i'}(r) · T_{i,i'}(r)φ` (`StageExpansionStatement`),
where `Stage_{i'}(r) = B_θ(y^{β'} ⟨b', u_{j'} x'(r)⟩)` (`b1wStageVal`) and the transform
`T_{i,i'} = T^{same} + T^{letter}` is explicit:

* `b1wSameTransform`: `i'` at the same level, component and vector, with a lower moment
  `β' = β - s`, `s ∈ {2e₀, e₀+e₁, 2e₁, e₀, e₁}`; the five terms of `b1wSameLevel`;
* `b1wLetterTransform`: `i'` at the previous level `l`, any component `x'` and vector `b'`, with the
  moment `β' = β₀ + #ω - a` of the jet-to-value transfer (`b1wJetPair`) for the three moment-flux
  variants of clause 1 (`β₀ = β - e₀, β - e₁, β`, tests `φ, φ, D_{-θ,k}φ`). The vector
  `γ.map* e` of the letter is expanded in the basis of `h x'` (the coefficient
  `⟨γ.map* e, b'⟩`).

Only earlier stages appear (`StageTransformEarlierStatement`): the same-level moments are lower,
and a letter spends at most `K_s(l)` moments, so `deg i' ≤ deg i` with `i'` at a lower level.

-/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.Assembly

universe u v

section Defs

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The basis vector of a stage. -/
def b1wVec (i : B1WIndex ι h Nw m Ks) : h i.2.1 := stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2

/-- The moment of a stage. -/
def b1wMom (i : B1WIndex ι h Nw m Ks) : ℕ × ℕ := i.2.2.1.1

open Classical in
/-- The vector of `i` seen in the component of `i'` (zero for another component). -/
def b1wSameVec (i i' : B1WIndex ι h Nw m Ks) : h i'.2.1 :=
  if hx : i.2.1 = i'.2.1 then hx ▸ b1wVec i else 0

/-- The unscaled stage value at time `r`: `B_θ(y^β ⟨b, u_j x(r)⟩)`. -/
def b1wStageVal {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i : B1WIndex ι h Nw m Ks) (r : ℝ) : Vec 2 → ℂ :=
  b1wStageFun θ (b1wMom i) (b1wVec i) (planeValue (F.u i.1 i.2.1 r))

/-- The same-level transform: the five terms of `b1wSameLevel`, at the stage `i'` with the same
level, component and vector and the shifted moment. -/
def b1wSameTransform (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ) : Vec 2 → ℂ := fun z =>
  if i'.1 = i.1 then
    (inner ℝ (b1wSameVec i i') (b1wVec i') : ℂ) *
      ((if b1wMom i' = ((b1wMom i).1 - 2, (b1wMom i).2) then
          ((G 0 0 * (((b1wMom i).1 : ℝ) * (((b1wMom i).1 : ℝ) - 1)) : ℝ) : ℂ) * φ z else 0) +
        (if b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2 - 1) then
          (((G 0 1 + G 1 0) * (((b1wMom i).1 : ℝ) * ((b1wMom i).2 : ℝ)) : ℝ) : ℂ) * φ z
        else 0) +
        (if b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 2) then
          ((G 1 1 * (((b1wMom i).2 : ℝ) * (((b1wMom i).2 : ℝ) - 1)) : ℝ) : ℂ) * φ z else 0) +
        (if b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2) then
          (((b1wMom i).1 : ℝ) : ℂ) * ((vf z 0 : ℂ) * φ z +
            ∑ k : Fin 2, ((G k 0 + G 0 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z) else 0) +
        (if b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 1) then
          (((b1wMom i).2 : ℝ) : ℂ) * ((vf z 1 : ℂ) * φ z +
            ∑ k : Fin 2, ((G k 1 + G 1 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z) else 0))
  else 0

/-- One letter expansion `b1wLetterExpansion` restricted to the stage `i'` at the previous
level: the component of `i'`, the coefficient `⟨γ.map* e, b'⟩` of its basis vector, and the
moments `β₀ + #ω - a` equal to that of `i'`. -/
def b1wLetterPart {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ)
    (i' : B1WIndex ι h Nw m Ks) : Vec 2 → ℂ := fun z =>
  ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
      (l.succ, x) (l.castSucc, i'.2.1),
    if hd : d ∈ Finset.Icc 2 D then
      (((F.letters l).edge x i'.2.1 ⟨d, hd⟩).map fun γ =>
        ∑ α : DerivativeWord2 (d - 1),
          ∑ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
            ∑ ω : DerivativeWord2 s,
              ((((F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
                ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
                    Finset.range ((wordCount α).2 + 1),
                  if b1wMom i' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2)
                  then
                    ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                        (β₀.1 + (wordCount ω).1).descFactorial a.1 *
                        (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
                      (inner ℝ (ContinuousLinearMap.adjoint γ.map e) (b1wVec i') : ℂ) *
                      fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                        (fun z' => ((iteratedFDeriv ℝ s (fun X => γ.coeff α r X z' k) F.X₀
                          (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z)
                  else 0)).sum
    else 0

/-- The letter transform: the three moment-flux variants of clause 1, through the letter `l` from
the level of `i'` to the level of `i`. -/
def b1wLetterTransform {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (r : ℝ) (φ : Vec 2 → ℂ) : Vec 2 → ℂ := fun z =>
  ∑ l : Fin Nw, if i.1 = l.succ ∧ i'.1 = l.castSucc then
    -((((b1wMom i).1 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1 - 1, (b1wMom i).2) 0 r φ i' z) -
      (((b1wMom i).2 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1, (b1wMom i).2 - 1) 1 r φ i' z -
      ∑ k : Fin 2, b1wLetterPart F θ l i.2.1 (b1wVec i) (b1wMom i) k r
        (fibreCovDeriv (-θ) k φ) i' z
  else 0

/-- **The test transform of the stage expansion** `T_{i,i'} = T^{same} + T^{letter}`. -/
def b1wTestTransform {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (r : ℝ) (φ : Vec 2 → ℂ) : Vec 2 → ℂ := fun z =>
  b1wSameTransform θ (F.G r) (F.v r) i i' φ z + b1wLetterTransform F θ i i' r φ z

end Defs

/-- **The stage expansion of the tested sources.** For a.e. time of the piece, the tested
source of every stage against a `C^{d_max+1}` periodic test (`d_max` the largest letter order) is
the sum over the stages (`B1WIndex`) of the cell pairings of their values with the test transforms.

The degenerate cases are included. Level `0`, `β = 0`: both sides vanish (the moment derivatives
and the previous flux are `0`; every same-level indicator needs a lower moment, and no letter
reaches level `0`). `N_w = 0`: only the same-level part. `β = (1, 0)` at level `0`: the only term
is the stage `(0, x, (0,0), b)` with `T = v₀φ + ∑_k (G k0 + G 0k) D_{-θ,k}φ`, the first-order
moment equation. A one-dimensional `h x` (`b` unique): the basis expansion is trivial. -/
def StageExpansionStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (m : ℕ)
    (Ks : Fin Nw → ℕ),
  (∀ l, (F.letters l).slow = Ks l) → (∀ l, (F.letters l).order ≤ F.J) →
  LetterBlochStatement.{u, v} → AmplitudeIdMoments F →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
    ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ),
      ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ z in AVenhance.unitCube,
          b1wStageVal F θ i' r z * b1wTestTransform F θ i i' r φ z

/-- **Only earlier stages appear in the expansion.**

Same level: the five shifts lower `|β|` by `1` or `2` (or carry a zero coefficient when the
subtraction truncates). Previous level: `|β'| ≤ |β| + K_s(l)`, so `deg i' ≤ deg i` and `i'` has
the lower level. -/
def StageTransformEarlierStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (m : ℕ)
    (Ks : Fin Nw → ℕ),
  (∀ l, (F.letters l).slow = Ks l) →
  ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
    ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The terminal output relation of the word fibre facts (statement)

The last clause of the word fibre facts bounds the moment amplitude of the terminal level at `b` by the slow stage of
the output stage `out β` at `b`. The slow test is `q(b) = 1`, so that stage is the `ℓ²` norm of the
cell means `⟨W_i(b), 1⟩` over the stages `i = (N_w, x, β', e)` with `|β'| = |β|`. For a single
component `x` and moment `β`, Parseval over an orthonormal basis `(e)` of `h x` and
`(∫ cos f)² + (∫ sin f)² = |∫ e^{-iθ·y} f|²` turn the amplitude into
`(∑_e |∫ e^{-iθ·y} (ϖy)^β ⟨e, u_N(b)⟩|²)^{1/2}`. The phase integral is the cell integral of the
Bloch periodic part (`integral_phase_eq_cell_planeBlochC`), which is the cell mean of the stage
value divided by its scale `c_i = π_x^{-1/2} ϖ^{|β|}/β! · A_N⁻¹`. So the moment amplitude is at
most `β! A_N` times the stage norm of the cell means (`TerminalOutputStatement`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- **The terminal output relation.**

For `N_w = 0`, `β = 0`, one component, `h x = ℝ` and `e = 1`, the amplitude is
`π_x^{-1/2} |∫ e^{-iθ·y} u(b)|`, the scale is `π_x^{-1/2}` (`A_0 = 1`), and the cell mean of the
Bloch part is the phase integral, so equality holds. For `θ = 0` one has `sin = 0`, `cos = 1`, and
the Bloch part's cell mean is `∫ y^β ⟨e, u⟩`. Several `β'` with `|β'| = |β|` share the stage
`out β`, while the left side uses only `β' = β`, so in general the inequality is strict.
The factor `β! A_N` is explicit; there is no other constant. -/
def TerminalOutputStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ),
    (∀ i, cellValue (Dθ i) F.b =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 F.b) y))) →
    (∀ i, MemLp (cellValue (Dθ i) F.b) 2 (volume.restrict AVenhance.unitCube)) →
    AmplitudeIdMoments F →
    0 < b1wAmp F.ηg F.letters (Fin.last Nw) →
    ∀ β ∈ momentIndices m,
      momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ ≤
        ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
          b1wAmp F.ηg F.letters (Fin.last Nw) *
          stageNorm b1wSt (b1wOut Nw Ks β) (fun i => cellComplexPair
            (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) F.b))
            (cellConstantCLM 1)))

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The bounds of the stage transforms (statements)

The stage expansion pairs earlier stage values with the transforms `T_{i,i'}` of the test.
In the normalization of the word fibre facts the test family of a stage `k'` is
`Φ_{i'} = ∑_{i ∈ stage k} (c_i/c_{i'}) conj(T_{i,i'}(conj ψ_i))`, with `c` the stage scales
(`b1wScale`). These operators are bounded in Sobolev norms, dimension-free and with no `P_e`:

* `SameLevelTransformBoundStatement`: same level, `H^{n+1} → H^n`. The drift enters as `ϖ v`, and
  `ϖ ≤ √η` (`S ≥ 1`) gives `ϖ |D^l v| ≤ C_{vj}(l)`. The metric is bounded by `IsCellMetric`.
* `LetterTransformBoundAEStatement`: from level `l + 1` to level `l`, `H^{n+d_l} → H^n` for
  `n + d_max ≤ J`, at almost every time (the coefficient jets are bounded in essential supremum
  over time). The analytic envelope (`IsCycleLetter.analytic`) bounds the constituents summed
  with `‖γ.map‖` by `√(π_v/π_u)` times the majorant. That factor is the ratio of the stage scales,
  the majorant's row and column sums are at most `θ_l` (the amplitude ratio `A_{l+1}/A_l`, a Schur
  bound over the components), and the vector `γ.map* e` acts by its operator norm on the basis
  (Parseval). The powers of `ϖ` are nonnegative: `|β| - |β''| + s ≥ 0`.

The input tests are `TorusHk N` with `N ≥ d_max + 3`, so they have `C^{d_max+1}` classical
representatives (`torusHigherClassicalValue`), as the stage expansion needs. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- The scale ratio `c_i / c_{i'}` of two stages. -/
def b1wScaleRatio {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {D Nw m : ℕ} {Ks : Fin Nw → ℕ} (π : ι → ℝ) (ϖ ηg : ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (i i' : B1WIndex ι h Nw m Ks) : ℂ :=
  b1wScale π ϖ ηg letters i / b1wScale π ϖ ηg letters i'

/-- **The same-level transform bound.**

For `|β| ≤ 0` every indicator fails or has a zero coefficient, so `Φ = 0`.
For `v = 0`, `G = I`, `Φ` is `ϖ^2` or `ϖ` times derivatives of order `≤ 1` of the tests, so
`C = C(n)`. For `dim h x = 1` there is one basis vector. The constant `C` is chosen after the word
parameters, `ρ` and `n`, and before the components, the data and the time. -/
def SameLevelTransformBoundStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ),
  ∃ C : ℝ, 0 ≤ C ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ r ∈ Icc F.a F.b, ∀ (k k' : ℕ),
    (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        i'.1 = i.1) →
  ∀ (N : ℕ), n + 1 ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
    ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk n ℂ,
      (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wSameTransform θ (F.G r) (F.v r) i i'
              (fun y => star (torusHigherClassicalValue N (ψ i) y)) z)) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2

/-- **The letter transform bound**, for almost every time: the coefficient jets of the letters are
bounded only in essential supremum over time (`IsAnalyticEnvelope`), so one null set of times is excluded before the stages, the orders and the tests.

For a letter with no edges (`θ_l = 0`) the transform is `0`. For one component and one
constituent of order `2`, slow order `0` and constant coefficient `c`, `Φ` is `ϖ`-weighted first
derivatives of `c ψ` (one zero of the transfer), bounded by `|c| ≤ θ_l`, divided by the amplitude
`θ_l`. For a positive letter one has the Taylor factor `(ϖη_g)^s/s!` with `s ≥ 1` against the
amplitude `θ_l η_g`. The constant is chosen at the same stage as in the previous statement. -/
def LetterTransformBoundAEStatement : Prop :=
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
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (k k' : ℕ),
    (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      i.1 = l.succ) →
    (∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
      i'.1 = l.castSucc) →
  ∀ (N : ℕ), n + d l ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
    ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk n ℂ,
      (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N (ψ i) y)) z)) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2


/-- **The same-level transform bound at every frequency of the zone**: the
frequency hypothesis is `|θ_k| ≤ ρ` in place of `|ξ| ≤ ρ`; the proofs of the transform bounds use only this
(`theta_abs_le`), and `SameLevelTransformBoundStatement` is its corollary. -/
def SameLevelTransformBoundZoneStatement : Prop :=
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
  ∀ (N : ℕ), n + 1 ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
    ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk n ℂ,
      (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wSameTransform θ (F.G r) (F.v r) i i'
              (fun y => star (torusHigherClassicalValue N (ψ i) y)) z)) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2

/-- **The letter transform bound at every frequency of the zone**, almost
every time; `LetterTransformBoundAEStatement` is its corollary. -/
def LetterTransformBoundAEZoneStatement : Prop :=
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
  ∀ (N : ℕ), n + d l ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
    ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk n ℂ,
      (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N (ψ i) y)) z)) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Data and proved producers used by the bounded interior-package assembly. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

/-- The physical inputs of the graph and row producer: the constants and the drift bounds of the
constructed cell problem. -/
structure InteriorPhysicalInputs (K : ScalarConstants) (α q : ℝ) (Λ : ℕ)
    (ζ : ℝ → ℝ) (m : ℕ) (ν B : ℝ) (y₀ : Vec 2) where
  seed : ScalarConstants
  Cw : ℝ
  hCw : 0 ≤ Cw
  constants_eq : K = scalarBufferedComparisonConstants
    (constructedScalarFibreConstants seed Cw hCw)
  hΛ : 1 ≤ Λ
  hζ : IsFastProfile ζ
  hν : 0 < ν
  flux_eq : B = ocMeanFlux α q Λ ζ m ν
  scale_pos : 0 < ocEll q Λ m ν ^ 2
  pulse_ratio : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m
  drift : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)
  bound : ℝ
  drift_bound : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ bound ^ 2
  scaled_bound : ∀ t x, Real.sqrt (ν / B) *
    Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw
  contrast_nonneg : 0 ≤ ν / B
  contrast_le_one : ν / B ≤ 1
  mean_zero : ∀ t (i : Fin 2),
    cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x i : ℂ)) = 0
  smooth : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t)
  drift_jets : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
    (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ K.Cvj j

/-- A block context fixes the numerical constants before its physical realization. -/
structure InteriorBlockContext (K : ScalarConstants) where
  α : ℝ
  q : ℝ
  Λ : ℕ
  ζ : ℝ → ℝ
  m : ℕ
  ν : ℝ
  B : ℝ
  y₀ : Vec 2
  inputs : InteriorPhysicalInputs K α q Λ ζ m ν B y₀
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  metric : IsCellMetric (fun t _ => G t)
  g : ℝ
  metric_near : IsMetricNearIdentity (fun t _ => G t) g
  metric_small : g ≤ 1 / 16
  Θ : ℝ
  threshold : 1 ≤ Θ
  ta : ℝ
  T : ℝ
  admissible : IsOCAdmissibleInterval α q Λ ζ m ν B Θ K.θs ta T

namespace InteriorBlockContext

def eta {K : ScalarConstants} (d : InteriorBlockContext K) := d.ν / d.B
def drift {K : ScalarConstants} (d : InteriorBlockContext K) :=
  ocCellDrift d.α d.q d.Λ d.ζ d.m d.ν d.y₀
def left {K : ScalarConstants} (d : InteriorBlockContext K) := d.ta / ocEll d.q d.Λ d.m d.ν ^ 2
def length {K : ScalarConstants} (d : InteriorBlockContext K) := d.T / ocEll d.q d.Λ d.m d.ν ^ 2
def right {K : ScalarConstants} (d : InteriorBlockContext K) := (d.ta + d.T) / ocEll d.q d.Λ d.m d.ν ^ 2
def weight {K : ScalarConstants} (d : InteriorBlockContext K) := Real.sqrt (d.eta / d.length)
def tau {K : ScalarConstants} (d : InteriorBlockContext K) :=
  ocTau d.α d.q d.Λ d.m / ocEll d.q d.Λ d.m d.ν ^ 2

theorem right_eq {K : ScalarConstants} (d : InteriorBlockContext K) :
    d.right = d.left + d.length := by
  unfold right left length
  ring

end InteriorBlockContext

/-- All local fields already produced by the existing fibre and geometry modules. -/
structure PreparedInteriorData {K : ScalarConstants} (d : InteriorBlockContext K) where
  reg : BlockRegions
  quiet_iff : ∀ t, t ∈ reg.quiet ↔
    ∀ s ∈ Set.Icc (t - d.tau / 24) (t + d.tau / 24), ∀ z, d.drift s z = 0
  actual : FibreScalarData K d.eta d.G d.drift d.left d.length
  /-- The actual symbol is the literal coefficient symbol of the actual drift. -/
  lam_eq : ∀ (hη : d.eta ≤ 1) (hw : ∀ t x, Real.sqrt d.eta *
      Real.sqrt (∑ i, d.drift t x i ^ 2) ≤ K.Cw),
    actual.lam = fibreCoefficientSymbol d.eta d.G d.drift
      (fibreCoefficientFamily d.eta K.Cw hη d.G d.metric d.inputs.drift hw)
  quiet_zero : ∀ t ∈ reg.quiet ∩ Set.Icc d.left (d.left + d.length), ∀ z, d.drift t z = 0
  cover : ∀ t ∈ Set.Icc d.left (d.left + d.length), t ∈ reg.quiet ∨ ∃ p, t ∈ Set.Icc (reg.lo p) (reg.hi p)
  buffer_nonneg : 0 ≤ reg.buffer
  buffer_le : reg.buffer ≤ d.length
  joins_ge : 2 * reg.P ≤ reg.joins
  buffer_inside : ∀ p, Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) ⊆
    Set.Icc d.left (d.left + d.length)
  buffer_quiet : ∀ p, Set.Ico (reg.lo p - reg.buffer) (reg.lo p) ⊆ reg.quiet ∧
    Set.Ioc (reg.hi p) (reg.hi p + reg.buffer) ⊆ reg.quiet
  ext : Fin reg.P → ℝ → Vec 2 → Vec 2
  ext_local : ∀ p, FibreScalarData K d.eta d.G (ext p) d.left d.length
  ext_shear : ∀ p, ∃ V : ℝ → ℝ → ℝ,
    ∀ t z, ext p t z = V t (z (reg.orient p).rev) • basisVec (reg.orient p)
  ext_drift : ∀ p, IsCellDrift (ext p) ∧ (∀ t (k : Fin 2), cellMean (fun x => (ext p t x k : ℂ)) = 0) ∧
    ∀ t x, Real.sqrt d.eta * Real.sqrt (∑ i, ext p t x i ^ 2) ≤ K.Cw
  ext_agree : ∀ p, ∀ t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer), ∀ z,
    ext p t z = d.drift t z
  replace_graph : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      cellSobolevNorm j (fun x => cellValue (fibreSeriesJet actual.r ξ) t x -
          cellValue (fibreSeriesJet (ext_local p).r ξ) t x) ≤
        ENNReal.ofReal (K.Cj j * peFactor d.eta ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_row : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ s ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p),
      cellSobolevNorm j (fun x => fibreSeriesFun actual.ell ξ s x -
          fibreSeriesFun (ext_local p).ell ξ s x) ≤
        ENNReal.ofReal (K.Cj j * peFactor d.eta ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_symbol : ∀ (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      ‖fibreSeriesC actual.lam ξ t - fibreSeriesC (ext_local p).lam ξ t‖ ≤
        K.Cj 0 * peFactor d.eta ^ K.Qj 0 * fibreNorm ξ ^ 2 * Real.exp (-(K.cj 0) * reg.buffer)
  orientation : ∀ p, ∃ k : ℤ, Odd k ∧
    (∀ t ∈ Icc (reg.lo p) (reg.hi p),
      |ocEll d.q d.Λ d.m d.ν ^ 2 * t - k * ocTau d.α d.q d.Λ d.m| ≤
        3 / 4 * ocTau d.α d.q d.Λ d.m) ∧
    reg.orient p = (if k % 4 = 3 then 0 else 1)
  joins_upper : (reg.joins : ℝ) ≤ d.T / ocTau d.α d.q d.Λ d.m + 4
  buffer_lower : (∀ t ∈ Icc (d.left - d.tau / 24) (d.left + 7 * d.tau / 24) ∪
    Icc (d.right - 7 * d.tau / 24) (d.right + d.tau / 24), ∀ z, d.drift t z = 0) →
    min (d.tau / 4) d.length ≤ reg.buffer
  marks_in : ∀ j, ∀ t ∈ reg.marks j, d.left ≤ t ∧ t + K.θs ≤ d.right
  marks_sep : ∀ j, ∀ t ∈ reg.marks j, ∀ t' ∈ reg.marks j, t ≠ t' →
    t + K.θs ≤ t' ∨ t' + K.θs ≤ t
  marks_count : ∀ j, (1 - Real.exp (-2)) / 288 * d.length / K.θs ≤
    ((reg.marks j).card : ℝ)
  marks_core : ∀ j, ∀ t ∈ reg.marks j, ∃ k : ℤ,
    k % 4 = (if j = 0 then 3 else 1) ∧
    IsOCCompleteCore d.α d.q d.Λ d.m (ocLabel d.α d.q d.Λ d.m k) k ∧
    ((k : ℝ) - 1 / 3) * ocTau d.α d.q d.Λ d.m ≤ ocEll d.q d.Λ d.m d.ν ^ 2 * t ∧
    ocEll d.q d.Λ d.m d.ν ^ 2 * (t + K.θs) ≤
      ((k : ℝ) + 1 / 3) * ocTau d.α d.q d.Λ d.m

/-- The prepared package is constructed, rather than assumed as an assembly ingredient. -/
theorem preparedInteriorData_exists {K : ScalarConstants} (d : InteriorBlockContext K) :
    Nonempty (PreparedInteriorData d) := by
  classical
  obtain ⟨seed, Cw, hCw, hK, hΛ, hζ, hν, hB, hL, hr, hv, V, hb, hw,
    hη0, hη1, hm, _hsm, _hj⟩ := d.inputs
  let a := d.left
  let b := d.right
  let τ := d.tau
  let quiet := interiorTrimmedQuiet τ d.drift
  let D := interiorQuietBuffer τ a b quiet
  have hτ : 0 < τ := div_pos
    (AVRegularity.Construction.Stream.ocTau_pos (α := d.α) (q := d.q) (m := d.m) hΛ) hL
  have hlen : b - a = d.length := by
    dsimp only [a, b]
    rw [d.right_eq]
    ring
  have hS : 0 ≤ d.length := zero_le_one.trans (d.threshold.trans d.admissible.2.1)
  have hab : a ≤ b := sub_nonneg.mp (hlen.symm ▸ hS)
  have hDb := interiorQuietBuffer_bounds hτ hab quiet
  have hleft : Ico a (a + D) ⊆ quiet := interiorQuietBuffer_left hτ hab quiet
  have hright : Ioc (b - D) b ⊆ quiet := interiorQuietBuffer_right hτ hab quiet
  have hleftD : ∀ t ∈ Ico a (a + D), ∀ z, d.drift t z = 0 :=
    fun t ht => interiorTrimmedQuiet_drift hτ.le (hleft ht)
  have hrightD : ∀ t ∈ Ioc (b - D) b, ∀ z, d.drift t z = 0 :=
    fun t ht => interiorTrimmedQuiet_drift hτ.le (hright ht)
  obtain ⟨marks, hcount, hin, hsep, hcore⟩ :=
    interior_cell_marks d.ν d.B d.Θ K.θs d.ta d.T hL d.admissible
  let reg := interiorBufferedBlockRegions τ a b D d.drift marks
  have hflux : d.eta = d.ν / ocMeanFlux d.α d.q d.Λ d.ζ d.m d.ν := by
    simp only [InteriorBlockContext.eta, hB]
  have hf := interiorBufferedGraphRowData hΛ hζ hν hr d.y₀ a b D marks hL hDb.1 hDb.2.1
    hleft hright hv V hb d.G d.metric Cw hCw
    (hflux ▸ hw) (hflux ▸ hη0) (hflux ▸ hη1) hm
    d.metric_near d.metric_small seed a d.length
  rw [← hK, ← hflux] at hf
  obtain ⟨actual, hlam, extlocal, hgraph, hrow, hsymbol⟩ := hf
  have hjoin : (b - a) / τ = d.T / ocTau d.α d.q d.Λ d.m := by
    rw [hlen]
    dsimp only [InteriorBlockContext.length, τ, InteriorBlockContext.tau]
    have hτp := AVRegularity.Construction.Stream.ocTau_pos (α := d.α) (q := d.q) (m := d.m) hΛ
    have hell : ocEll d.q d.Λ d.m d.ν ≠ 0 := by
      intro hz
      rw [hz] at hL
      norm_num at hL
    field_simp [hell, hτp.ne']
  have hwK : ∀ t x, Real.sqrt d.eta * Real.sqrt (∑ i, d.drift t x i ^ 2) ≤ K.Cw := by
    simpa only [hK, scalarBufferedComparisonConstants, scalarConstantsWithGapRates,
      scalarConstantsWithJetPrices, scalarConstantsWithRadius, constructedScalarFibreConstants]
      using (show ∀ t x, Real.sqrt d.eta * Real.sqrt (∑ i, d.drift t x i ^ 2) ≤ Cw from hw)
  refine ⟨{
    reg := reg, quiet_iff := fun _ => Iff.rfl, actual := actual, lam_eq := hlam,
    quiet_zero := ?_, cover := ?_, buffer_nonneg := hDb.1,
    buffer_le := hlen ▸ hDb.2.2, joins_ge := ?_, buffer_inside := ?_, buffer_quiet := ?_,
    ext := interiorOrientationExtensions d.α d.q d.Λ d.ζ d.m d.ν d.y₀ a b,
    ext_local := extlocal, ext_shear := ?_, ext_drift := ?_, ext_agree := ?_,
    replace_graph := ?_, replace_row := ?_, replace_symbol := ?_,
    orientation := ?_, joins_upper := ?_, buffer_lower := ?_,
    marks_in := hin, marks_sep := hsep, marks_count := hcount, marks_core := hcore }⟩
  · intro t ht
    exact interiorTrimmedQuiet_drift hτ.le ht.1
  · intro t ht
    apply interiorBufferedActualRegions_cover (α := d.α) (q := d.q) (Λ := d.Λ)
      (ζ := d.ζ) (m := d.m) hΛ hζ d.ν d.y₀ hL a b D marks hleft hright t
    simpa only [a, b, d.right_eq] using ht
  · exact le_of_eq (interiorBufferedBlockRegions_joins τ a b D d.drift marks)
  · simpa only [← d.right_eq] using
      interiorBufferedBlockRegions_inside τ a b D d.drift marks
  · exact interiorBufferedActualRegions_quiet_buffers hΛ hζ d.ν d.y₀ hL a b D marks
      hleft hright hDb.2.1
  · exact interiorOrientationExtensions_shear d.ν d.y₀ a b D marks
  · exact interiorOrientationExtensions_drift hΛ hζ d.ν d.y₀ a b d.eta K.Cw
      (by simpa only [hK, scalarBufferedComparisonConstants, scalarConstantsWithGapRates,
        scalarConstantsWithJetPrices, scalarConstantsWithRadius, constructedScalarFibreConstants]
        using hCw) hv hwK
  · exact interiorOrientationExtensions_agree hΛ hζ d.ν d.y₀ hL a b D marks hDb.2.1 hleftD hrightD
  · intro j p ξ hreal hξ t ht
    exact hgraph p j ξ hreal hξ t ht
  · intro j p ξ hreal hξ t ht
    exact hrow p j ξ hreal hξ t ht
  · exact hsymbol
  · exact interiorBufferedActualRegions_orientations d.ν d.y₀ hL a b D marks
  · rw [← hjoin]
    exact interiorBufferedBlockRegions_join_bound hτ hab D d.drift marks
  · intro hquiet
    change min (τ / 4) d.length ≤ D
    rw [← hlen]
    exact interiorQuietBuffer_lower τ a b quiet (interior_trimmed_ends hquiet)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! The ingredients of `scalar_package_interior`.

Each ingredient is a closed proposition that carries its own constants, quantified in the order
the statement allows, so it can be proved on its own and the assembly combines the witnesses.

* `InteriorDriftScaleStatement`: the drift jets of the normalized constructed drift and its cell
  stream function, uniformly over band chains and levels.
* `CellQuietGapStatement`: the sharp gap `π²/2` of the nonconstant harmonics on drift-free
  times (the quiet middle regions).
* `InteriorHighSmoothingStatement`: full Brillouin-band smoothing of the forward and reversed
  fibre propagators of the constructed cell problems at polynomial cost (the complementary band).
* `CellChartWeightsStatement`: the chart weights and fluxes.
* `CellNegativeAdjointStatement`: propagation of the transposed scalar equation in
  negative-weight positive Sobolev norms.

The quiet-gap, chart-weight and adjoint statements are generic in the cell problem: their
hypotheses are the uniform bounds `CellProblemBounds`, which the constructed drift satisfies by
`InteriorDriftScaleStatement` and proved facts; the smoothing statement is for the constructed
drift, whose energy hierarchy is proved. The Gaussian, the phase jets, the graph and row records,
the replacement bounds, the marks, the contraction and the quiet mean are proved and discharged
in the assembly. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

/-- The uniform bounds of one cell problem (contrast `η`, time-only metric `G`, drift `v`):
`w = √η v` is bounded by `Cw` with jets bounded by `Cvj`, and `v = σ∇ψ` for a smooth periodic
stream function with `√η|ψ| ≤ Cψ`. -/
structure CellProblemBounds (Cw Cψ : ℝ) (Cvj : ℕ → ℝ) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) : Prop where
  eta_pos : 0 < η
  eta_le : η ≤ 1
  metric : IsCellMetric (fun t _ => G t)
  drift : IsCellDrift v
  mean_zero : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0
  smooth : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)
  scaled : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw
  jets : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j
  stream : ∃ ψ : ℝ → Vec 2 → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2) ∧
    (∀ t, AVenhance.IsZ2Periodic (ψ t)) ∧ (∀ t z, v t z = streamVel ψ t z) ∧
    ∀ t z, Real.sqrt η * |ψ t z| ≤ Cψ

/-- **Drift scale.** For `Λ` large, the normalized constructed drift has jets bounded uniformly
over band chains, levels and centres, and a smooth periodic cell stream function with
`√η|ψ| ≤ Cψ`. -/
def InteriorDriftScaleStatement : Prop :=
  ∀ (α s q : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → IsAdmissibleQ α s q →
  ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
  ∃ Λ₁ : ℕ, ∀ Λ : ℕ, Λ₁ ≤ Λ → ∃ (Cψ : ℝ) (Cvj : ℕ → ℝ),
    ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ y₀ : Vec 2,
      (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
        (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ Cvj j) ∧
      ∃ ψ : ℝ → Vec 2 → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2) ∧
        (∀ t, AVenhance.IsZ2Periodic (ψ t)) ∧
        (∀ t z, ocCellDrift α q Λ ζ m ν y₀ t z = streamVel ψ t z) ∧
        ∀ t z, Real.sqrt (ν / B) * |ψ t z| ≤ Cψ

/-- The sharp gap `π²/2` of the nonconstant harmonics of Brillouin-zone fibre solutions on
drift-free intervals. -/
def CellQuietGapBounds (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
  ∀ a b : ℝ, a ≤ b → (∀ t ∈ Set.Icc a b, ∀ z, v t z = 0) →
  ∀ D : ℝ → RawJet2 1 ℂ,
    IsCellSolution (Set.Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) D →
    cellL2Norm (cellQ0 (cellValue D b)) ≤
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2) * (b - a))) *
        cellL2Norm (cellQ0 (cellValue D a))

/-- **Quiet gap.** On a drift-free interval the nonconstant harmonics of a Brillouin-zone fibre
solution decay at the sharp rate `π²/2`. -/
def CellQuietGapStatement : Prop :=
  ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2),
    0 < η → IsCellMetric (fun t _ => G t) → IsCellDrift v → CellQuietGapBounds η G v

/-- Full Brillouin-band smoothing of the forward and reversed fibre propagators from `L²` to
`C^j` at cost `C_j P_e^{Q_j}(1+(t-s))^{Q_j}(1+(t-s)^{-j/2})`. -/
def CellHighSmoothingBounds (C : ℕ → ℝ) (Q : ℕ → ℕ) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
  ∀ s t : ℝ, s < t →
    (∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
        cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (C j * peFactor η ^ Q j * (1 + (t - s)) ^ Q j *
            (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue D s)) ∧
    (∀ Ψ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc (-t) (-s))
        (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
          (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) Ψ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
        cellValue Ψ (-s) =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (C j * peFactor η ^ Q j * (1 + (t - s)) ^ Q j *
            (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue Ψ (-t)))

/-- **High smoothing.** For `Λ` large, the forward and reversed fibre propagators of the
constructed cell problems smooth on the full Brillouin band, with constants uniform over band
chains, levels, centres and time-only metrics. -/
def InteriorHighSmoothingStatement : Prop :=
  ∀ (α s q : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → IsAdmissibleQ α s q →
  ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
  ∃ Λ₁ : ℕ, ∀ Λ : ℕ, Λ₁ ≤ Λ → ∃ (C : ℕ → ℝ) (Q : ℕ → ℕ), (∀ j, 0 < C j) ∧
    ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ y₀ : Vec 2,
    ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ, IsCellMetric (fun t _ => G t) →
      CellHighSmoothingBounds C Q (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)

/-- Chart weights comparable to `(1 + ϖ²|z|²)^m`, `ϖ = √(η/S)`, with defect inequality, flux
bound and rates `≤ C_m/S` on every window of length `S ≥ 1`. -/
def CellChartWeightsBounds (Cwt : ℕ → ℝ) (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ t₀ S : ℝ, 1 ≤ S → ∀ M : ℕ,
    Nonempty (ChartWeights (fun t _ => G t) v t₀ S (Real.sqrt (η / S)) 0 M Cwt)

/-- **Chart weights.** The weight constants depend only on the uniform bounds of the cell
problem. -/
def CellChartWeightsStatement : Prop :=
  ∀ (Cw Cψ : ℝ) (Cvj : ℕ → ℝ), ∃ Cwt : ℕ → ℝ, (∀ m, 0 < Cwt m) ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2),
      CellProblemBounds Cw Cψ Cvj η G v → CellChartWeightsBounds Cwt η G v

/-- Propagation of the transposed scalar equation on the plane in the norms
`‖⟨ϖz⟩^{-p} D^a u‖`, `a ≤ k`, `ϖ = √(η/S)`, on every subinterval of a window of length `S`, at
cost `C P_e^Q (1+(t-s))^Q`. -/
def CellNegativeAdjointBounds (Cneg : ℕ → ℕ → ℝ) (Qneg : ℕ → ℕ) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ (t₀ S : ℝ), 0 < S →
  ∀ (k p : ℕ) (s t : ℝ), t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
  ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
    (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
    (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
    IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
      (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
    weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k (Real.sqrt (η / S)) 1
        (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
      ENNReal.ofReal (Cneg k p * peFactor η ^ Qneg k * (1 + (t - s)) ^ Qneg k) *
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k (Real.sqrt (η / S)) 1
          (fun x a w' => planeJetOrder (f x) a w')

/-- **Negative-weight adjoint propagation.** The constants depend only on the uniform bounds of
the cell problem. -/
def CellNegativeAdjointStatement : Prop :=
  ∀ (Cw Cψ : ℝ) (Cvj : ℕ → ℝ), ∃ (Cneg : ℕ → ℕ → ℝ) (Qneg : ℕ → ℕ),
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2),
      CellProblemBounds Cw Cψ Cvj η G v → CellNegativeAdjointBounds Cneg Qneg η G v

end AVRegularity.CycleWords.Assembly
end
end
end
