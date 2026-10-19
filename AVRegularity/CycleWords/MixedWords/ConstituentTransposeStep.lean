-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.MixedWordsB1ZeroWord
public import AVRegularity.CycleWords.MixedWords.JetToValueStep
import AVRegularity.CycleComparison.Reconstruction.ChainLinear
import AVRegularity.CycleWords.MixedWords.AfwCrude

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: the named steps (statements)

`LetterBlochStatement` is split into the following steps, each a `Prop` on the frame of the
amplitude identification (`AmplitudeIdFrame`), proved in the `LetterBloch*` modules.

* `LetterBlochGood F r`: the integrability facts at time `r` (values, flux, weak jets of `w`
  against every monomial) and `u = w` as values.
* `LetterBlochIntegrableAE F`: `Good` holds for a.e. `r ∈ [a, b]`.
* `LetterBlochClause1 F`, `LetterBlochClause2 F`, `LetterBlochClause3 F`: the three clauses at a
  time where `Good` holds (clause 2 needs nothing).
* `TaylorWordExpansion`: the multilinear expansion of the slow Taylor monomial.
* `LetterFluxPointwise F`: the pointwise expansion of the level `j + 1` flux over the letter.
* `WeakJetToValue`: the weak (Sobolev) form of the jet-to-value transfer.
* `letterBloch_frame`: the clauses and the integrability give the frame form of `letterBloch`. -/

universe u v

/-- The multilinear expansion of the slow Taylor monomial:
`D^s f(X₀)[δy, …, δy] = ∑_ω δ^s y^{#ω} D^s f(X₀)[e_ω]`. -/
def TaylorWordExpansion : Prop :=
  ∀ (f : Vec 2 → ℝ) (X₀ : Vec 2) (s : ℕ) (δ : ℝ) (y : Vec 2),
    iteratedFDeriv ℝ s f X₀ (fun _ => δ • y) =
      ∑ ω : DerivativeWord2 s, δ ^ s * momentWeight (wordCount ω) y *
        iteratedFDeriv ℝ s f X₀ (fun i => basisVec (ω i))

/-- The weak jet-to-value transfer: for a plane `H^K` function with all weighted jets integrable
and a smooth periodic test `c ψ`, the Bloch pairing of the order-`n` jet equals `b1wJetPair` of
its value. -/
def WeakJetToValue : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (θ : Vec 2) (K n : ℕ) (hn : n ≤ K)
    (w : DerivativeWord2 n) (β : ℕ × ℕ) (W : PlaneHk Set.univ K E) (e' : E),
    (∀ (γ : ℕ × ℕ) (n' : ℕ) (v : DerivativeWord2 n'),
      Integrable (fun y => momentWeight γ y • planeJetOrder W n' v y)) →
    ∀ (c : Vec 2 → ℝ) (ψ : Vec 2 → ℂ), ContDiff ℝ n c → AVenhance.IsZ2Periodic c →
      ContDiff ℝ n ψ → AVenhance.IsZ2Periodic ψ →
      ∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e' (planeJetOrder W n w y)) z *
            ((c z : ℂ) * ψ z) =
        b1wJetPair θ β e' (planeValue W) c w ψ

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
  {K : ScalarConstants} {g₁ : ℝ}

/-- Time `r` belongs to the window, and at every level and component `u = w` as values, the
value and the previous-level flux have all monomial moments (against every vector), and every
jet of `w` has all monomial moments. -/
def LetterBlochGood (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (r : ℝ) :
    Prop :=
  r ∈ Icc F.a F.b ∧ ∀ (j : Fin (Nw + 1)) (x : ι),
    planeValue (F.u j x r) =ᵐ[volume] planeValue (F.w j x r) ∧
    (∀ (e : h x) (β : ℕ × ℕ),
      Integrable (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x r) y))) ∧
    (∀ (e : h x) (β : ℕ × ℕ) (k : Fin 2),
      Integrable (fun y => momentWeight β y * inner ℝ e
        (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
          (j, x) r y k))) ∧
    ∀ (β : ℕ × ℕ) (n : ℕ) (w : DerivativeWord2 n),
      Integrable (fun y => momentWeight β y • planeJetOrder (F.w j x r) n w y)

/-- **Integrability at a.e. time.** -/
def LetterBlochIntegrableAE
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), LetterBlochGood F r

/-- **Clause 1**: the tested forcing is the same-level terms minus the letter flux pairings. -/
def LetterBlochClause1
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ (θ : Vec 2) (r : ℝ), LetterBlochGood F r →
    ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (φ : Vec 2 → ℂ),
      ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ → AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ j x e β r φ =
        b1wSameLevel θ (F.G r) (F.v r) β e (planeValue (F.u j x r)) φ -
          ((β.1 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1 - 1, β.2) 0 r φ -
          ((β.2 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1, β.2 - 1) 1 r φ -
          ∑ k : Fin 2, b1wFluxPair F θ j x e β k r (fibreCovDeriv (-θ) k φ)

/-- **Clause 2**: the flux pairing vanishes at level `0`. -/
def LetterBlochClause2
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ (θ : Vec 2) (r : ℝ) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
    b1wFluxPair F θ 0 x e β₀ k r ψ = 0

/-- The pointwise letter expansion of the level `j + 1` flux against `e` (the integrand of
`b1wLetterExpansion` before periodization). -/
def LetterFluxPointwise
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ (j : Fin Nw) (x : ι) (e : h x) (k : Fin 2) (r : ℝ) (y : Vec 2),
    inner ℝ e (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
        (j.succ, x) r y k) =
      ∑ x' : ι, ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
          (j.succ, x) (j.castSucc, x'),
        if hd : d ∈ Finset.Icc 2 D then
          (((F.letters j).edge x x' ⟨d, hd⟩).map fun γ =>
            ∑ α : DerivativeWord2 (d - 1),
              ∑ s ∈ Finset.Icc (if (F.letters j).positive then 1 else 0) (F.letters j).slow,
                ∑ ω : DerivativeWord2 s,
                  ((F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)) * momentWeight (wordCount ω) y *
                    iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k) F.X₀
                      (fun i => basisVec (ω i)) *
                    inner ℝ (ContinuousLinearMap.adjoint γ.map e)
                      (planeJetOrder (F.w j.castSucc x' r) (d - 1) α y)).sum
        else 0

/-- **Clause 3**: at level `j + 1` the flux pairing is its letter expansion. -/
def LetterBlochClause3
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  (∀ i, (F.letters i).order ≤ F.J) →
  ∀ (θ : Vec 2) (r : ℝ), LetterBlochGood F r →
    ∀ (j : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
      ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ → AVenhance.IsZ2Periodic ψ →
      b1wFluxPair F θ j.succ x e β₀ k r ψ = b1wLetterExpansion F θ j x e β₀ k r ψ

/-- The frame form of `letterBloch` from its steps. -/
theorem letterBloch_frame
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hI : LetterBlochIntegrableAE F) (h1 : LetterBlochClause1 F) (h2 : LetterBlochClause2 F)
    (h3 : LetterBlochClause3 F) (θ : Vec 2)
    (horder : ∀ i, (F.letters i).order ≤ F.J) :
    ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
      (∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (φ : Vec 2 → ℂ),
        ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ → AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ j x e β r φ =
          b1wSameLevel θ (F.G r) (F.v r) β e (planeValue (F.u j x r)) φ -
            ((β.1 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1 - 1, β.2) 0 r φ -
            ((β.2 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1, β.2 - 1) 1 r φ -
            ∑ k : Fin 2, b1wFluxPair F θ j x e β k r (fibreCovDeriv (-θ) k φ)) ∧
      (∀ (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
        b1wFluxPair F θ 0 x e β₀ k r ψ = 0) ∧
      ∀ (j : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
        ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ → AVenhance.IsZ2Periodic ψ →
        b1wFluxPair F θ j.succ x e β₀ k r ψ = b1wLetterExpansion F θ j x e β₀ k r ψ := by
  filter_upwards [hI] with r hr
  exact ⟨fun j x e β φ hφ hp => h1 θ r hr j x e β φ hφ hp,
    fun x e β₀ k ψ => h2 θ r x e β₀ k ψ,
    fun j x e β₀ k ψ hψ hp => h3 horder θ r hr j x e β₀ k ψ hψ hp⟩

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The word fibre facts: the conclusion for one piece and frequency

`WordFibreFactsAt` is the conclusion of `WordFibreFactsStatement` after its binders: the
instantiation of the abstract fibre word for one word piece at one frequency, with the constants
`M, out, Q, C_z, C_d, C_out, Θ, C_f, c_E`, the datum jets `J₀ n = datumJets … n (planeValue ∘ f)`
and the terminal amplitudes `Amp β = momentAmpNorm … β (planeValue (u_N(b)))` (the only two
places where the chain enters). The statement is
definitionally `∀ K, ∃ g₁, … ∀ θ, |ξ| ≤ ρ → WordFibreFactsAt …` (`wordFibreFactsStatement_iff`),
so the poorly buffered and the well buffered instantiations each produce a `WordFibreFactsAt`, and
the final case split picks one. -/

universe u v

/-- **The conclusion of `WordFibreFactsStatement`** for one piece and frequency. -/
def WordFibreFactsAt (K : ScalarConstants) {Nw D : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) (M : ℕ)
    (out : ℕ × ℕ → ℕ) (Q : ℕ) (Cz Cd Cout Θ Cf cE : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (letters : Fin Nw → CycleLetter ι h D)
    (η S ηg t₀ Sw ϖ a b Dq : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg)
    (J₀ : ℕ → ℝ≥0∞) (Amp : ℕ × ℕ → ℝ≥0∞) (θ : Vec 2) : Prop :=
  ∃ (I : Type u) (_ : Fintype I) (st : I → ℕ) (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (Sr : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2) (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (N₀ : ℂ) (Γ : ℝ → ℝ) (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (ζ : ℝ) (εs εf Dd Dp : ℕ → ℝ),
    (∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (Sr i t) (F i t))) ∧
    CellWeakHilbertCurve a b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (qs t) 0 0) ∧
    N₀ ≠ 0 ∧ (∀ r, 0 < Γ r) ∧
    (∀ r s, a ≤ r → r ≤ s → s ≤ b → Γ s ≤ Real.exp (Real.pi ^ 2 / 16 * (s - r)) * Γ r) ∧
    (∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ)) ∧
    (∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ) ∧
    (∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ) ∧
    0 ≤ ζ ∧ ζ ≤ 1 ∧ ζ ^ 2 * (b - a) ≤ Cz * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ 2 ∧
    Monotone εs ∧ Monotone εf ∧ (∀ k, 0 ≤ εs k) ∧ (∀ k, 0 ≤ εf k) ∧
    Monotone Dd ∧ Monotone Dp ∧ (∀ k, 0 ≤ Dd k) ∧ (∀ k, 0 ≤ Dp k) ∧ (∀ k, ζ * Dp k ≤ Dd k) ∧
    (∀ k < M, slowStage st k W q N₀ a 0 ≤ Dd k) ∧
    (∀ k < M, Cf * fastStage st k W Adm ν Γ a 0 ≤ Dp k) ∧
    (∀ r ∈ Set.Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ' : I → ℂ, ∃ φ' : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ' i')) ∧
      (∀ k' < k, stageNorm st k' κ' ≤ Θ * ζ ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ' i') ^ 2) ≤
        Θ * ζ * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (Sr i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ' i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ' i'))‖ ≤
        ‖N₀‖ * εs k * stageNorm st k β) ∧
    (∀ t ∈ Set.Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k, Adm k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ν k a (Ψv i a) ^ 2) ≤
          Cf * Real.exp (-(Real.pi ^ 2 / 8) * t) ∧
        ∀ r ∈ Set.Icc a (a + t), ∃ κ' : I → ℂ, ∃ φ' : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ' i')) ∧
          (∀ k' < k, stageNorm st k' κ' ≤
            Θ * ζ * Cf * Real.exp (-(Real.pi ^ 2 / 8) * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ' i') ^ 2) ≤
            Θ * Cf * Real.exp (-(Real.pi ^ 2 / 8) * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (Sr i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ' i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ' i'))‖ ≤
            εf k / Γ (a + t)) ∧
    ∀ β ∈ momentIndices m,
      ENNReal.ofReal (Dd (out β)) ≤
        ENNReal.ofReal Cd * J₀ (β.1 + β.2 + ∑ i, Ks i) ∧
      ENNReal.ofReal (Dp (out β)) ≤
        ENNReal.ofReal Cd * J₀ (β.1 + β.2 + ∑ i, Ks i) ∧
      ENNReal.ofReal ((εs (out β) + εf (out β)) * (b - a)) ≤
        ENNReal.ofReal (Cd * peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
          Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq))) *
          J₀ (β.1 + β.2 + ∑ i, Ks i) ∧
      Amp β ≤
        ENNReal.ofReal (Real.exp (blockGauge pkg.actual.lam η a b θ).re * Cout *
          wordTheta ηg letters * (slowStage st (out β) W q N₀ a (b - a) +
            fastStage st (out β) W Adm ν Γ a (b - a) +
              (εs (out β) + εf (out β)) * (b - a)))

/-- `WordFibreFactsStatement` is, definitionally, `WordFibreFactsAt` after its binders. -/
theorem wordFibreFactsStatement_iff : WordFibreFactsStatement.{u, v} ↔
    ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
    ∃ (M : ℕ) (out : ℕ × ℕ → ℕ) (Q : ℕ), (∀ β ∈ momentIndices m, out β < M) ∧
    ∀ (CH ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
    ∃ (Cz Cd Cout Θ Cf cE : ℝ), 0 ≤ Cz ∧ 0 ≤ Cd ∧ 0 ≤ Cout ∧ 0 ≤ Θ ∧ 0 ≤ Cf ∧ 0 < cE ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
      (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
    ∀ (η S ηg t₀ Sw ϖ a b Dq : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
      (g : ℝ) (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg),
      IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b →
      t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw → b - a ≤ CH * S →
      0 ≤ Dq → Set.Ioc (b - Dq) b ⊆ reg.quiet →
      wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
    ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
    ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
      (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
      (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
      (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w →
    ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ →
      WordFibreFactsAt K m Ks M out Q Cz Cd Cout Θ Cf cE letters η S ηg t₀ Sw ϖ a b Dq G v reg
        pkg (fun n => datumJets π ϖ n (fun x => planeValue (f x)) θ)
        (fun β => momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ) θ :=
  Iff.rfl

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: the Taylor expansion and clause 2 -/

universe u v

/-- The product of the coordinates of a word is the monomial of its letter counts. -/
theorem prod_word_coord {s : ℕ} (ω : DerivativeWord2 s) (y : Vec 2) :
    ∏ i, y (ω i) = momentWeight (wordCount ω) y := by
  classical
  unfold momentWeight wordCount
  have h0 : ∏ i ∈ Finset.univ.filter (fun i => ω i = 0), y (ω i) =
      y 0 ^ (Finset.univ.filter fun i => ω i = 0).card := by
    rw [Finset.prod_congr rfl (g := fun _ => y 0) (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]), Finset.prod_const]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => ¬ ω i = 0), y (ω i) =
      y 1 ^ (Finset.univ.filter fun i => ω i = 1).card := by
    have hf : (Finset.univ.filter fun i => ¬ ω i = 0) = Finset.univ.filter fun i => ω i = 1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        omega
      · intro hi
        omega
    rw [hf, Finset.prod_congr rfl (g := fun _ => y 1) (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]), Finset.prod_const]
  rw [← h0, ← h1, Finset.prod_filter_mul_prod_filter_not]

theorem taylorWordExpansion : TaylorWordExpansion := by
  intro f X₀ s δ y
  have hy : δ • y = ∑ j : Fin 2, (δ * y j) • basisVec j := by
    ext i
    fin_cases i <;> simp
  have hfun : (fun _ : Fin s => δ • y) = fun _ => ∑ j ∈ Finset.univ, (δ * y j) • basisVec j := by
    funext _
    exact hy
  rw [hfun, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ s f X₀)
    (fun i => δ * y (ω i)) (fun i => basisVec (ω i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    prod_word_coord, smul_eq_mul, mul_assoc]

/-- **Clause 2** (level `0`): the previous flux is `0`. -/
theorem letterBlochClause2 {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) :
    LetterBlochClause2 F := by
  intro θ r x e β₀ k ψ
  unfold b1wFluxPair
  simp [wordChainPreviousFlux_initial, planeBlochC]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: weak integration by parts against bounded tests

A weak partial derivative of an integrable `u` with integrable derivative `gi` pairs with every
bounded `C¹` test of bounded derivative (not only compactly supported ones):
`∫ u ∂_k ψ = -∫ gi ψ`. Proof: cut off by `χ(y/R)`, use the compact `C¹` identity
(`hasWeakPartialDerivOn_test_contDiff_one`), and let `R → ∞` by dominated convergence; the
cutoff derivative is `O(1/R)`. -/

/-- The standard cutoff bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def letterCutoffBump : ContDiffBump (0 : Vec 2) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

/-- The cutoff at scale `n + 1`. -/
def letterCutoff (n : ℕ) (y : Vec 2) : ℝ := letterCutoffBump (((n : ℝ) + 1)⁻¹ • y)

theorem letterCutoff_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (letterCutoff n) :=
  letterCutoffBump.contDiff.comp (contDiff_id.const_smul (((n : ℝ) + 1)⁻¹))

theorem letterCutoff_compact (n : ℕ) : HasCompactSupport (letterCutoff n) :=
  letterCutoffBump.hasCompactSupport.comp_smul (inv_ne_zero (by positivity : ((n : ℝ) + 1) ≠ 0))

theorem letterCutoff_nonneg (n : ℕ) (y : Vec 2) : 0 ≤ letterCutoff n y :=
  letterCutoffBump.nonneg

theorem letterCutoff_le_one (n : ℕ) (y : Vec 2) : letterCutoff n y ≤ 1 :=
  letterCutoffBump.le_one

theorem letterCutoff_eventually_one (y : Vec 2) : ∀ᶠ n : ℕ in atTop, letterCutoff n y = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply letterCutoffBump.one_of_mem_closedBall
  show _ ∈ Metric.closedBall (0 : Vec 2) 1
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  show ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
  have : ‖y‖ ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- A uniform bound for the directional derivative of the cutoff, of size `B / (n + 1)`. -/
theorem letterCutoff_deriv_bound (k : Fin 2) : ∃ B : ℝ, ∀ (n : ℕ) (y : Vec 2),
    |fderiv ℝ (letterCutoff n) y (basisVec k)| ≤ B / ((n : ℝ) + 1) := by
  have hc : Continuous fun z => fderiv ℝ letterCutoffBump z (basisVec k) :=
    ((letterCutoffBump.contDiff (n := 1)).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport fun z => fderiv ℝ letterCutoffBump z (basisVec k) :=
    letterCutoffBump.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec k)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨B, fun n y => ?_⟩
  have hd : fderiv ℝ (letterCutoff n) y (basisVec k) =
      ((n : ℝ) + 1)⁻¹ * fderiv ℝ letterCutoffBump (((n : ℝ) + 1)⁻¹ • y) (basisVec k) := by
    have h := ((letterCutoffBump.contDiff (n := 1)).differentiable (by simp) (((n : ℝ) + 1)⁻¹ • y)
      ).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul (((n : ℝ) + 1)⁻¹))
    show fderiv ℝ (fun y => letterCutoffBump (((n : ℝ) + 1)⁻¹ • y)) y (basisVec k) = _
    have h' : HasFDerivAt (fun y => letterCutoffBump (((n : ℝ) + 1)⁻¹ • y)) _ y := h
    rw [h'.fderiv]
    simp
  rw [hd, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using hB _) (by positivity)

theorem letterCutoff_deriv_tendsto (k : Fin 2) (y : Vec 2) :
    Tendsto (fun n : ℕ => fderiv ℝ (letterCutoff n) y (basisVec k)) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := letterCutoff_deriv_bound k
  have h1 : Tendsto (fun n : ℕ => B * (1 / ((n : ℝ) + 1))) atTop (𝓝 (B * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
  rw [mul_zero] at h1
  refine squeeze_zero_norm (fun n => ?_) h1
  rw [Real.norm_eq_abs]
  calc _ ≤ B / ((n : ℝ) + 1) := hB n y
    _ = _ := by ring

/-- **Weak integration by parts against a bounded `C¹` test** (real form). -/
theorem weak_ibp_bdd_real {u gi : Vec 2 → ℝ} {k : Fin 2}
    (hw : HasWeakPartialDerivOn univ k u gi) (hu : Integrable u) (hgi : Integrable gi)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) {M : ℝ} (hb : ∀ y, |ψ y| ≤ M)
    (hd : ∀ y, |fderiv ℝ ψ y (basisVec k)| ≤ M) :
    ∫ y, u y * fderiv ℝ ψ y (basisVec k) = -∫ y, gi y * ψ y := by
  obtain ⟨B, hB⟩ := letterCutoff_deriv_bound k
  have hdψ : Continuous (fun y => fderiv ℝ ψ y (basisVec k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcd : ∀ n, Continuous (fun y => fderiv ℝ (letterCutoff n) y (basisVec k)) := fun n =>
    (((letterCutoff_contDiff n).of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).continuous_fderiv
      (by simp)).clm_apply continuous_const
  have hcc : ∀ n, Continuous (letterCutoff n) := fun n => (letterCutoff_contDiff n).continuous
  have key : ∀ n, ∫ y, u y * (letterCutoff n y * fderiv ℝ ψ y (basisVec k) +
      ψ y * fderiv ℝ (letterCutoff n) y (basisVec k)) =
      -∫ y, gi y * (letterCutoff n y * ψ y) := by
    intro n
    have hc1 : ContDiff ℝ 1 (letterCutoff n) := (letterCutoff_contDiff n).of_le (by simp)
    have hg : ContDiff ℝ 1 (fun y => letterCutoff n y * ψ y) := hc1.mul hψ
    have hcs : HasCompactSupport (fun y => letterCutoff n y * ψ y) :=
      (letterCutoff_compact n).mul_right
    rw [← hasWeakPartialDerivOn_test_contDiff_one hw hu.locallyIntegrable hgi.locallyIntegrable
      hg hcs]
    congr 1
    ext y
    rw [fderiv_fun_mul (hc1.differentiable (by simp)).differentiableAt
      (hψ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hT1 : Tendsto (fun n : ℕ => ∫ y, u y * (letterCutoff n y * fderiv ℝ ψ y (basisVec k) +
      ψ y * fderiv ℝ (letterCutoff n) y (basisVec k))) atTop
      (𝓝 (∫ y, u y * fderiv ℝ ψ y (basisVec k))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖u y‖ * (M + M * |B|)) ?_ ?_ ?_ ?_
    · intro n
      exact hu.1.mul ((((hcc n).mul hdψ).add (hψ.continuous.mul (hcd n))).aestronglyMeasurable)
    · exact hu.norm.mul_const _
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      calc _ ≤ |letterCutoff n y * fderiv ℝ ψ y (basisVec k)| +
            |ψ y * fderiv ℝ (letterCutoff n) y (basisVec k)| := abs_add_le _ _
        _ ≤ M + M * |B| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (letterCutoff_nonneg n y)]
          have h1 : letterCutoff n y * |fderiv ℝ ψ y (basisVec k)| ≤ M :=
            (mul_le_of_le_one_left (abs_nonneg _) (letterCutoff_le_one n y)).trans (hd y)
          have h2 : |ψ y| * |fderiv ℝ (letterCutoff n) y (basisVec k)| ≤ M * |B| := by
            refine mul_le_mul (hb y) ?_ (abs_nonneg _) hM
            refine (hB n y).trans ?_
            calc B / ((n : ℝ) + 1) ≤ |B / ((n : ℝ) + 1)| := le_abs_self _
              _ = |B| / ((n : ℝ) + 1) := by
                rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
              _ ≤ |B| := div_le_self (abs_nonneg _) (by
                  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                  linarith)
          linarith
    · refine Filter.Eventually.of_forall fun y => ?_
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun n : ℕ => letterCutoff n y) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((letterCutoff_eventually_one y).mono fun n hn => hn.symm)
      have h2 := (letterCutoff_deriv_tendsto k y).const_mul (ψ y)
      have := (h1.mul_const (fderiv ℝ ψ y (basisVec k))).add h2
      simpa using this
  have hT3 : Tendsto (fun n : ℕ => ∫ y, gi y * (letterCutoff n y * ψ y)) atTop
      (𝓝 (∫ y, gi y * ψ y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖gi y‖ * M) ?_ ?_ ?_ ?_
    · intro n
      exact hgi.1.mul (((hcc n).mul hψ.continuous).aestronglyMeasurable)
    · exact hgi.norm.mul_const _
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (letterCutoff_nonneg n y)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (letterCutoff_le_one n y)).trans (hb y)
    · refine Filter.Eventually.of_forall fun y => ?_
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun n : ℕ => letterCutoff n y) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((letterCutoff_eventually_one y).mono fun n hn => hn.symm)
      simpa using h1.mul_const (ψ y)
  have hT3' := hT3.neg
  simp only [← key] at hT3'
  exact tendsto_nhds_unique hT1 hT3'

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: the pointwise flux expansion -/

universe u v

/-- The pairing of a list of constituents (slow evaluation) with a vector `e`. -/
theorem inner_slowEval_apply {Hu Hv : Type*} [NormedAddCommGroup Hu] [InnerProductSpace ℝ Hu]
    [CompleteSpace Hu] [NormedAddCommGroup Hv] [InnerProductSpace ℝ Hv] [CompleteSpace Hv]
    {d : ℕ} (ev : (Vec 2 → ℝ) → Vec 2 → ℝ) (L : List (Constituent d Hu Hv)) (t : ℝ) (z : Vec 2)
    (g : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => Hu)) (e : Hv) (k : Fin 2) :
    inner ℝ e ((slowEvalCoefficient ev L t z g) k) =
      (L.map fun γ => ∑ α : DerivativeWord2 (d - 1),
        ev (fun X => γ.coeff α t X z k) z * inner ℝ (ContinuousLinearMap.adjoint γ.map e) (g α)).sum := by
  induction L with
  | nil => simp [slowEvalCoefficient]
  | cons γ L ih =>
    have hsplit : slowEvalCoefficient ev (γ :: L) t z g =
        slowEvalCoefficient ev [γ] t z g + slowEvalCoefficient ev L t z g := by
      simp [slowEvalCoefficient]
    rw [hsplit, PiLp.add_apply, inner_add_right, ih, List.map_cons, List.sum_cons]
    congr 1
    simp [slowEvalCoefficient, inner_sum, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
  {K : ScalarConstants} {g₁ : ℝ}

theorem letterFluxPointwise (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) :
    LetterFluxPointwise F := by
  classical
  intro j x e k r y
  unfold wordChainPreviousFlux
  simp only [WithLp.ofLp_sum, Finset.sum_apply, inner_sum]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j.castSucc]
  · refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← Finset.sum_coe_sort (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
      (j.succ, x) (j.castSucc, x'))]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd := Finset.mem_filter.mp d.2
    have hs : (j.succ : Fin (Nw + 1)).val = (j.castSucc : Fin (Nw + 1)).val + 1 := by simp
    rw [dite_eq_left_of_eq_true (eq_true hd.1)]
    have hs' : (j.succ : Fin (Nw + 1)).val = ((j.castSucc, x') : Fin (Nw + 1) × ι).1.val + 1 := by
      simp
    rw [dite_eq_left_of_eq_true (eq_true hs')]
    refine (inner_slowEval_apply _ _ r y _ e k).trans ?_
    congr 1
    refine List.map_congr_left fun γ _ => ?_
    refine Finset.sum_congr rfl fun α _ => ?_
    have hle : (d : ℕ) - 1 ≤ F.κ j.castSucc x' + 1 := by
      have := hd.2
      simp only at this
      omega
    have hjet : (wordChainJetArray F.κ (fun q => F.w q.1 q.2 r) (j.succ, x) (j.castSucc, x') d y) α =
        planeJetOrder (F.w j.castSucc x' r) ((d : ℕ) - 1) α y := by
      simp [wordChainJetArray, planeJetOrder, hle]
    rw [hjet]
    simp only [taylorSlow]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [taylorWordExpansion, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  · intro l _ hl
    refine Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero fun d _ => ?_
    have h' : ¬ (j.val = l.val) := by
      intro hh
      apply hl
      apply Fin.ext
      simpa using hh.symm
    simp [h']
  · intro hh
    exact absurd (Finset.mem_univ _) hh

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # I with measurable forcing from the literal I (adapter)

`CellWeakIdentity` is iterated: it asks slice integrability for a.e. time, integrability of the
slice integrals, and their identity. So changing the source and flux slice by slice, for a.e.
time, keeps it (`cellWeakIdentity_congr_forcing`), and with it `IsCellSolution`
(`isCellSolution_congr_forcing`).

`amplitudeIdFibresMeas_of_literal`: the literal I and the `L²` time carriers of its forcing give
the measurable fibre clause. The carriers have jointly measurable versions in `L²` of the product
(`exists_cellCurve_version`, `cellCurve_version_memLp`), equal slice by slice to the literal
forcing for a.e. time, and the literal cell solution solves the problem with these. -/

universe u v

/-- The weak identity only sees the forcing slice by slice, for a.e. time. -/
theorem cellWeakIdentity_congr_forcing {C : CellCoefficients} {s t : ℝ}
    {u₀ u₁ ψ : Vec 2 → ℂ} {dψ : Fin 2 → Vec 2 → ℂ} {u : ℝ → Vec 2 → ℂ}
    {du : ℝ → Fin 2 → Vec 2 → ℂ} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (h : CellWeakIdentity C s t u₀ u₁ ψ dψ u du src F)
    (hc : ∀ᵐ τ ∂volume.restrict (Ioc s t),
      src' τ =ᵐ[volume.restrict AVenhance.unitCube] src τ ∧
        F' τ =ᵐ[volume.restrict AVenhance.unitCube] F τ) :
    CellWeakIdentity C s t u₀ u₁ ψ dψ u du src' F' := by
  unfold CellWeakIdentity at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  set rhs : ℝ → Vec 2 → ℂ := fun τ x =>
    -(∑ j : Fin 2, ∑ k : Fin 2, (C.G τ x j k : ℂ) *
        (du τ j x + Complex.I * C.θ j * u τ x) * (dψ k x - Complex.I * C.θ k * ψ x))
      - ∑ k : Fin 2, (C.v τ x k : ℂ) * (du τ k x + Complex.I * C.θ k * u τ x) * ψ x
      + C.κ τ * u τ x * ψ x + src τ x * ψ x
      - ∑ k : Fin 2, F τ x k * (dψ k x - Complex.I * C.θ k * ψ x) with hrhs
  set rhs' : ℝ → Vec 2 → ℂ := fun τ x =>
    -(∑ j : Fin 2, ∑ k : Fin 2, (C.G τ x j k : ℂ) *
        (du τ j x + Complex.I * C.θ j * u τ x) * (dψ k x - Complex.I * C.θ k * ψ x))
      - ∑ k : Fin 2, (C.v τ x k : ℂ) * (du τ k x + Complex.I * C.θ k * u τ x) * ψ x
      + C.κ τ * u τ x * ψ x + src' τ x * ψ x
      - ∑ k : Fin 2, F' τ x k * (dψ k x - Complex.I * C.θ k * ψ x) with hrhs'
  have hslice : ∀ᵐ τ ∂volume.restrict (Ioc s t),
      rhs' τ =ᵐ[volume.restrict AVenhance.unitCube] rhs τ := by
    filter_upwards [hc] with τ hτ
    filter_upwards [hτ.1, hτ.2] with x hx1 hx2
    simp only [hrhs, hrhs', hx1, hx2]
  have hint : (fun τ => ∫ x, rhs' τ x ∂volume.restrict AVenhance.unitCube) =ᵐ[volume.restrict
      (Ioc s t)] fun τ => ∫ x, rhs τ x ∂volume.restrict AVenhance.unitCube := by
    filter_upwards [hslice] with τ hτ
    exact integral_congr_ae hτ
  refine ⟨h1, h2, ?_, h4.congr_fun_ae hint.symm, ?_⟩
  · filter_upwards [h3, hslice] with τ hτ hτ'
    exact hτ.congr hτ'.symm
  · rw [h5]
    exact (integral_congr_ae hint).symm

/-- **A cell solution solves the problem with any forcing equal slice by slice, a.e. in time.** -/
theorem isCellSolution_congr_forcing {a b : ℝ} {C : CellCoefficients}
    {src src' : ℝ → Vec 2 → ℂ} {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (h : IsCellSolution (Icc a b) C src F D)
    (hc : ∀ᵐ τ ∂volume.restrict (Icc a b),
      src' τ =ᵐ[volume.restrict AVenhance.unitCube] src τ ∧
        F' τ =ᵐ[volume.restrict AVenhance.unitCube] F τ) :
    IsCellSolution (Icc a b) C src' F' D := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun s hs t ht hst ψ => ?_⟩
  refine cellWeakIdentity_congr_forcing (h7 s hs t ht hst ψ) ?_
  have hsub : Ioc s t ⊆ Icc a b := fun τ hτ => ⟨hs.1.trans hτ.1.le, hτ.2.trans ht.2⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub hc

/-- **The measurable fibre clause of the amplitude identification from its literal statement and
the time carriers.** -/
theorem amplitudeIdFibresMeas_of_literal (hI : AmplitudeIdentificationStatement.{u, v})
    (hC : AmplitudeIdForcingCurvesStatement.{u, v}) : AmplitudeIdFibresMeasStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hIK⟩ := hI K
  refine ⟨g₁, hg₁, ?_⟩
  intro ι _ h _ _ _ _ _ _ D Nw F j x e θ β
  obtain ⟨-, hfib, -⟩ := hIK F.H F.J F.π F.letters F.η F.S F.ηg F.t₀ F.Sw F.ϖ F.a F.b F.G F.v
    F.g F.reg F.pkg F.piece F.left F.ordered F.right F.X₀ F.κ F.slots F.cap F.f F.u F.w
    (planeDatum_support_of_compact F.φ (fun x => (F.compact x).2) _ F.datum) F.solution
  obtain ⟨Dθ, hsol, hval⟩ := hfib j x e θ β
  obtain ⟨⟨R, hR, hRr⟩, hQ⟩ := hC K g₁ F j x e θ β
  choose Q hQm hQr using hQ
  obtain ⟨Gs, hGs, hGss⟩ := exists_cellCurve_version R hR.aestronglyMeasurable
  have hk := fun k => exists_cellCurve_version (Q k) (hQm k).aestronglyMeasurable
  choose Gk hGk hGks using hk
  refine ⟨Dθ, fun r z => Gs (r, z), fun r z => WithLp.toLp 2 fun k => Gk k (r, z), ?_, ?_, ?_,
    ?_, hval⟩
  · exact cellCurve_version_memLp R hR Gs hGs hGss
  · intro k
    exact cellCurve_version_memLp (Q k) (hQm k) (Gk k) (hGk k) (hGks k)
  · filter_upwards [hGss, hRr, ae_all_iff.2 hGks, ae_all_iff.2 hQr] with r h1 h2 h3 h4
    refine ⟨h1.trans h2, ?_⟩
    filter_upwards [ae_all_iff.2 h3, ae_all_iff.2 h4] with z hz3 hz4
    ext k
    exact (hz3 k).trans (hz4 k)
  · refine isCellSolution_congr_forcing hsol ?_
    filter_upwards [hGss, hRr, ae_all_iff.2 hGks, ae_all_iff.2 hQr] with r h1 h2 h3 h4
    refine ⟨h1.trans h2, ?_⟩
    filter_upwards [ae_all_iff.2 h3, ae_all_iff.2 h4] with z hz3 hz4
    ext k
    exact (hz3 k).trans (hz4 k)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # Jet-to-value transfer: the twisted derivatives of the test

The twisted derivatives `D_k = ∂_k + iθ_k` commute on `C²` functions (`fibreCovDeriv_comm`,
from the symmetry of mixed partials), so a new letter can be put in front of
`fibreCovPow θ b = D₀^{b₀} D₁^{b₁}` (`fibreCovDeriv_fibreCovPow`). `fibreCovPow` keeps
periodicity and lowers the smoothness by `b₀ + b₁`. -/

/-- The iterated twisted derivatives of a periodic function are periodic. -/
theorem isZ2Periodic_fibreCovDeriv_iterate (θ : Vec 2) (k : Fin 2) :
    ∀ (p : ℕ) {φ : Vec 2 → ℂ}, AVenhance.IsZ2Periodic φ →
      AVenhance.IsZ2Periodic ((fibreCovDeriv θ k)^[p] φ)
  | 0, _, hp => hp
  | p + 1, _, hp => by
    rw [Function.iterate_succ_apply']
    exact isZ2Periodic_fibreCovDeriv (isZ2Periodic_fibreCovDeriv_iterate θ k p hp) θ k

/-- `p` twisted derivatives of a `C^{j+p}` function are `C^j`. -/
theorem contDiff_fibreCovDeriv_iterate (θ : Vec 2) (k : Fin 2) (j : ℕ) :
    ∀ (p : ℕ) {φ : Vec 2 → ℂ}, ContDiff ℝ (j + p : ℕ) φ →
      ContDiff ℝ j ((fibreCovDeriv θ k)^[p] φ)
  | 0, _, hφ => by simpa using hφ
  | p + 1, φ, hφ => by
    rw [Function.iterate_succ_apply']
    have h := contDiff_fibreCovDeriv_iterate θ k (j + 1) p (φ := φ)
      (by rw [show j + 1 + p = j + (p + 1) by omega]; exact hφ)
    exact contDiff_fibreCovDeriv h θ k

theorem isZ2Periodic_fibreCovPow (θ : Vec 2) (b : ℕ × ℕ) {φ : Vec 2 → ℂ}
    (hp : AVenhance.IsZ2Periodic φ) : AVenhance.IsZ2Periodic (fibreCovPow θ b φ) :=
  isZ2Periodic_fibreCovDeriv_iterate θ 0 b.1 (isZ2Periodic_fibreCovDeriv_iterate θ 1 b.2 hp)

theorem contDiff_fibreCovPow (θ : Vec 2) (b : ℕ × ℕ) (j : ℕ) {φ : Vec 2 → ℂ}
    (hφ : ContDiff ℝ (j + b.1 + b.2 : ℕ) φ) : ContDiff ℝ j (fibreCovPow θ b φ) :=
  contDiff_fibreCovDeriv_iterate θ 0 j b.1
    (contDiff_fibreCovDeriv_iterate θ 1 (j + b.1) b.2 hφ)

/-- **The twisted derivatives commute** on `C²` functions. -/
theorem fibreCovDeriv_comm (θ : Vec 2) {g : Vec 2 → ℂ} (hg : ContDiff ℝ (2 : ℕ) g) :
    fibreCovDeriv θ 1 (fibreCovDeriv θ 0 g) = fibreCovDeriv θ 0 (fibreCovDeriv θ 1 g) := by
  have hsym : ∀ x, fderiv ℝ (fun z => fderiv ℝ g z (basisVec 0)) x (basisVec 1) =
      fderiv ℝ (fun z => fderiv ℝ g z (basisVec 1)) x (basisVec 0) := by
    intro x
    have h := CycleComparison.Reconstruction.orderedDerivative_comp_perm_of_contDiff (m := 2)
      ![0, 1] (Equiv.swap 0 1) hg x
    have e1 : (![0, 1] : DerivativeWord2 2) ∘ Equiv.swap 0 1 = ![1, 0] := by
      ext i
      fin_cases i <;> rfl
    rw [e1] at h
    simpa [orderedDerivative] using h.symm
  have hd : ∀ k : Fin 2, Differentiable ℝ (fun z => fderiv ℝ g z (basisVec k)) := fun k =>
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hD : ∀ k : Fin 2, fibreCovDeriv θ k g =
      fun z => fderiv ℝ g z (basisVec k) + Complex.I * (θ k : ℂ) * g z := fun k => rfl
  funext x
  rw [hD 0, hD 1]
  simp only [fibreCovDeriv]
  rw [fderiv_fun_add (hd 0 x) ((hg1.const_mul _) x), fderiv_fun_add (hd 1 x) ((hg1.const_mul _) x),
    fderiv_const_mul (hg1 x), fderiv_const_mul (hg1 x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hsym x]
  ring

/-- `D_1` passes through `p` factors `D_0`. -/
theorem fibreCovDeriv_one_iterate_zero (θ : Vec 2) :
    ∀ (p : ℕ) {ψ : Vec 2 → ℂ}, ContDiff ℝ (p + 1 : ℕ) ψ →
      fibreCovDeriv θ 1 ((fibreCovDeriv θ 0)^[p] ψ) =
        (fibreCovDeriv θ 0)^[p] (fibreCovDeriv θ 1 ψ)
  | 0, _, _ => rfl
  | p + 1, ψ, hψ => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      fibreCovDeriv_comm θ (contDiff_fibreCovDeriv_iterate θ 0 2 p
        (by rw [show 2 + p = p + 1 + 1 by omega]; exact hψ)),
      fibreCovDeriv_one_iterate_zero θ p (hψ.of_le (by norm_cast; omega))]

/-- A new letter in front of `fibreCovPow`. -/
theorem fibreCovDeriv_fibreCovPow (θ : Vec 2) (a : Fin 2) (b : ℕ × ℕ) {φ : Vec 2 → ℂ}
    (hφ : ContDiff ℝ (b.1 + b.2 + 1 : ℕ) φ) :
    fibreCovDeriv θ a (fibreCovPow θ b φ) =
      fibreCovPow θ (if a = 0 then (b.1 + 1, b.2) else (b.1, b.2 + 1)) φ := by
  fin_cases a
  · simp only [fibreCovPow, Fin.zero_eta, ↓reduceIte]
    rw [Function.iterate_succ_apply']
  · simp only [fibreCovPow, Fin.mk_one, one_ne_zero, ↓reduceIte]
    rw [fibreCovDeriv_one_iterate_zero θ b.1 (contDiff_fibreCovDeriv_iterate θ 1 (b.1 + 1) b.2
      (by rw [show b.1 + 1 + b.2 = b.1 + b.2 + 1 by omega]; exact hφ)),
      ← Function.iterate_succ_apply' (fibreCovDeriv θ 1)]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The word stage bound from the word fibre facts

The stage functions of the word stage bound (`WordStageStatement`) are the gauged slow coordinates
and fast seminorms of the abstract fibre word (`slowStage`, `fastStage`), the errors are
`E_k = (ε_{s,k} + ε_{f,k})(b - a)`, the letter constant is `Θ max(1, C_f)` and the fast rate
`π²/8 - π²/16 = π²/16`. The triangular inequalities are `afw_slow` and `afw_fast`
(`wordStage_of_fibreFacts`). -/

universe u v

/-- **`WordStageStatement` from `WordFibreFactsStatement`.** -/
theorem wordStage_of_fibreFacts (hW : WordFibreFactsStatement.{u, v}) :
    WordStageStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hWK⟩ := hW K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D H m d Ks pos
  obtain ⟨M, out, Q, hout, hWo⟩ := hWK Nw D H m d Ks pos
  refine ⟨M, out, Q, hout, ?_⟩
  intro CH ρ hρ hρlo
  obtain ⟨Cz, Cd, Cout, Θ, Cf, cE, hCz, hCd, hCout, hΘ, hCf, hcE, hWc⟩ := hWo CH ρ hρ hρlo
  have hΘ' : 0 ≤ Θ * max 1 Cf := mul_nonneg hΘ (le_max_of_le_left zero_le_one)
  have hc : (0 : ℝ) < Real.pi ^ 2 / 16 := by positivity
  refine ⟨Cz, Cd, Cout, Θ * max 1 Cf, Real.pi ^ 2 / 16, cE, hCz, hCd, hCout, hΘ', hc, hcE, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB ht₀a hab
    hbS hCH hDq hq hJ X₀ κ hκ f u w hf hch θ hθ
  obtain ⟨I, _, st, C, hG, V, hv, hbv, W, Ws, Sr, F, q, qs, N₀, Γ, Adm, ν, ζ, εs, εf, Dd, Dp,
    hWcur, hqcur, hN₀, hΓ, hgauge, hAdm, hν, hνL, hζ0, hζ1, hζτ, hεsm, hεfm, hεs0, hεf0, hDdm,
    hDpm, hDd0, hDp0, hζDp, hD0, hDp0', H3s, H4, hout'⟩ :=
      hWc J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB ht₀a hab hbS hCH hDq hq hJ
        X₀ κ hκ f u w hf hch θ hθ
  have hτ : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have hslow := afw_slow C hG V hv hbv st M W Ws Sr F hWcur q qs hqcur N₀ hN₀ Γ
    (fun r => (hΓ r).le) Adm ν hAdm hν hνL hΘ hζ0 hεs0 H3s
  have hfast := afw_fast C hG V hv hbv st M W Ws Sr F hWcur q N₀ hN₀ Γ hΓ (Real.pi ^ 2 / 16)
    (Real.pi ^ 2 / 8) hgauge Adm ν hAdm hν hνL hΘ hζ0 hεf0 hCf H4
  have hA0 : ∀ k r, 0 ≤ slowStage st k W q N₀ a r := fun k r =>
    div_nonneg (stageNorm_nonneg _ _ _) (norm_nonneg _)
  have hB0 : ∀ k r, 0 ≤ fastStage st k W Adm ν Γ a r := fun k r =>
    mul_nonneg (hΓ _).le (fastRaw_nonneg _ _ _ _ _)
  have hrate : Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 = Real.pi ^ 2 / 16 := by ring
  refine ⟨fun k => slowStage st k W q N₀ a, fun k => fastStage st k W Adm ν Γ a, Dd, Dp,
    fun k => (εs k + εf k) * (b - a), ζ, hζ0, hζ1, hζτ, hDdm, hDpm,
    fun k k' hk => mul_le_mul_of_nonneg_right (add_le_add (hεsm hk) (hεfm hk)) hτ,
    hDd0, hDp0, hζDp, fun k => mul_nonneg (add_nonneg (hεs0 k) (hεf0 k)) hτ, ?_, ?_, ?_⟩
  · intro k hk t ht a' b' hmaj
    have h := hslow k hk t ht a' b' hmaj
    have hsum0 : 0 ≤ ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) :=
      Finset.sum_nonneg fun k' hk' => by
        obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
        exact (majorant_integral_nonneg (cf := 0) (σ := 0) ht.1 hζ0
          (fun r hr => (hA0 k' r).trans (hle r hr).1)
          (fun r hr => (hB0 k' r).trans (hle r hr).2)).1
    have hΘle : Θ ≤ Θ * max 1 Cf := le_mul_of_one_le_right hΘ (le_max_left _ _)
    have hεt : εs k * t ≤ (εs k + εf k) * (b - a) :=
      mul_le_mul (by linarith [hεf0 k]) ht.2 ht.1 (by linarith [hεs0 k, hεf0 k])
    calc slowStage st k W q N₀ a t
        ≤ slowStage st k W q N₀ a 0 + εs k * t + Θ * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) := h
      _ ≤ Dd k + (εs k + εf k) * (b - a) + Θ * max 1 Cf * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) :=
          add_le_add (add_le_add (hD0 k hk) hεt) (mul_le_mul_of_nonneg_right hΘle hsum0)
  · intro k hk t ht a' b' hmaj
    have h := hfast k hk t ht a' b' hmaj
    rw [hrate] at h
    have hsum0 : 0 ≤ ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t,
        Real.exp (-(Real.pi ^ 2 / 16) * (t - r)) * (ζ * a' k' r + b' k' r) :=
      Finset.sum_nonneg fun k' hk' => by
        obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
        have := (majorant_integral_nonneg (cf := Real.pi ^ 2 / 16) (σ := 0) ht.1 hζ0
          (fun r hr => (hA0 k' r).trans (hle r hr).1)
          (fun r hr => (hB0 k' r).trans (hle r hr).2)).2
        simpa using this
    have hΘle : Θ * Cf ≤ Θ * max 1 Cf := mul_le_mul_of_nonneg_left (le_max_right _ _) hΘ
    have hεt : εf k * t ≤ (εs k + εf k) * (b - a) :=
      mul_le_mul (by linarith [hεs0 k]) ht.2 ht.1 (by linarith [hεs0 k, hεf0 k])
    have hinit : Cf * Real.exp (-(Real.pi ^ 2 / 16) * t) * fastStage st k W Adm ν Γ a 0 ≤
        Real.exp (-(Real.pi ^ 2 / 16) * t) * Dp k := by
      have := mul_le_mul_of_nonneg_left (hDp0' k hk) (Real.exp_pos (-(Real.pi ^ 2 / 16) * t)).le
      calc Cf * Real.exp (-(Real.pi ^ 2 / 16) * t) * fastStage st k W Adm ν Γ a 0
          = Real.exp (-(Real.pi ^ 2 / 16) * t) * (Cf * fastStage st k W Adm ν Γ a 0) := by ring
        _ ≤ _ := this
    calc fastStage st k W Adm ν Γ a t
        ≤ Cf * Real.exp (-(Real.pi ^ 2 / 16) * t) * fastStage st k W Adm ν Γ a 0 + εf k * t +
            Θ * Cf * ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t,
              Real.exp (-(Real.pi ^ 2 / 16) * (t - r)) * (ζ * a' k' r + b' k' r) := h
      _ ≤ Real.exp (-(Real.pi ^ 2 / 16) * t) * Dp k + (εs k + εf k) * (b - a) +
            Θ * max 1 Cf * ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t,
              Real.exp (-(Real.pi ^ 2 / 16) * (t - r)) * (ζ * a' k' r + b' k' r) :=
          add_le_add (add_le_add hinit hεt) (mul_le_mul_of_nonneg_right hΘle hsum0)
  · exact hout'

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # Jet-to-value transfer

Induction on the word, peeling its first letter `a` (the innermost derivative):
`∂^{a·w'} h = ∂^{w'}(∂_a h)`. The induction hypothesis for `∂_a h` gives the transfer sum of `∂_a h`
against the tests `D^{c'-a'} φ`; one letter in the cell moves `∂_a` onto the test
(`D_a D^{c'-a'} = D^{c'+e_a-a'}`, `fibreCovDeriv_fibreCovPow`) and onto the weight (`β_a - a'_a`
times the lowered moment); the coefficients recombine by `transferSum_step_zero` /
`transferSum_step_one`. The weak form is `weakJetToValue`, with one letter in the cell by
`cell_moment_weakDeriv`. -/

theorem transfer_orderedDerivative_nil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : DerivativeWord2 0) (h : Vec 2 → E) : orderedDerivative w h = h := by
  simp [orderedDerivative]

theorem transfer_orderedDerivative_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (a : Fin 2) (w : DerivativeWord2 n) (h : Vec 2 → E) :
    orderedDerivative (Fin.cons a w : DerivativeWord2 (n + 1)) h =
      orderedDerivative w (fun x => fderiv ℝ h x (basisVec a)) := by
  simp [orderedDerivative, List.ofFn_succ]

theorem wordCount_nil (w : DerivativeWord2 0) : wordCount w = (0, 0) := by
  simp [wordCount]

theorem wordCount_cons {n : ℕ} (a : Fin 2) (w : DerivativeWord2 n) :
    wordCount (Fin.cons a w : DerivativeWord2 (n + 1)) =
      if a = 0 then ((wordCount w).1 + 1, (wordCount w).2)
      else ((wordCount w).1, (wordCount w).2 + 1) := by
  simp only [wordCount, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  fin_cases a <;> simp [add_comm]

theorem wordCount_sum : ∀ {n : ℕ} (w : DerivativeWord2 n), (wordCount w).1 + (wordCount w).2 = n
  | 0, w => by simp [wordCount_nil]
  | n + 1, w => by
    obtain ⟨a, w', rfl⟩ : ∃ a w', w = (Fin.cons a w' : DerivativeWord2 (n + 1)) :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    have h := wordCount_sum w'
    rw [wordCount_cons]
    split_ifs <;> simp <;> omega

/-- The transfer integrals `∫_□ B_θ(y^{β-a} h) (D_{-θ})^{c-a} φ`. -/
def transferInt (θ : Vec 2) (c β : ℕ × ℕ) (h : Vec 2 → ℝ) (φ : Vec 2 → ℂ) (a : ℕ × ℕ) : ℂ :=
  ∫ z in AVenhance.unitCube,
    planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
      fibreCovPow (-θ) (c.1 - a.1, c.2 - a.2) φ z

/-- The integrability hypothesis of the transfer, up to order `n`. -/
def TransferIntegrable (n : ℕ) (β : ℕ × ℕ) (h : Vec 2 → ℝ) : Prop :=
  ∀ γ : ℕ × ℕ, γ ≤ β → ∀ j ≤ n, ∀ v : DerivativeWord2 j,
    Integrable (fun y => momentWeight γ y * orderedDerivative v h y)

/-- The integrability hypothesis passes from `h` to `∂_a h`, one order lower. -/
theorem TransferIntegrable.deriv {n : ℕ} {β : ℕ × ℕ} {h : Vec 2 → ℝ}
    (hint : TransferIntegrable (n + 1) β h) (a : Fin 2) :
    TransferIntegrable n β (fun x => fderiv ℝ h x (basisVec a)) := by
  intro γ hγ j hj v
  have := hint γ hγ (j + 1) (by omega) (Fin.cons a v)
  rwa [transfer_orderedDerivative_cons] at this

/-- The three integrability facts of one letter `k` at the weight `β - a`. -/
theorem TransferIntegrable.letter {n : ℕ} {β : ℕ × ℕ} {h : Vec 2 → ℝ}
    (hint : TransferIntegrable (n + 1) β h) (a : ℕ × ℕ) (k : Fin 2) :
    Integrable (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) ∧
      Integrable (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y *
        fderiv ℝ h y (basisVec k)) ∧
      Integrable (fun y => momentWeight (momentShift (β.1 - a.1, β.2 - a.2) k) y * h y) := by
  have hle : ((β.1 - a.1, β.2 - a.2) : ℕ × ℕ) ≤ β :=
    Prod.mk_le_mk.2 ⟨Nat.sub_le _ _, Nat.sub_le _ _⟩
  have hle' : momentShift (β.1 - a.1, β.2 - a.2) k ≤ β := by
    unfold momentShift
    split_ifs
    · exact Prod.mk_le_mk.2 ⟨by omega, Nat.sub_le _ _⟩
    · exact Prod.mk_le_mk.2 ⟨Nat.sub_le _ _, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · have := hint _ hle 0 (Nat.zero_le _) Fin.elim0
    rwa [transfer_orderedDerivative_nil] at this
  · have := hint _ hle 1 (by omega) (Fin.cons k Fin.elim0)
    rwa [transfer_orderedDerivative_cons, transfer_orderedDerivative_nil] at this
  · have := hint _ hle' 0 (Nat.zero_le _) Fin.elim0
    rwa [transfer_orderedDerivative_nil] at this

/-! # Transposed constituent: periodic integration by parts for twisted derivatives

One step: for `C¹` periodic `u, v`, `∫_□ u · D_{-θ,k} v = -∫_□ D_{θ,k} u · v`
(`integral_mul_fibreCovDeriv_neg`), to be iterated along `D_k^p`. -/

theorem integrableOn_unitCube_of_continuous_c {f : Vec 2 → ℂ} (hf : Continuous f) :
    IntegrableOn f AVenhance.unitCube := by
  have hK := isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  refine (hf.continuousOn.integrableOn_compact hK).mono_set ?_
  intro x hx
  exact fun i _ => ⟨(hx i trivial).1.le, (hx i trivial).2.le⟩

/-- Partial derivatives of `C¹` periodic complex functions integrate to zero over the cell. -/
theorem integral_fderiv_basis_eq_zero_c {F : Vec 2 → ℂ} (hF : ContDiff ℝ 1 F)
    (hp : AVenhance.IsZ2Periodic F) (k : Fin 2) :
    ∫ x in AVenhance.unitCube, fderiv ℝ F x (basisVec k) = 0 := by
  have hcont : Continuous fun x => fderiv ℝ F x (basisVec k) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint := integrableOn_unitCube_of_continuous_c hcont
  have hre : ContDiff ℝ 1 (fun x => (F x).re) := Complex.reCLM.contDiff.comp hF
  have him : ContDiff ℝ 1 (fun x => (F x).im) := Complex.imCLM.contDiff.comp hF
  have hrp : AVenhance.IsZ2Periodic (fun x => (F x).re) := fun n x => by simp [hp n x]
  have hip : AVenhance.IsZ2Periodic (fun x => (F x).im) := fun n x => by simp [hp n x]
  have d1 : ∀ x, fderiv ℝ (fun x => (F x).re) x (basisVec k) =
      (fderiv ℝ F x (basisVec k)).re := fun x => by
    have := (Complex.reCLM.hasFDerivAt.comp x
      ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv
    rw [show (fun x => (F x).re) = Complex.reCLM ∘ F from rfl, this]
    rfl
  have d2 : ∀ x, fderiv ℝ (fun x => (F x).im) x (basisVec k) =
      (fderiv ℝ F x (basisVec k)).im := fun x => by
    have := (Complex.imCLM.hasFDerivAt.comp x
      ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv
    rw [show (fun x => (F x).im) = Complex.imCLM ∘ F from rfl, this]
    rfl
  have z1 := AVRegularity.CoupledEnergy.Variational.periodic_partial_integral_zero _ hre hrp k
  have z2 := AVRegularity.CoupledEnergy.Variational.periodic_partial_integral_zero _ him hip k
  simp only [d1, d2] at z1 z2
  apply Complex.ext
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    simp only [Complex.zero_re]; rw [← h]; exact z1
  · have h := integral_im hint
    simp only [RCLike.im_to_complex] at h
    simp only [Complex.zero_im]; rw [← h]; exact z2

/-- One step of periodic integration by parts for the twisted derivative. -/
theorem integral_mul_fibreCovDeriv_neg (θ : Vec 2) (k : Fin 2) {u v : Vec 2 → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hup : AVenhance.IsZ2Periodic u)
    (hvp : AVenhance.IsZ2Periodic v) :
    ∫ z in AVenhance.unitCube, u z * fibreCovDeriv (-θ) k v z =
      -∫ z in AVenhance.unitCube, fibreCovDeriv θ k u z * v z := by
  have hF : ContDiff ℝ 1 (fun z => u z * v z) := hu.mul hv
  have hFp : AVenhance.IsZ2Periodic (fun z => u z * v z) := fun n z => by
    simp [hup n z, hvp n z]
  have h0 := integral_fderiv_basis_eq_zero_c hF hFp k
  have hdu := hu.differentiable (by simp)
  have hdv := hv.differentiable (by simp)
  have e : ∀ z, fderiv ℝ (fun z => u z * v z) z (basisVec k) =
      u z * fibreCovDeriv (-θ) k v z + fibreCovDeriv θ k u z * v z := fun z => by
    rw [fderiv_fun_mul (hdu z) (hdv z)]
    simp only [fibreCovDeriv, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul, Pi.neg_apply]
    push_cast
    ring
  have hc1 : Continuous fun z => u z * fibreCovDeriv (-θ) k v z :=
    hu.continuous.mul (contDiff_fibreCovDeriv (j := 0) (by simpa using hv) _ k).continuous
  have hc2 : Continuous fun z => fibreCovDeriv θ k u z * v z :=
    (contDiff_fibreCovDeriv (j := 0) (by simpa using hu) _ k).continuous.mul hv.continuous
  simp only [e] at h0
  rw [integral_add (integrableOn_unitCube_of_continuous_c hc1)
    (integrableOn_unitCube_of_continuous_c hc2)] at h0
  exact eq_neg_of_add_eq_zero_left h0

end AVRegularity.CycleWords.Assembly
end
