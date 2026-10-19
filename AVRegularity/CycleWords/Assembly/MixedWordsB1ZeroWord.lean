-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.SlowDamping
public import AVRegularity.CycleWords.MixedWords.AmplitudeLimit

section
section
/-! # The letter Bloch identity (statements)

The stage functions of the word fibre facts are the Bloch periodic parts of the moment-weighted levels,
`b1wStageFun θ β e (u_j(r)) = planeBlochC θ (y^β⟨e, u_j(r)⟩)` (the values of
`AmplitudeIdentificationStatement`). The forcing of its cell problem of stage `(j, x, e, β)`,
tested against a smooth periodic `φ`, is
`b1wTestedSource` = `∫ S φ - ∑_k ∫ F_k (∂_k - iθ_k)φ`. This is the bilinear form of the
`cellComplexSource` that the splittings H3s and H4 of the word fibre facts bound.

`LetterBlochStatement` writes this tested forcing through earlier stage functions only:

* the same-level terms (`b1wSameLevel`): lower moments of the same level, with the constant
  metric `G(r)` and the periodic drift `v(r, ·)`;
* the previous-level letter terms: the letter flux tested against the moment weight
  (`b1wFluxPair`) is `0` at level `0`, and at level `j + 1` it expands (`b1wLetterExpansion`) over
  components `x'`, admissible orders `d`, edge constituents `γ`, words `α` of length `d - 1`,
  Taylor orders `s` and words `ω` (the slow Taylor polynomial in `δy`, `δ = ϖη_g`). Each term is
  `δ^s/s!` times the jet-to-value pairing (`b1wJetPair`) of
  the level-`j` stage function at moment `β₀ + #ω - a`, for vector `γ.map* e`, against the
  transposed derivative `D_{-θ}^{#α - a}` of the periodic coefficient `∂_X^ω γ.coeff_α(r, X₀, ·)`
  times the test.

These transposed constituents are those of the transverse blocks: for smooth periodic `g`,
`∑_{k,α} (-1)^{d-1} ∫ g D_{-θ}^{α}(a_{α,k} D_{-θ,k} φ)` is minus the row pairing of `φ` with the
constituent flux of `g`. So the row bounds of the transverse blocks apply term by term. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- The stage function: the Bloch periodic part at `θ` of `y^β⟨e, g(y)⟩`. -/
def b1wStageFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ : Vec 2)
    (β : ℕ × ℕ) (e : E) (g : Vec 2 → E) : Vec 2 → ℂ :=
  planeBlochC θ (fun y => momentWeight β y * inner ℝ e (g y))

/-- The same-level terms: lower moments with the constant metric and the periodic drift. Each
cell integral is parenthesized: without `∂μ` an integral's body absorbs a following `+ …`
(found when checking the first clause). -/
def b1wSameLevel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ : Vec 2)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2) (β : ℕ × ℕ) (e : E) (g : Vec 2 → E)
    (φ : Vec 2 → ℂ) : ℂ :=
  ((G 0 0 * ((β.1 : ℝ) * ((β.1 : ℝ) - 1)) : ℝ) : ℂ) *
      (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 2, β.2) e g z * φ z) +
    (((G 0 1 + G 1 0) * ((β.1 : ℝ) * (β.2 : ℝ)) : ℝ) : ℂ) *
      (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 1, β.2 - 1) e g z * φ z) +
    ((G 1 1 * ((β.2 : ℝ) * ((β.2 : ℝ) - 1)) : ℝ) : ℂ) *
      (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1, β.2 - 2) e g z * φ z) +
    ((β.1 : ℝ) : ℂ) * (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 1, β.2) e g z *
      ((vf z 0 : ℂ) * φ z + ∑ k : Fin 2, ((G k 0 + G 0 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z)) +
    ((β.2 : ℝ) : ℂ) * (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1, β.2 - 1) e g z *
      ((vf z 1 : ℂ) * φ z + ∑ k : Fin 2, ((G k 1 + G 1 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z))

/-- The jet-to-value pairing (the right side of the jet-to-value identity) of the stage function at
moment `β` and vector `e'` against `D_{-θ}^{#α - a}(c ψ)`. -/
def b1wJetPair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ : Vec 2)
    (β : ℕ × ℕ) (e' : E) (g : Vec 2 → E) (c : Vec 2 → ℝ) {n : ℕ} (α : DerivativeWord2 n)
    (ψ : Vec 2 → ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
      Finset.range ((wordCount α).2 + 1),
    ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
        β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) *
      ∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - a.1, β.2 - a.2) e' g z *
        fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun z' => (c z' : ℂ) * ψ z') z)

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- The forcing of I's cell problem of stage `(j, x, e, β)` at time `r`, tested against `φ`:
`∫ S φ - ∑_k ∫ F_k (∂_k - iθ_k)φ` with I's source `S` and flux `F`. -/
def b1wTestedSource {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (r : ℝ) (φ : Vec 2 → ℂ) : ℂ :=
  (∫ z in AVenhance.unitCube, planeBlochC θ (fun y =>
      (momentWeightLap (F.G r) β y + ∑ i, F.v r y i * momentWeightGrad β y i) *
          inner ℝ e (planeValue (F.u j x r) y) -
        ∑ i, momentWeightGrad β y i * inner ℝ e
          (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
            (j, x) r y i)) z * φ z) -
    ∑ k : Fin 2, ∫ z in AVenhance.unitCube, planeBlochC θ (fun y =>
      momentWeight β y * inner ℝ e
          (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
            (j, x) r y k) -
        (∑ i, (F.G r k i + F.G r i k) * momentWeightGrad β y i) *
          inner ℝ e (planeValue (F.u j x r) y)) z * fibreCovDeriv (-θ) k φ z

/-- The previous-level letter flux tested against the moment weight `y^{β₀}` and `ψ`. -/
def b1wFluxPair {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) : ℂ :=
  ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => momentWeight β₀ y * inner ℝ e
      (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
        (j, x) r y k)) z * ψ z

/-- The letter expansion of `b1wFluxPair` at level `j + 1`: components `x'`, admissible orders
`d`, edge constituents `γ` of letter `j`, words `α`, Taylor orders `s` and words `ω`. -/
def b1wLetterExpansion {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (j : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) : ℂ :=
  ∑ x' : ι, ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
      (j.succ, x) (j.castSucc, x'),
    if hd : d ∈ Finset.Icc 2 D then
      (((F.letters j).edge x x' ⟨d, hd⟩).map fun γ =>
        ∑ α : DerivativeWord2 (d - 1),
          ∑ s ∈ Finset.Icc (if (F.letters j).positive then 1 else 0) (F.letters j).slow,
            ∑ ω : DerivativeWord2 s,
              ((((F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
                b1wJetPair θ (β₀.1 + (wordCount ω).1, β₀.2 + (wordCount ω).2)
                  (ContinuousLinearMap.adjoint γ.map e) (planeValue (F.u j.castSucc x' r))
                  (fun y => iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k) F.X₀
                    (fun i => basisVec (ω i))) α ψ).sum
    else 0

end Frame

/-- **The letter Bloch identity.** For a.e. time of the piece, the tested forcing of every
stage is its same-level terms minus the letter flux pairings; the letter flux vanishes at level
`0` and at level `j + 1` is its expansion over the letter `j`.

For `β = 0` at level `0` the moment derivatives vanish (`momentWeightLap`,
`momentWeightGrad` at `0`) and the previous flux is `0`, so both sides are `0`. For `β = (1,0)`,
`G = I`, `v = 0` at level `0` the source is `0` and the flux is `-2u_e e₀`, so the left side is
`2∫ Stage(0)·∂₀φ`; on the right, the `β.1` term gives `∫ Stage(0)·2∂₀φ` and the letter terms
vanish. For `N_w = 0` the third clause is vacuous. For a letter with one edge constituent of order
`2`, slow order `0` and a constant coefficient `c`, the expansion has `s = 0`, one word of length
`1` and `a ∈ {0, 1}`; the term `a = 0` is the transposed derivative `-∫ Stage(β₀) D_{-θ}(cψ)`, and
`a = 1` (only for `β₀ ≠ 0`) is the moment term.

The hypothesis `order ≤ J`: clause 3 moves `d - 1` derivatives onto the test
`c ψ`, and the frame gives the coefficients only `C^J` in `y`. The word fibre facts supply it:
`order = d_i ≤ max d ≤ wordReserveJstar - 2 ≤ J`. With `d_max` the largest letter order, the
tests are `C^{d_max+1}` in clause 1 and `C^{d_max}` in clause 3 (not `C^∞`): clause 3 moves at
most `d - 1 ≤ d_max - 1` derivatives onto `c ψ` (edges above the letter order are empty), and
clause 1 feeds it `D_{-θ,k} φ`. The word fibre facts apply the identity to `H^{d_max+3}` tests through their
classical representatives (`torusHigherClassicalValue_contDiff`); `d_max` and not the bound `D`,
since the regularity reserve `J` of the word fibre facts is in terms of the actual orders. -/
def LetterBlochStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
  (∀ i, (F.letters i).order ≤ F.J) →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
    (∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (φ : Vec 2 → ℂ),
      ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ →
        AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ j x e β r φ =
        b1wSameLevel θ (F.G r) (F.v r) β e (planeValue (F.u j x r)) φ -
          ((β.1 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1 - 1, β.2) 0 r φ -
          ((β.2 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1, β.2 - 1) 1 r φ -
          ∑ k : Fin 2, b1wFluxPair F θ j x e β k r (fibreCovDeriv (-θ) k φ)) ∧
    (∀ (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
      b1wFluxPair F θ 0 x e β₀ k r ψ = 0) ∧
    ∀ (j : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
      ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ →
        AVenhance.IsZ2Periodic ψ →
      b1wFluxPair F θ j.succ x e β₀ k r ψ = b1wLetterExpansion F θ j x e β₀ k r ψ

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The word fibre facts (the instantiation of the abstract fibre word)

`WordFibreFactsStatement` is the input of the abstract fibre word (`afw_slow`, `afw_fast`) for a
word chain at one frequency, so that the stage inequalities follow (`wordStage_of_fibreFacts`). The proof chooses the index type (stages × components × an orthonormal basis, rescaled by `π_x^{-1/2}` and
`∏θ_i`), the curves (the Bloch periodic parts of the moments of the levels, the amplitude
identification with moments), the terminal adjoint curve `q` (from the test `1`:
`N₀ = ⟨1 + r(b), 1⟩ = 1`; no package row is used), the gauge `Γ = |e^{-Ξ}|`
(H5, `scalarPackage_gauge_growth`, slow damping `π²/16`), the admissible fast tests
(transverse for the region, annihilating `1 + r`) with their norms, and proves the block
splittings H3s and H4 (the letter Bloch identity, the transverse blocks, local transversality
with the rate `π²/8`, the quiet gap, the replacements; errors through a crude pass of the same
inequalities). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- **The word fibre facts.** The datum is the plane value of `f`, vanishing a.e. outside
a ball (as in `RetainedAmplitudeFactorStatement`); the data bounds are by its Bloch jets.

With no letters and `m = 0` there is one stage per component and basis vector; `H3s` and `H4` have
no earlier stages (empty sums), so only the data bounds, the decay of the adjoint test families, and
the output relation remain. For `f = 0` the curves vanish and all quantities are `0`. The constants
`M, out, Q` are chosen after the orders, and `C_z, C_d, C_out, Θ, C_f, c_E` after `C_H, ρ`. -/
def WordFibreFactsStatement : Prop :=
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
        ENNReal.ofReal Cd * datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      ENNReal.ofReal (Dp (out β)) ≤
        ENNReal.ofReal Cd * datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      ENNReal.ofReal ((εs (out β) + εf (out β)) * (b - a)) ≤
        ENNReal.ofReal (Cd * peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
          Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq))) *
          datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ ≤
        ENNReal.ofReal (Real.exp (blockGauge pkg.actual.lam η a b θ).re * Cout *
          wordTheta ηg letters * (slowStage st (out β) W q N₀ a (b - a) +
            fastStage st (out β) W Adm ν Γ a (b - a) +
              (εs (out β) + εf (out β)) * (b - a)))

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The amplitude identification with measurable source and flux (statements)

The statement `AmplitudeIdentificationStatement` is kept as it is. Its
cell problem is forced by the literal source and flux (`amplitudeIdLiteralSource`,
`amplitudeIdLiteralFlux`). These are built pointwise from plane representatives chosen time by
time, so they are not known to be jointly measurable. `CellWeakIdentity` is iterated (slice
integrals, then time), so the literal identity is meaningful. But turning the cell solution into
a Hilbert curve (`cellSolution_to_Hilbert`) needs `MemLp` on the product measure, and in this
Mathlib that includes joint measurability.

* `AmplitudeIdForcingCurvesStatement`: the literal source and each flux component have
  `L²(cell)`-valued time carriers in `L²` in time, slice-wise equal for a.e. time
  (`amplitudeId_word_moment_families` with `amplitudeId_moment_forcing_curves`).
* `AmplitudeIdFibresMeasStatement`: the restated fibre clause of `AmplitudeIdentificationStatement`,
  the form the word fibre facts use. For every stage there are a cell solution, a source and a flux
  in `L²` of `[a,b] × cell`, slice-wise equal for a.e. time to the literal ones, and the value
  identity.

`amplitudeIdFibresMeas_of_literal` derives the second from `AmplitudeIdentificationStatement` and
the first, with jointly measurable versions of the source and flux. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- I's literal source of stage `(j, x, e, β)` at frequency `θ`. -/
def amplitudeIdLiteralSource {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) : ℝ → Vec 2 → ℂ :=
  fun r z => planeBlochC θ (fun y =>
    (momentWeightLap (F.G r) β y + ∑ i, F.v r y i * momentWeightGrad β y i) *
        inner ℝ e (planeValue (F.u j x r) y) -
      ∑ i, momentWeightGrad β y i * inner ℝ e
        (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
          (j, x) r y i)) z

/-- I's literal flux of stage `(j, x, e, β)` at frequency `θ`. -/
def amplitudeIdLiteralFlux {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun r z => WithLp.toLp 2 fun k => planeBlochC θ (fun y =>
    momentWeight β y * inner ℝ e
        (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r)
          (j, x) r y k) -
      (∑ i, (F.G r k i + F.G r i k) * momentWeightGrad β y i) *
        inner ℝ e (planeValue (F.u j x r) y)) z

end Frame

/-- **The literal forcing has `L²` time carriers** (`amplitudeId_word_moment_families`,
`amplitudeId_moment_forcing_curves`). -/
def AmplitudeIdForcingCurvesStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ),
    (∃ R : ℝ → ComplexCellL2, MemLp R 2 (volume.restrict (Icc F.a F.b)) ∧
      ∀ᵐ t ∂volume.restrict (Icc F.a F.b), R t =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ j x e β t) ∧
    ∀ k : Fin 2, ∃ Q : ℝ → ComplexCellL2, MemLp Q 2 (volume.restrict (Icc F.a F.b)) ∧
      ∀ᵐ t ∂volume.restrict (Icc F.a F.b), Q t =ᵐ[volume.restrict AVenhance.unitCube]
        fun z => amplitudeIdLiteralFlux F θ j x e β t z k

/-- **I's fibre clause with measurable source and flux.** For every stage there are a cell
solution of the actual fibre problem, a source and a flux in `L²([a,b] × cell)` that agree slice
by slice, for a.e. time, with the literal ones, and the value identity of I.

At level `0` with `β = 0` the literal source and flux vanish, so `0` is a measurable
choice. Only the metric threshold `g₁` precedes the data, as in the statements this one refines. -/
def AmplitudeIdFibresMeasStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ),
    ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
      (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
      MemLp (Function.uncurry src) 2
        ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
      (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
        ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
        Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
      IsCellSolution (Icc F.a F.b)
        (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
      ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y))

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # A word of zero amplitude has no terminal level (statement)

The output relation of the word fibre facts (and of the stage inequalities, the moment amplitudes
and `RetainedAmplitudeFactorStatement`) bounds the moment amplitudes of the terminal
level by the word amplitude `Θ_w = ∏ θ_l (η_g if positive)`. When some `θ_l = 0`, the stage
rescaling `A_j⁻¹` of the word fibre facts is `0` from level `l + 1` on and carries no information, so this case
is proved directly: the letter `l` then has the zero majorant (`row_sum`, `nonneg`), its
coefficient jets vanish for almost every time (`analytic`, an essential supremum), the level
`l + 1` has zero forcing and zero datum, so it vanishes (`wordChainSuccessor_l2_duhamel`), and so do
the later levels. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- **A word of zero amplitude has no terminal level.**

With no letters (`N_w = 0`) one has `Θ_w = 1` and the statement is vacuous. For one letter with
`θ = 0` (for instance no edges) the majorant is `0`, the flux vanishes a.e. in time, and level
`1` starts from `0` (`chainDatum`), so it is `0`. If a letter in the middle is zero, the levels
after it vanish, since every later letter acts on `0`. At `t = a` every level `j ≥ 1` is its datum
`0`. There are no constants. -/
def ZeroAmplitudeWordStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁),
    wordTheta F.ηg F.letters = 0 →
    ∀ x, ∀ t ∈ Icc F.a F.b, planeValue (F.u (Fin.last Nw) x t) =ᵐ[volume] 0

end AVRegularity.CycleWords.Assembly
end
end
end
