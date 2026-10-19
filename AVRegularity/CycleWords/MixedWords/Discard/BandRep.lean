-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.PlaneVec
public import AVRegularity.CycleWords.MixedWords.Discard.Letter
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
public import AVRegularity.CycleWords.MixedWords.Discard.BandCoeff
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
section
/-! # the block bound of the coupling from the transform families

At a quiet time the transform families of the zone (`StageFamilyZoneStatement`) tested on the modes
give the `ℓ²` bound of the adjoint blocks of `τ(r)` (`quiet_block_bound`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

local instance G1Measure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem value_norm_le' (K : ℕ) (U : TorusHk K ℂ) : ‖torusHkValueCLM U‖ ≤ ‖U‖ := by
  change ‖U.val (valueIndex2 K)‖ ≤ ‖U.val‖
  exact PiLp.norm_apply_le _ _

theorem mode_value_norm (n : Fin 2 → ℤ) (γ : ℂ) :
    ‖γ • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)‖ = ‖γ‖ := by
  rw [norm_smul, scalarTorusToCell.norm_map,
    (UnitAddTorus.orthonormal_mFourier (d := Fin 2)).norm_eq_one n, mul_one]

theorem hk_mode_norm_sq (N : ℕ) (n : Fin 2 → ℤ) (c : ℂ) :
    ‖quietHsMode N n c‖ ^ 2 = ‖c‖ ^ 2 * ModeNorm N n := by
  have := hk_norm_sq N {n} (fun _ => c)
  simpa using this

section Block

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The block bound of the coupling.** -/
theorem quiet_block_bound {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (hr0 : ∀ z, F.v r z = 0)
    (hq : ∀ l, ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (N N' k k' : ℕ) (hN : 2 ≤ N) (hkk : k' < k) {Bz : ℝ} (n : Fin 2 → ℤ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk N' ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ Bz ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (a : B1WIndex ι h Nw m Ks → ℂ) :
    ∑ i' ∈ stageSet b1wSt k', ‖∑ i ∈ stageSet b1wSt k,
        (starRingEnd ℂ) (quietTau F θ n r i i') * a i‖ ^ 2 ≤
      Bz ^ 2 * ModeNorm N n * ∑ i ∈ stageSet b1wSt k, ‖a i‖ ^ 2 := by
  classical
  obtain ⟨Φ, hΦv, hΦn⟩ := hprov (fun i => quietHsMode N n (a i))
  set γ : B1WIndex ι h Nw m Ks → ℂ := fun i' =>
    ∑ i ∈ stageSet b1wSt k, (starRingEnd ℂ) (quietTau F θ n r i i') * a i with hγ
  have hval : ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (Φ i') =
      γ i' • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n) := by
    intro i' hi'
    have hst : ∀ i : B1WIndex ι h Nw m Ks, i ∈ stageSet b1wSt k → b1wSt i' < b1wSt i :=
        fun i hi => by
      rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hi').2]; exact hkk
    apply Lp.ext
    rw [scalarTorusToCell_mode]
    filter_upwards [hΦv i' hi', Lp.coeFn_smul (γ i')
      ((cellComplexFourierMode_memLp n).toLp (cellComplexFourierMode n)),
      (cellComplexFourierMode_memLp n).coeFn_toLp] with y h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, hγ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [classical_quietHsMode N hN]
    have e : (fun y => star (a i * cellComplexFourierMode n y)) =
        fun y => star (a i) * cellComplexFourierMode (-n) y := by
      funext y; rw [star_mul', star_cellComplexFourierMode]
    rw [e, b1wTestTransform_mode F θ i i' r hr0 hq (-n) (star (a i)) y]
    simp only [quietTau, hst i hi, ↓reduceIte, star_mul', star_cellComplexFourierMode, neg_neg,
      map_mul, Complex.star_def, Complex.conj_conj]
    have hrr : (starRingEnd ℂ) (b1wScaleRatio F.π F.ϖ F.ηg F.letters i i') =
        b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' := b1wScaleRatio_star _ _ _ _ _ _
    rw [hrr]
    ring
  have hnorm : ∀ i' ∈ stageSet b1wSt k', ‖γ i'‖ ≤ ‖Φ i'‖ := by
    intro i' hi'
    calc ‖γ i'‖ = ‖γ i' • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)‖ :=
          (mode_value_norm n _).symm
      _ = ‖torusHkValueCLM (Φ i')‖ := by rw [hval i' hi']
      _ ≤ ‖Φ i'‖ := value_norm_le' _ _
  calc ∑ i' ∈ stageSet b1wSt k', ‖γ i'‖ ^ 2 ≤ ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 :=
        Finset.sum_le_sum fun i' hi' => pow_le_pow_left₀ (norm_nonneg _) (hnorm i' hi') 2
    _ ≤ Bz ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖quietHsMode N n (a i)‖ ^ 2 := hΦn
    _ = _ := by
        simp_rw [hk_mode_norm_sq]
        rw [← Finset.sum_mul]
        ring

end Block

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the forward letter operators

`fwdLetterOps : FwdLetterOpsStatement`, the mirror of `letterOpsZone`: the forward
transform `ratio · b1wLetterTransform` is the family `fwdGfam` of the block operators
(`ratio_letterTransform`), realized by `fwd_letterBlock_exists`; the stage blocks are
recovered by `block_reduce` with the roles of input and output exchanged. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

section Ratio

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ}

theorem list_scale {α : Type*} (l : List α) (a : α → ℝ) (g : α → ℂ) (c : ℝ) :
    (c : ℂ) * (l.map fun γ => ((a γ : ℝ) : ℂ) * g γ).sum =
      (l.map fun γ => ((a γ : ℝ) : ℂ) * ((c : ℂ) * g γ)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, mul_add, ih]
    congr 1
    ring

open Classical in
theorem letterPart_scaled {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (i i' : B1WIndex ι h Nw m Ks) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) (z : Vec 2)
    (c : ℝ) :
    (c : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i) β₀ k r ψ i' z =
      ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
          (l.succ, i.2.1) (l.castSucc, i'.2.1),
        if hd : d ∈ Finset.Icc 2 D then
          (((F.letters l).edge i.2.1 i'.2.1 ⟨d, hd⟩).map fun γ =>
            ((letterMat (stdOrthonormalBasis ℝ (h i.2.1)) (stdOrthonormalBasis ℝ (h i'.2.1)) γ.map
              i.2.2.2 i'.2.2.2 : ℝ) : ℂ) *
              ((c : ℂ) * letterGam θ (F.letters l).positive (F.letters l).slow
                (F.ϖ * F.ηg) F.X₀ r d γ.coeff β₀ k (b1wMom i') ψ z)).sum
        else 0 := by
  have hl : ∀ (M : h i'.2.1 →L[ℝ] h i.2.1),
      letterMat (stdOrthonormalBasis ℝ (h i.2.1)) (stdOrthonormalBasis ℝ (h i'.2.1)) M
        i.2.2.2 i'.2.2.2 = inner ℝ (ContinuousLinearMap.adjoint M (b1wVec i)) (b1wVec i') :=
    fun M => rfl
  rw [tbLetterPart_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true, hl]
    exact list_scale ((F.letters l).edge i.2.1 i'.2.1 ⟨d, hd⟩)
      (fun γ => inner ℝ (ContinuousLinearMap.adjoint γ.map (b1wVec i)) (b1wVec i'))
      (fun γ => letterGam θ (F.letters l).positive (F.letters l).slow (F.ϖ * F.ηg)
        F.X₀ r d γ.coeff β₀ k (b1wMom i') ψ z) c
  · simp [hd]

theorem ratio_letterTransform {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (r : ℝ)
    (f : Vec 2 → ℂ) (z : Vec 2) :
    ((letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i') : ℝ) : ℂ) *
        b1wLetterTransform F θ i i' r f z =
      fwdGfam θ (F.letters l)
        (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, i.2.1)
          (l.castSucc, i'.2.1)) (F.ϖ * F.ηg) F.X₀ r i.2.1 i'.2.1 (b1wMom i) (b1wMom i')
        (letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i'))
        i.2.2.2 i'.2.2.2 f z := by
  classical
  set R := letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i') with hR
  have hT : b1wLetterTransform F θ i i' r f z =
      -((((b1wMom i).1 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1 - 1, (b1wMom i).2) 0 r f i' z) -
      (((b1wMom i).2 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1, (b1wMom i).2 - 1) 1 r f i' z -
      ∑ k : Fin 2, b1wLetterPart F θ l i.2.1 (b1wVec i) (b1wMom i) k r
        (fibreCovDeriv (-θ) k f) i' z := by
    unfold b1wLetterTransform
    rw [Finset.sum_eq_single l]
    · simp only [hi, hi', and_self, ite_true]
    · intro l' _ hne
      have hn : ¬ (i.1 = l'.succ ∧ i'.1 = l'.castSucc) := by
        rintro ⟨h1, -⟩
        rw [hi] at h1
        exact hne (Fin.succ_injective _ h1.symm)
      simp only [hn, ite_false]
    · intro hl; exact absurd (Finset.mem_univ l) hl
  rw [hT]
  simp only [Fin.sum_univ_two]
  have k1 := letterPart_scaled F θ l i i' ((b1wMom i).1 - 1, (b1wMom i).2) 0 r f z
    (R * -(((b1wMom i).1 : ℝ)))
  have k2 := letterPart_scaled F θ l i i' ((b1wMom i).1, (b1wMom i).2 - 1) 1 r f z
    (R * -(((b1wMom i).2 : ℝ)))
  have k3 := letterPart_scaled F θ l i i' (b1wMom i) 0 r (fibreCovDeriv (-θ) 0 f) z (R * -1)
  have k4 := letterPart_scaled F θ l i i' (b1wMom i) 1 r (fibreCovDeriv (-θ) 1 f) z (R * -1)
  unfold fwdGfam
  simp only [letterVars, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    variantFun, Bool.false_eq_true, ↓reduceIte]
  rw [← k1, ← k2, ← k3, ← k4]
  push_cast
  ring

end Ratio

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the scalar plane statement from three component statements

For one real component `u`, one word `w` and one moment `β`, put `v = ∂^w u - ∂^w (μ(D) u)`.
The three component statements are:

* `JetFourierStatement`: `v ∈ L²` and its radian transform is
  `Φ_w(ξ) = (iξ)^w (1 - μ(ξ)) û(ξ)` (weak jets of `PlaneHk` are `L²` weak derivatives, so the
  transform of `∂_j f` is `iξ_j f̂`: `planeFourier_real_weakDerivative_ae`; the cutoff is the
  convolution with the Schwartz kernel `cutoffKernel μ`, whose transform is `μ`).
* `MomentPlancherelStatement`: if an `L²` function has the transform `Φ`, and `Φ` has
  classical partial derivatives `D_γ` (`γ ≤ β`) that are in `L²`, then `∫ y^{2β} v² = (2π)⁻² ∫ |D_β|²`
  (the transform of `y_j f` is `i ∂_j f̂`; use `planeFourier_distribution_derivative_ae` and
  `planeFourier_distribution_derivative_of_ae` inductively on `|β|`).
* `FtCalculusStatement`: the derivatives `D_γ` of `Φ_w` exist, are continuous, and are
  pointwise bounded by `C` times the band integrands of the transforms of the moments `y^{γ'} u`,
  `γ' ≤ γ` (Leibniz; `∂_j û = -i FT(y_j u)`; `1 - μ` and the jets of `μ` vanish on `|ξ| < ρ`;
  the symbol of `w` has degree `≤ K_f`).

`scalar_of_parts` proves `ScalarStatement` from them. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

/-- The radian symbol `∏_j (i ξ_{w_j})` of a derivative word. -/
def derivativeWordSymbol {a : ℕ} (w : DerivativeWord2 a) (ξ : Vec 2) : ℂ :=
  ∏ j : Fin a, (Complex.I * (ξ (w j) : ℂ))

/-- The frequency side of the jet `∂^w (u - μ(D)u)`: `(iξ)^w (1 - μ(ξ)) û(ξ)`. -/
def jetFrequencySide {a : ℕ} (μ : Vec 2 → ℝ) (w : DerivativeWord2 a) (g : Vec 2 → ℝ) (ξ : Vec 2) : ℂ :=
  derivativeWordSymbol w ξ * ((1 - μ ξ : ℝ) : ℂ) * planeTransform g ξ

/-- `v` is a real `L²` function with radian transform `Φ`. -/
def HasFT (v : Vec 2 → ℝ) (Φ : Vec 2 → ℂ) : Prop :=
  ∃ hv : MemLp v 2 volume,
    fourierL2 (ofRealL2 volume (hv.toLp v)) =ᵐ[volume] fun x => Φ ((2 * Real.pi) • x)

/-- A family `D` of functions on frequency space with `D 0 = Φ` and `D (γ + e_j) = ∂_j D γ`
(classical partial derivatives, continuous), for the multi-indices `γ ≤ β`. -/
def DerivFamily (β : ℕ × ℕ) (Φ : Vec 2 → ℂ) (D : ℕ × ℕ → Vec 2 → ℂ) : Prop :=
  D (0, 0) = Φ ∧
  (∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → Continuous (D γ)) ∧
  (∀ γ : ℕ × ℕ, γ.1 + 1 ≤ β.1 → γ.2 ≤ β.2 → ∀ ξ : Vec 2,
    HasDerivAt (fun t : ℝ => D γ (ξ + t • basisVec 0)) (D (γ.1 + 1, γ.2) ξ) 0) ∧
  (∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 + 1 ≤ β.2 → ∀ ξ : Vec 2,
    HasDerivAt (fun t : ℝ => D γ (ξ + t • basisVec 1)) (D (γ.1, γ.2 + 1) ξ) 0)

/-- The transform of the jet of `u - μ(D)u`. -/
def JetFourierStatement : Prop :=
  ∀ (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ θ, μ (-θ) = μ θ) →
  ∀ (κ a : ℕ), a ≤ κ → ∀ u : PlaneHk Set.univ κ ℝ, Integrable (planeValue u) →
  ∀ w : DerivativeWord2 a,
    HasFT (fun z => planeJetOrder u a w z -
      orderedDerivative w (fourierCutoff μ (planeValue u)) z) (jetFrequencySide μ w (planeValue u))

/-- Plancherel with moments, from the derivatives of the transform. -/
def MomentPlancherelStatement : Prop :=
  ∀ (v : Vec 2 → ℝ) (Φ : Vec 2 → ℂ), HasFT v Φ →
  ∀ (β : ℕ × ℕ) (D : ℕ × ℕ → Vec 2 → ℂ), DerivFamily β Φ D →
    (∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 < ∞) →
    ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * v z ^ 2) =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ‖D β ξ‖ₑ ^ 2

/-- The derivatives of `Φ_w` and their band bounds. -/
def FtCalculusStatement : Prop :=
  ∀ (Kf m : ℕ) (ρ Bμ : ℝ), 0 ≤ ρ → 0 ≤ Bμ → ∃ C : ℝ, 0 < C ∧
  ∀ (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ (l : ℕ) θ, l ≤ m + Kf → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) →
    (∀ θ, vecDot θ θ < ρ ^ 2 → μ θ = 1) →
  ∀ (a : ℕ), a ≤ Kf → ∀ w : DerivativeWord2 a, ∀ g : Vec 2 → ℝ,
    (∀ β ∈ momentIndices m, Integrable (fun y => momentWeight β y * g y)) →
  ∀ β ∈ momentIndices m, ∃ D : ℕ × ℕ → Vec 2 → ℂ,
    DerivFamily β (jetFrequencySide μ w g) D ∧
    ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → ∀ ξ : Vec 2,
      ‖D γ ξ‖ ^ 2 ≤ C * ∑ γ' ∈ (momentIndices m).filter (fun γ' => γ'.1 ≤ γ.1 ∧ γ'.2 ≤ γ.2),
        (if ρ ^ 2 ≤ vecDot ξ ξ then
          (1 + vecDot ξ ξ) ^ Kf * ‖planeTransform (fun y => momentWeight γ' y * g y) ξ‖ ^ 2 else 0)

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the band output (`BandOutputStatement`), assembly

`BandOutputStatement` from three steps:

* `BandRepStatement`: for a multiplier supported in the ball of radius `π/2` and a field with
  integrable moments of order `≤ m`, the cutoff is the band-limited function `ampFun` of the
  cosine/sine amplitudes `cutoffCosAmplitude`, `cutoffSinAmplitude`, which are `C^m` bands.
* `BandAmpOutputStatement`: for band amplitudes the output norm `jetOutputNorm` of `ampFun` is
  bounded by the `L²` norm of `amplitudeJetNorm` (from `layer_sq_le` with `M = a`, where
  `ϖ^a (1 + |θ|/ϖ)^a ≤ (1 + π/2)^a`).
* `BandJetStatement`: the pointwise bound of `amplitudeJetNorm` of the cutoff amplitudes by the
  cell means (Leibniz for the product with the multiplier, `ϖ^l ‖∂^l μ‖ ≤ B_μ`, and the Fourier
  jets of the moments). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleWords.Assembly
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard.BandDatum

universe u v

/-- Step 1: representation and smoothness. -/
def BandRepStatement : Prop :=
  ∀ (m : ℕ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ →
    (∀ θ, μ θ ≠ 0 → vecDot θ θ ≤ (Real.pi / 2) ^ 2) →
  ∀ U : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (U x) volume) →
    (∀ x, ∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • U x y)) →
  ∀ x, IsBandAmp (Real.pi / 2) m (cutoffCosAmplitude μ (U x)) ∧
    IsBandAmp (Real.pi / 2) m (cutoffSinAmplitude μ (U x)) ∧
    ∀ z, fourierCutoff μ (U x) z =
      ampFun (Real.pi / 2) (cutoffCosAmplitude μ (U x)) (cutoffSinAmplitude μ (U x)) z

/-- Step 2: the output norm of a band-limited family by the `L²` norm of its amplitude jets. -/
def BandAmpOutputStatement : Prop :=
  ∀ (Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (ϖ rstar : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 < rstar → rstar ≤ Cout →
  ∀ A B : ∀ x, Vec 2 → h x, (∀ x, IsBandAmp (Real.pi / 2) m (A x)) →
    (∀ x, IsBandAmp (Real.pi / 2) m (B x)) →
    jetOutputNorm π m Kf ϖ rstar
        (fun x _ wd z => orderedDerivative wd (ampFun (Real.pi / 2) (A x) (B x)) z) ≤
      ENNReal.ofReal C * (∫⁻ θ, amplitudeJetNorm π m ϖ A B θ ^ 2) ^ (1 / 2 : ℝ)

open scoped Classical in
/-- Step 3: the amplitude jets of the cutoff against the cell means (pointwise in `θ`). -/
def BandJetStatement : Prop :=
  ∀ (m : ℕ), ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (ϖ ρ₁ Bμ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ρ₁ → 0 ≤ Bμ →
  ∀ μ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ θ, μ θ ≠ 0 → ρ₁ ^ 2 ≤ vecDot θ θ ∧ vecDot θ θ ≤ (Real.pi / 2) ^ 2) →
    (∀ (l : ℕ) θ, l ≤ m → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ / ϖ ^ l) →
  ∀ U : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (U x) volume) →
    (∀ x, ∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • U x y)) →
  ∀ θ : Vec 2,
    amplitudeJetNorm π m ϖ (fun x => cutoffCosAmplitude μ (U x))
        (fun x => cutoffSinAmplitude μ (U x)) θ ≤
      ENNReal.ofReal (C * Bμ) *
        (if θ ∈ freqCube ∧ ρ₁ ^ 2 ≤ vecDot θ θ then outMeanSq π ϖ m θ U else 0) ^ (1 / 2 : ℝ)

open scoped Classical in
theorem lintegral_indicator_sq {Q : Vec 2 → ℝ≥0∞} {P : Vec 2 → Prop} {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ θ, (c * (if θ ∈ freqCube ∧ P θ then Q θ else 0) ^ (1 / 2 : ℝ)) ^ 2 =
      c ^ 2 * ∫⁻ θ in freqCube, if P θ then Q θ else 0 := by
  have hpt : ∀ θ, (c * (if θ ∈ freqCube ∧ P θ then Q θ else 0) ^ (1 / 2 : ℝ)) ^ 2 =
      c ^ 2 * (freqCube.indicator (fun θ => if P θ then Q θ else 0) θ) := by
    intro θ
    by_cases hθ : θ ∈ freqCube
    · by_cases hP : P θ
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hθ, hP⟩), mul_pow, rpow_half_sq, Set.indicator_of_mem hθ, ite_eq_left_of_eq_true _ _ (eq_true hP)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hh => hP hh.2), Set.indicator_of_mem hθ, ite_eq_right_of_eq_false _ _ (eq_false hP),
          ENNReal.zero_rpow_of_pos (by norm_num)]
        simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hh => hθ hh.1), Set.indicator_of_notMem hθ,
        ENNReal.zero_rpow_of_pos (by norm_num)]
      simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc), lintegral_indicator measurableSet_freqCube]

open scoped Classical in
/-- **O2 from its three steps.** -/
theorem bandOutputStatement_of_steps (h1 : BandRepStatement.{u, v})
    (h2 : BandAmpOutputStatement.{u, v}) (h3 : BandJetStatement.{u, v}) :
    BandOutputStatement.{u, v} := by
  intro Kf m Cout hCout
  obtain ⟨C₂, hC₂, h2'⟩ := h2 Kf m Cout hCout
  obtain ⟨C₃, hC₃, h3'⟩ := h3 m
  refine ⟨C₂ * C₃, mul_pos hC₂ hC₃, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ rstar ρ₁ Bμ hϖ hϖ1 hr hrC hρ hB μ hμ hev hsupp hjet U hmeas hint
  have hball : ∀ θ, μ θ ≠ 0 → vecDot θ θ ≤ (Real.pi / 2) ^ 2 := fun θ hθ => (hsupp θ hθ).2
  have hrep := fun x => h1 m μ hμ hball U hmeas hint x
  have hjn : jetOutputNorm π m Kf ϖ rstar
      (fun x _ wd z => orderedDerivative wd (fourierCutoff μ (U x)) z) =
      jetOutputNorm π m Kf ϖ rstar (fun x _ wd z => orderedDerivative wd
        (ampFun (Real.pi / 2) (cutoffCosAmplitude μ (U x)) (cutoffSinAmplitude μ (U x))) z) := by
    congr 1
    funext x a wd z
    rw [show fourierCutoff μ (U x) = ampFun (Real.pi / 2) (cutoffCosAmplitude μ (U x))
      (cutoffSinAmplitude μ (U x)) from funext (hrep x).2.2]
  rw [hjn]
  refine (h2' π hπ ϖ rstar hϖ hϖ1 hr hrC _ _ (fun x => (hrep x).1) (fun x => (hrep x).2.1)).trans ?_
  have hjetθ := h3' π hπ ϖ ρ₁ Bμ hϖ hϖ1 hρ hB μ hμ hev hsupp hjet U hmeas hint
  have hI : (∫⁻ θ, amplitudeJetNorm π m ϖ (fun x => cutoffCosAmplitude μ (U x))
        (fun x => cutoffSinAmplitude μ (U x)) θ ^ 2) ≤
      ENNReal.ofReal (C₃ * Bμ) ^ 2 * ∫⁻ θ in freqCube,
        (if ρ₁ ^ 2 ≤ vecDot θ θ then outMeanSq π ϖ m θ U else 0) := by
    rw [← lintegral_indicator_sq ENNReal.ofReal_ne_top]
    exact lintegral_mono fun θ => pow_le_pow_left₀ zero_le (hjetθ θ) 2
  calc ENNReal.ofReal C₂ * (∫⁻ θ, amplitudeJetNorm π m ϖ (fun x => cutoffCosAmplitude μ (U x))
        (fun x => cutoffSinAmplitude μ (U x)) θ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal (C₃ * Bμ) ^ 2 * ∫⁻ θ in freqCube,
        (if ρ₁ ^ 2 ≤ vecDot θ θ then outMeanSq π ϖ m θ U else 0)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hI (by norm_num)) _
    _ = ENNReal.ofReal ((C₂ * C₃) * Bμ) * (∫⁻ θ in freqCube,
        (if ρ₁ ^ 2 ≤ vecDot θ θ then outMeanSq π ϖ m θ U else 0)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half, ← mul_assoc,
          ← ENNReal.ofReal_mul hC₂.le, mul_assoc]

end AVRegularity.CycleWords.Discard.BandDatum
end
end
end

section
section
/-! # the forward letter operators, assembly

`fwdLetterOps : FwdLetterOpsStatement` (mirror of `letterOpsZone`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

/-- The chosen family of an `FBRealizes`. -/
def FBRealizes.op {m₁ m₂ N n s : ℕ} {G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c : ℝ}
    (hh : FBRealizes N n s G c) : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ :=
  Classical.choose (show ∃ _T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ, _ from hh)

theorem FBRealizes.op_spec {m₁ m₂ N n s : ℕ} {G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {c : ℝ} (hh : FBRealizes N n s G c) :
    BlockBound c (fun b' b => hh.op b b') ∧
    ∀ φ : Vec 2 → ℂ, ContDiff ℝ (s : ℕ) φ → AVenhance.IsZ2Periodic φ →
      (∀ b b', Continuous (G b b' φ)) ∧ ∀ b b' (X : TorusHk N ℂ),
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (hh.op b b' X) : Vec 2 → ℂ) y * φ y =
          ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * G b b' φ y :=
  Classical.choose_spec (show ∃ _T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ, _ from hh)

open Classical in
theorem fwdLetterOps : FwdLetterOpsStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  have hC0 : 0 ≤ 4 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks) := by
    unfold gamCfin gamPr
    have h1 := gamCc_nonneg D (m + ∑ l, Ks l) (Finset.univ.sup Ks)
    have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  refine ⟨4 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks), hC0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  have hθ := fun k => (hρ k).trans (le_abs_self ρ)
  have hgood : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
      ∀ l, LetterGood (F.letters l) (Icc F.a F.b) F.J r := by
    have h1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ l, r ∈ Icc F.a F.b →
        LetterGood (F.letters l) (Icc F.a F.b) F.J r :=
      ae_all_iff.2 fun l => letterGood_ae F.π F.piece.hπ (F.letters l) (Icc F.a F.b) F.J F.H
        (F.piece.hlet l)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1] with r hr hrI l using hr l hrI
  filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with r hg hr
  intro l N hN1
  set M0 := m + ∑ l, Ks l with hM0
  set Sm := Finset.univ.sup Ks with hSm
  set Dmax := Finset.univ.sup d with hDmax
  have hord : (F.letters l).order ≤ Dmax := by
    rw [(hlet l).1]; exact Finset.le_sup (f := d) (Finset.mem_univ l)
  have hslow : (F.letters l).slow ≤ Sm := by
    rw [(hlet l).2.1]; exact Finset.le_sup (f := Ks) (Finset.mem_univ l)
  have hN1' : n + (F.letters l).order ≤ N := by rw [(hlet l).1]; exact hN1
  let A : ι → ι → Finset ℕ := fun x x' => admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
    (l.succ, x) (l.castSucc, x')
  have hBR : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      FBRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n (Dmax + 1)
        (fwdGfam θ (F.letters l) (A x x') (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (4 * gamCfin D n |ρ| M0 Sm * (if LetterMomRel Sm (Dmax + 1) β β' then 1 else 0) *
          letterCompWeight (F.letters l) x x') := fun x x' β β' hβ hβ' =>
    fwd_letterBlock_exists F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) r hr (hg l) F.piece.hπ
      F.ϖ F.ηg hϖpos hϖ1 F.piece.hηg F.piece.hηg1 θ |ρ| hθ F.X₀ (A x x') n N Dmax M0 Sm hord hslow
      hJ hN1' (Dmax + 1) (Nat.le_succ _) x x' β β' hβ hβ'
  let Top : ∀ (x x' : ι) (β β' : ℕ × ℕ), Fin (Module.finrank ℝ (h x)) →
      Fin (Module.finrank ℝ (h x')) → TorusHk N ℂ →L[ℝ] TorusHk n ℂ := fun x x' β β' =>
    if hh : β.1 + β.2 ≤ M0 ∧ β'.1 + β'.2 ≤ M0 then (hBR x x' β β' hh.1 hh.2).op
    else fun _ _ => 0
  refine ⟨fun i i' => Top i.2.1 i'.2.1 (b1wMom i) (b1wMom i') i.2.2.2 i'.2.2.2, ?_, ?_⟩
  · intro i i' hi hi' X φ hφ hφp
    have hM : (b1wMom i).1 + (b1wMom i).2 ≤ M0 := stage_mom_le i
    have hM' : (b1wMom i').1 + (b1wMom i').2 ≤ M0 := stage_mom_le i'
    have hφ' : ContDiff ℝ ((Dmax + 1 : ℕ) : ℕ) φ := by exact_mod_cast hφ
    have hspec := ((hBR i.2.1 i'.2.1 (b1wMom i) (b1wMom i') hM hM').op_spec.2 φ hφ' hφp).2
      i.2.2.2 i'.2.2.2 X
    simp only [Top, hM, hM', and_self, dite_true]
    rw [hspec, b1wScaleRatio_letter F.π F.ϖ F.ηg F.letters l i i' hi hi', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← ratio_letterTransform F θ l i i' hi hi' r φ y]
    ring
  · intro S S' x x' β β' hS hS' f
    have hnn : 0 ≤ ∑ i' ∈ S', ‖f i'‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    by_cases hSe : S.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hSe]
      simp only [Finset.sum_empty]
      positivity
    by_cases hSe' : S'.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hSe']
      simp
    obtain ⟨i0, hi0⟩ := hSe
    obtain ⟨i0', hi0'⟩ := hSe'
    obtain ⟨hβ, b0, -⟩ := stage_eq i0 l.succ x β ⟨(hS i0 hi0).1, (hS i0 hi0).2⟩
    obtain ⟨hβ', b0', -⟩ := stage_eq i0' l.castSucc x' β' ⟨(hS' i0' hi0').1, (hS' i0' hi0').2⟩
    let mk : Fin (Module.finrank ℝ (h x)) → B1WIndex ι h Nw m Ks := fun b =>
      ⟨l.succ, x, ⟨β, hβ⟩, b⟩
    let mk' : Fin (Module.finrank ℝ (h x')) → B1WIndex ι h Nw m Ks := fun b =>
      ⟨l.castSucc, x', ⟨β', hβ'⟩, b⟩
    have hM : β.1 + β.2 ≤ M0 := stage_mom_le (mk b0)
    have hM' : β'.1 + β'.2 ≤ M0 := stage_mom_le (mk' b0')
    have hTm : ∀ b' b, Top (mk b).2.1 (mk' b').2.1 (b1wMom (mk b)) (b1wMom (mk' b'))
        (mk b).2.2.2 (mk' b').2.2.2 = (hBR x x' β β' hM hM').op b b' := by
      intro b' b
      show Top x x' β β' b b' = _
      simp only [Top, hM, hM', and_self, dite_true]
    have key := block_reduce (fun b' b => (hBR x x' β β' hM hM').op b b') _
      (hBR x x' β β' hM hM').op_spec.1 mk' mk
      (fun a b hab => by simpa [mk'] using hab) (fun a b hab => by simpa [mk] using hab)
      (fun i' i => Top i.2.1 i'.2.1 (b1wMom i) (b1wMom i') i.2.2.2 i'.2.2.2)
      hTm S' S
      (fun i hi => by
        obtain ⟨hβi, b, hb⟩ := stage_eq i l.castSucc x' β' ⟨(hS' i hi).1, (hS' i hi).2⟩
        exact ⟨b, hb.symm⟩)
      (fun i hi => by
        obtain ⟨hβi, b, hb⟩ := stage_eq i l.succ x β ⟨(hS i hi).1, (hS i hi).2⟩
        exact ⟨b, hb.symm⟩) f
    calc _ ≤ _ := key
      _ = _ := by ring

end AVRegularity.CycleWords.Discard
end
end

section
/-! # finite moments give `C^m` Fourier amplitudes

The trigonometric transform of a field with all polynomial moments is smooth. Here the same
argument is run with the moments of order `≤ n` only: the transform of a
field with integrable moments of order `≤ m` is `C^m`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CycleWords.Assembly
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard.BandDatum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The moments of order `≤ n` are integrable. -/
def FinMom (n : ℕ) (g : Vec 2 → E) : Prop :=
  ∀ β ∈ momentIndices n, Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • g y)

theorem FinMom.integrable {n : ℕ} {g : Vec 2 → E} (hg : FinMom n g) : Integrable g := by
  have := hg (0, 0) (by simp [momentIndices])
  simpa only [pow_zero, one_mul, one_smul] using this

theorem FinMom.mono {n n' : ℕ} (hn : n ≤ n') {g : Vec 2 → E} (hg : FinMom n' g) : FinMom n g :=
  fun β hβ => hg β (by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ ⊢
    omega)

theorem FinMom.neg {n : ℕ} {g : Vec 2 → E} (hg : FinMom n g) : FinMom n (-g) := by
  intro β hβ
  convert (hg β hβ).neg using 1
  funext y
  exact smul_neg _ _

theorem FinMom.coord {n : ℕ} {g : Vec 2 → E} (hg : FinMom (n + 1) g) (i : Fin 2) :
    FinMom n (fun y => y i • g y) := by
  intro β hβ
  simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ
  fin_cases i
  · convert hg (β.1 + 1, β.2) (by
      simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega) using 1
    funext y
    simp only [smul_smul, pow_succ, Fin.zero_eta]
    congr 1
    ring
  · convert hg (β.1, β.2 + 1) (by
      simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega) using 1
    funext y
    simp only [smul_smul, pow_succ, Fin.mk_one]
    congr 1
    ring

theorem finMom_zero {n : ℕ} : FinMom n (0 : Vec 2 → E) := by
  intro β _
  simp

private theorem finMom_phase_integrable {g : Vec 2 → E} (hg : Integrable g)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hb : ∀ z, |ψ z| ≤ 1) (θ : Vec 2) :
    Integrable (fun y => ψ (vecDot y θ) • g y) := by
  apply hg.norm.mono'
    ((hψ.comp (by unfold vecDot; fun_prop)).aestronglyMeasurable.smul hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖ψ (vecDot y θ) • g y‖ ≤ ‖g y‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb _))

private theorem finMom_pair_integrable {A B : Vec 2 → E} (hA : Integrable A) (hB : Integrable B)
    (θ : Vec 2) : Integrable (fun y => Real.cos (vecDot y θ) • A y + Real.sin (vecDot y θ) • B y) :=
  (finMom_phase_integrable hA Real.cos Real.continuous_cos Real.abs_cos_le_one θ).add
    (finMom_phase_integrable hB Real.sin Real.continuous_sin Real.abs_sin_le_one θ)

private theorem finMom_deriv_integrable {A B : Vec 2 → E}
    (hA : FinMom 1 A) (hB : FinMom 1 B) (θ : Vec 2) :
    Integrable (fun y => ampIntegrandDeriv A B θ y) := by
  unfold ampIntegrandDeriv
  refine integrable_finsetSum (f := fun i y => coordSmulRight (E := E) i
    (Real.cos (vecDot y θ) • derivAmpA i B y + Real.sin (vecDot y θ) • derivAmpB i A y))
    Finset.univ (fun i _ => ?_)
  exact (coordSmulRight (E := E) i).integrable_comp (finMom_pair_integrable
    (hB.coord i).integrable (hA.coord i).neg.integrable θ)

private theorem finMom_deriv_bound (A B : Vec 2 → E) (θ y : Vec 2) :
    ‖ampIntegrandDeriv A B θ y‖ ≤
      ∑ i : Fin 2, (‖derivAmpA i B y‖ + ‖derivAmpB i A y‖) := by
  unfold ampIntegrandDeriv
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  refine (norm_coordSmulRight_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

variable [CompleteSpace E]

/-- The full-space trigonometric integral. -/
def phasePair (A B : Vec 2 → E) (θ : Vec 2) : E :=
  ∫ y, Real.cos (vecDot y θ) • A y + Real.sin (vecDot y θ) • B y

/-- Differentiation under the integral is justified by the moments of order `≤ 1`. -/
theorem phasePair_hasFDerivAt {A B : Vec 2 → E} (hA : FinMom 1 A) (hB : FinMom 1 B) (θ : Vec 2) :
    HasFDerivAt (phasePair A B)
      (∑ i : Fin 2, coordSmulRight i (phasePair (derivAmpA i B) (derivAmpB i A) θ)) θ := by
  have hi (i : Fin 2) : Integrable (fun y => coordSmulRight (E := E) i
      (Real.cos (vecDot y θ) • derivAmpA i B y + Real.sin (vecDot y θ) • derivAmpB i A y)) :=
    (coordSmulRight (E := E) i).integrable_comp
      (finMom_pair_integrable (hB.coord i).integrable (hA.coord i).neg.integrable θ)
  have he : (∫ y, ampIntegrandDeriv A B θ y) =
      ∑ i : Fin 2, coordSmulRight i (phasePair (derivAmpA i B) (derivAmpB i A) θ) := by
    rw [show (fun y => ampIntegrandDeriv A B θ y) = (fun y => ∑ i : Fin 2,
      coordSmulRight i (Real.cos (vecDot y θ) • derivAmpA i B y +
        Real.sin (vecDot y θ) • derivAmpB i A y)) from rfl, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (coordSmulRight (E := E) i).integral_comp_comm
      (finMom_pair_integrable (hB.coord i).integrable (hA.coord i).neg.integrable θ)
  rw [← he]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (bound := fun y => ∑ i : Fin 2, (‖derivAmpA i B y‖ + ‖derivAmpB i A y‖)) Filter.univ_mem
    (Filter.Eventually.of_forall (fun θ' =>
      (finMom_pair_integrable hA.integrable hB.integrable θ').aestronglyMeasurable))
    (finMom_pair_integrable hA.integrable hB.integrable θ)
    (finMom_deriv_integrable hA hB θ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y θ' _ => finMom_deriv_bound A B θ' y))
    (integrable_finsetSum _ (fun i _ =>
      (hB.coord i).integrable.norm.add (hA.coord i).neg.integrable.norm))
    (Filter.Eventually.of_forall (fun y θ' _ => hasFDerivAt_ampIntegrand A B y θ'))

/-- The moments of order `≤ m` give a `C^m` transform. -/
theorem phasePair_contDiff : ∀ (m : ℕ) {A B : Vec 2 → E},
    FinMom m A → FinMom m B → ContDiff ℝ m (phasePair A B)
  | 0, A, B, hA, hB => by
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun y => ‖A y‖ + ‖B y‖)
      (fun θ => (finMom_pair_integrable hA.integrable hB.integrable θ).aestronglyMeasurable)
      (fun θ => Filter.Eventually.of_forall fun y => ?_)
      (hA.integrable.norm.add hB.integrable.norm)
      (Filter.Eventually.of_forall fun y => ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
    · have hd : Continuous fun θ : Vec 2 => vecDot y θ := by unfold vecDot; fun_prop
      exact ((Real.continuous_cos.comp hd).smul continuous_const).add
        ((Real.continuous_sin.comp hd).smul continuous_const)
  | m + 1, A, B, hA, hB => by
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun θ => (phasePair_hasFDerivAt (hA.mono (by omega)) (hB.mono (by omega)) θ).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    rw [show fderiv ℝ (phasePair A B) = fun θ =>
      ∑ i : Fin 2, coordSmulRight i (phasePair (derivAmpA i B) (derivAmpB i A) θ) from
      funext (fun θ => (phasePair_hasFDerivAt (hA.mono (by omega)) (hB.mono (by omega)) θ).fderiv)]
    exact ContDiff.sum (fun i _ => (coordSmulRight (E := E) i).contDiff.comp
      (phasePair_contDiff m (hB.coord i) (hA.coord i).neg))

private theorem finMom_vecDot_comm (θ y : Vec 2) : vecDot θ y = vecDot y θ := by
  unfold vecDot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem finMom_cos_contDiff {m : ℕ} {g : Vec 2 → E} (hg : FinMom m g) :
    ContDiff ℝ m (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) := by
  have he : (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) = phasePair g 0 := by
    funext θ
    simp only [phasePair, Pi.zero_apply, smul_zero, add_zero, finMom_vecDot_comm θ]
  rw [he]
  exact phasePair_contDiff m hg finMom_zero

theorem finMom_sin_contDiff {m : ℕ} {g : Vec 2 → E} (hg : FinMom m g) :
    ContDiff ℝ m (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) := by
  have he : (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) = phasePair 0 g := by
    funext θ
    simp only [phasePair, Pi.zero_apply, smul_zero, zero_add, finMom_vecDot_comm θ]
  rw [he]
  exact phasePair_contDiff m finMom_zero hg

universe u v

/-- **Step 1**: representation and smoothness of the cutoff amplitudes. -/
theorem bandRepStatement : BandRepStatement.{u, v} := by
  intro m ι _ h _ _ _ _ _ _ μ hμ hsupp U hmeas hint x
  have hg : FinMom m (U x) := hint x
  have hzero : ∀ θ : Vec 2, (Real.pi / 2) ^ 2 < vecDot θ θ → μ θ = 0 := fun θ hθ => by
    by_contra hne
    exact absurd (hsupp θ hne) (not_le.2 hθ)
  have hcpt : HasCompactSupport μ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) (Real.pi / 2)) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    refine hzero z ?_
    have h1 := norm_le_sqrt_vecDot z
    have h2 : Real.pi / 2 < Real.sqrt (vecDot z z) := hz.trans_le h1
    by_contra hcon
    exact absurd h2 (not_lt.2 (Real.sqrt_le_left (by positivity) |>.2 (not_lt.1 hcon)))
  have hcos : ContDiff ℝ m (cutoffCosAmplitude μ (U x)) :=
    (contDiff_const.mul (hμ.of_le (by exact_mod_cast le_top))).smul (finMom_cos_contDiff hg)
  have hsin : ContDiff ℝ m (cutoffSinAmplitude μ (U x)) :=
    (contDiff_const.mul (hμ.of_le (by exact_mod_cast le_top))).smul (finMom_sin_contDiff hg)
  have hv : ∀ θ : Vec 2, (Real.pi / 2) ^ 2 < vecDot θ θ →
      cutoffCosAmplitude μ (U x) θ = 0 ∧ cutoffSinAmplitude μ (U x) θ = 0 := fun θ hθ => by
    simp only [cutoffCosAmplitude, cutoffSinAmplitude, hzero θ hθ, mul_zero, zero_smul, and_self]
  refine ⟨⟨hcos, fun θ hθ => (hv θ hθ).1⟩, ⟨hsin, fun θ hθ => (hv θ hθ).2⟩, fun z => ?_⟩
  rw [factorFourierCutoff_eq_integral hμ.continuous
    (hμ.continuous.integrable_of_hasCompactSupport hcpt) hg.integrable]
  unfold ampFun
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro θ hθ
  have hn : (Real.pi / 2) ^ 2 < vecDot θ θ := lt_of_not_ge hθ
  simp only [cutoffCosAmplitude, cutoffSinAmplitude, hzero θ hn, mul_zero, zero_smul, smul_zero,
    add_zero]

end AVRegularity.CycleWords.Discard.BandDatum
end
end
end
