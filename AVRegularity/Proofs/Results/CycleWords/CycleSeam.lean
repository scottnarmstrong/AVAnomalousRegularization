-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.MixedWordsOfBandJet
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.Seam.S3CycleSeam
import AVRegularity.CycleWords.Seam.B1PlainStage
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_mixed_words`.

`cycle_mixed_words` is `cycle_mixed_words_of_ingredients` (`Assembly/CycleMixedWordsOfIngredients`)
at the four statements of `mixedWordsIngredients_of_bandJet` (the retained map, the model jets,
the chain discard and the Gaussian amplitude) at the band
jet (`bandJetStatement`), and the full-field bound on rough data `chainFullField`. -/

/-- **Finite-word extraction** (Lemma 11.12 of the paper). -/
theorem cycle_mixed_words (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ (χlo : Vec 2 → ℝ)
    (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χlo) (_hχ_even : ∀ ξ, χlo (-ξ) = χlo ξ)
    (_hχ_one : ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ K.ξlo → χlo ξ = 1)
    (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χlo ξ = 0)
    (Nw D H Kf m : ℕ) (_hD : 2 ≤ D)
    (Cout : ℝ) (_hCout : 0 < Cout) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
    ∃ (C c CGa cGa : ℝ) (Q : ℕ) (CM : ℕ → ℝ), 0 < C ∧ 0 < c ∧ 0 < CGa ∧ 0 < cGa ∧
      (∀ M, 0 < CM M) ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (letters : Fin Nw → CycleLetter ι h D)
        (_hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
          (letters i).positive = pos i)
        (η S ηg rstar t₀ ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
        (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout)
        (_hϖ : ϖ = Real.sqrt (η / S))
        (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
        (_hGm : IsCellMetric (fun t _ => G t)) (_hv : IsCellDrift v)
        (_hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0)
        (_hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
        (_hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j)
        (_hg0 : 0 ≤ g) (_hg : g ≤ K.g0) (_hg₁ : g ≤ g₁)
        (_hGn : IsMetricNearIdentity (fun t _ => G t) g)
        (reg : BlockRegions) (_pkg : ScalarPackage K η G v t₀ S ϖ reg)
        (_hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc t₀ (t₀ + S) ×ˢ Set.univ)
          (wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d) H)
        (_htrans : ∀ i, IsTransverseOnPulses (letters i).edge
          (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient)
        (_hquiet : ∀ i, IsQuietOn (letters i).edge v reg.quiet)
        (_hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
          Measurable fun t => γ.coeff α t X z)
        (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ) (_hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x)
        (_hκ : ∀ (j : Fin Nw) x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
          κ j.succ x + o.1 ≤ κ j.castSucc y + 2),
      ∃ P : (∀ x, PlaneHk Set.univ (κ 0 x) (h x)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        (∀ f x, (∀ M : ℕ, ContDiff ℝ M (P f x)) ∧
          HasFourierSupportIn (P f x) (2 * K.ξlo * Real.sqrt η)) ∧
        (∀ (M : ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)),
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
          weightedJetNorm π (m : ℝ) M ϖ ϖ⁻¹
              (fun x _ wd z => orderedDerivative wd (P f x) z) ≤
            ENNReal.ofReal (CM M * wordTheta ηg letters) *
              momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ∧
        (∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
          (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
          (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
          IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
            (fun _ _ _ => 0) u w →
          jetOutputNorm π m Kf ϖ rstar
              (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
                orderedDerivative wd (P f x) z) ≤
            ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
                (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer))) *
              momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ∧
        (∀ f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x),
          momentNorm π (wordReserveN m Ks + 2) ϖ (fun x => planeValue (f x)) < ⊤ →
          ∃ A B : ∀ x, Vec 2 → h x,
            (∀ x, IsRetainedAmplitude (P f x) (2 * K.ξlo * Real.sqrt η) (A x) (B x)) ∧
            (∀ x, ContDiff ℝ m (A x) ∧ ContDiff ℝ m (B x)) ∧
            (∀ x θ, A x (-θ) = A x θ ∧ B x (-θ) = -B x θ) ∧
            ∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
              amplitudeJetNorm π m ϖ A B θ ≤
                ENNReal.ofReal (CGa * wordTheta ηg letters *
                    (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ wordReserveP m Ks *
                    Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
                  ∑ α ∈ momentIndices (wordReserveN m Ks),
                    ENNReal.ofReal (ϖ ^ (α.1 + α.2) /
                        ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                      blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α
                        (fun x => planeValue (f x)) θ) :=
  CycleWords.Assembly.cycle_mixed_words_of_ingredients
    (CycleWords.Discard.mixedWordsIngredients_of_bandJet
      CycleWords.Discard.BandJets.bandJetStatement).1
    (CycleWords.Discard.mixedWordsIngredients_of_bandJet
      CycleWords.Discard.BandJets.bandJetStatement).2.1
    (CycleWords.Discard.mixedWordsIngredients_of_bandJet
      CycleWords.Discard.BandJets.bandJetStatement).2.2.1
    (CycleWords.Discard.mixedWordsIngredients_of_bandJet
      CycleWords.Discard.BandJets.bandJetStatement).2.2.2
    CycleWords.Discard.chainFullField K

/-! Proof of `cycle_seam`.

`cycle_seam` is `cycleSeamStatement_of_quietMarginDatum` (module `CycleWords.Seam.S3CycleSeam`: the five
seam ingredients of `cycle_seam_of_ingredients`, with the future kernel from `seamGaussianNeg`,
`seamLowPassMoment`, the chain discard, `b1_quietMarginFibre`, `cellLowPassMoment`) at `quietMarginDatum`. -/

/-- **The seam** (Lemma 11.15 of the paper). -/
theorem cycle_seam (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ (D H Kmax pout k : ℕ) (_hD : 2 ≤ D) (Nm Np : ℕ) (dO KsO : Fin Nm → ℕ) (posO : Fin Nm → Bool)
      (dF KsF : Fin Np → ℕ) (posF : Fin Np → Bool) (_hk : Kmax + ∑ i, dO i + 2 ≤ k),
    ∃ Q : ℕ, ∀ Mmod Nmod : ℕ, ∃ qΥ : ℕ,
    ∀ (Cout C0 Cs CU CH : ℝ) (_hCout : 0 < Cout) (_hCH : 0 < CH) (χm : Vec 2 → ℝ)
      (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χm) (_hχ_even : ∀ ξ, χm (-ξ) = χm ξ)
      (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
      (_hχ_one : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1),
    ∃ (c : ℝ) (CM CN : ℕ → ℝ), 0 < c ∧ (∀ M, 0 < CM M) ∧ (∀ N, 0 < CN N) ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (lettersF : Fin Np → CycleLetter ι h D)
        (_hlF : ∀ i, (lettersF i).order = dF i ∧ (lettersF i).slow = KsF i ∧
          (lettersF i).positive = posF i)
        -- the common scales
        (η S ηg rstar ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
        (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout)
        (_hϖ : ϖ = Real.sqrt (η / S))
        -- the future complete block
        (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ)
        (_hGmF : IsCellMetric (fun t _ => GF t)) (_hvF : IsCellDrift vF)
        (_hv0F : ∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0)
        (_hvsF : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t))
        (_hvwF : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ K.Cw)
        (_hvjF : ∀ (j : ℕ) t z,
          ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ K.Cvj j)
        (_hg0F : 0 ≤ gF) (_hgF : gF ≤ K.g0) (_hg₁F : gF ≤ g₁)
        (_hGnF : IsMetricNearIdentity (fun t _ => GF t) gF)
        (regF : BlockRegions) (_pkgF : ScalarPackage K η GF vF tF S ϖ regF)
        (_hletF : ∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ)
          (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
            max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
        (_htransF : ∀ i, IsTransverseOnPulses (lettersF i).edge
          (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient)
        (_hquietF : ∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S)))
        (_hmeasF : ∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
          Measurable fun t => γ.coeff α t X z)
        (a : ℝ) (_ha : 0 ≤ a) (_haS : a ≤ S) (_hquietMargin : Set.Icc tF (tF + a) ⊆ regF.quiet)
        (X₀F : Vec 2)
        (_hC0 : peFactor η ^ Q * (1 + S) ^ Q * (1 + regF.joins) *
          Real.exp (-c * regF.buffer) ≤ C0),
      ∃ Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        -- the future slots and output orders (the kernel is uniform in them), the old
        -- letters, the chart transition and the old partial piece
        ∀ (κF : Fin (Np + 1) → ι → ℕ) (Kout : ι → ℕ) (_hKout : ∀ x, Kout x ≤ Kmax)
          (_hκFf : ∀ x, Kout x ≤ κF (Fin.last Np) x)
          (_hκF : ∀ (j : Fin Np) x y (o : Finset.Icc 2 D), (lettersF j).edge x y o ≠ [] →
            κF j.succ x + o.1 ≤ κF j.castSucc y + 2)
          (lettersO : Fin Nm → CycleLetter ι h D)
          (_hlO : ∀ i, (lettersO i).order = dO i ∧ (lettersO i).slow = KsO i ∧
            (lettersO i).positive = posO i)
          (Υ Υinv : Vec 2 → Vec 2) (gU δ : ℝ) (_hδ : δ = ϖ * ηg)
          (_hgU : 0 ≤ gU ∧ gU ≤ K.g0) (_hΥ : IsCenteredTransition Υ Υinv gU δ CU qΥ)
          (_hΥs : ContDiff ℝ (⊤ : ℕ∞) Υinv)
          (tO SO aO bO : ℝ) (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vO : ℝ → Vec 2 → Vec 2) (gO : ℝ)
          (_hGmO : IsCellMetric (fun t _ => GO t)) (_hvO : IsCellDrift vO)
          (_hv0O : ∀ t (k : Fin 2), cellMean (fun x => (vO t x k : ℂ)) = 0)
          (_hvsO : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vO t))
          (_hvwO : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vO t x i ^ 2) ≤ K.Cw)
          (_hvjO : ∀ (j : ℕ) t z,
            ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vO t z') z‖ ≤ K.Cvj j)
          (_hg0O : 0 ≤ gO) (_hgO : gO ≤ K.g0) (_hg₁O : gO ≤ g₁)
          (_hGnO : IsMetricNearIdentity (fun t _ => GO t) gO)
          (regO : BlockRegions) (_pkgO : CoreScalarPackage K η GO vO tO SO ϖ regO)
          (_hwin : tO ≤ aO ∧ aO ≤ bO ∧ bO ≤ tO + SO) (_hdur : bO - aO ≤ CH * S)
          (_hC0O : peFactor η ^ Q * (1 + S) ^ Q * (1 + regO.joins) *
            Real.exp (-c * regO.buffer) ≤ C0)
          (_hseam : Set.Icc (bO - regF.buffer) bO ⊆ regO.quiet ∩ Set.Icc tO (tO + SO))
          (_hletO : ∀ i, IsCycleLetter π (lettersO i) (Set.Icc aO bO ×ˢ Set.univ)
            (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
              max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
          (_htransO : ∀ i, IsTransverseOnPulses (lettersO i).edge
            (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p)) regO.orient)
          (_hquietO : ∀ i, IsQuietOn (lettersO i).edge vO (regO.quiet ∩ Set.Icc tO (tO + SO)))
          (_hmeasO : ∀ i x y o, ∀ γ ∈ (lettersO i).edge x y o, ∀ α X z,
            Measurable fun t => γ.coeff α t X z)
          (X₀O : Vec 2) (κO : Fin (Nm + 1) → ι → ℕ)
          (_hκO : ∀ (j : Fin Nm) x y (o : Finset.Icc 2 D), (lettersO j).edge x y o ≠ [] →
            κO j.succ x + o.1 ≤ κO j.castSucc y + 2)
          (_hκmatch : ∀ x, κF 0 x ≤ κO (Fin.last Nm) x)
          (f : ∀ x, PlaneHk Set.univ (κO 0 x) (h x))
          (_hfsupp : ∀ x, ∀ᵐ z : Vec 2 ∂volume, (Cs / ϖ) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
            planeValue (f x) z = 0)
          (uO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x) (h x))
          (wO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x + 1) (h x))
          (_hchainO : IsPlaneChain (wordChainData GO lettersO X₀O δ) κO aO bO vO f
            (fun _j _x _ => 0) uO wO)
          (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
          (_hfF : ∀ x, planeValue (fF x) =ᵐ[volume]
            fun z => planeValue (uO (Fin.last Nm) x bO) (Υ z))
          (uF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
          (wF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x))
          (_hchainF : IsPlaneChain (wordChainData GF lettersF X₀F δ) κF tF (tF + S) vF fF
            (fun _j _x _ => 0) uF wF),
        (∀ x, ∀ M : ℕ, ContDiff ℝ M
          (Kp (fun x' z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
              (planeValue (uO (Fin.last Nm) x' bO)) (Υ z)) x)) ∧
        (∀ M : ℕ, M ≤ Mmod →
          weightedJetNorm π (pout : ℝ) M ϖ ϖ⁻¹
              (fun x _a' wd z => orderedDerivative wd
                (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                  (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z) ≤
            ENNReal.ofReal (CM M * (wordTheta ηg lettersO * wordTheta ηg lettersF)) *
              momentNorm π 0 ϖ (fun x => planeValue (f x))) ∧
        (∀ N : ℕ, 1 ≤ N → N ≤ Nmod →
          weightedJetNorm π (pout : ℝ) Kmax ϖ rstar
              (fun x a' wd z => if a' ≤ Kout x then
                planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
                orderedDerivative wd
                  (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                    (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z else 0) ≤
            ENNReal.ofReal (CN N * (wordTheta ηg lettersO * wordTheta ηg lettersF) *
                peFactor η ^ Q * (1 + S) ^ Q *
                (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
                  Real.exp (-c * a) + S ^ (-(N : ℝ) / 2))) *
              momentNorm π 0 ϖ (fun x => planeValue (f x))) :=
  CycleWords.Seam.cycleSeamStatement_of_quietMarginDatum CycleWords.Seam.quietMarginDatum K

end AVRegularity.Providers
end
