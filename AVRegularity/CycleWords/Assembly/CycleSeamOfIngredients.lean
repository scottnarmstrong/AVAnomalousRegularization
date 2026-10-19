-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.SeamNorms
import AVRegularity.CycleWords.Seam.B1PlainStage
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

/-! Conditional assembly of `cycle_seam` from the five seam ingredients `SeamOldNegativeStatement`,
`SeamOldScalarStatement`, `SeamFutureKernelStatement`, `SeamTransportStatement` and
`SeamCutoffComplementStatement`.

With `g = V₋f` the old output, `Π₋ = χ₋(θ/√η)` and `𝒯_Υ g = g ∘ Υ`, the model is
`K₊𝒯_ΥΠ₋g` with `K₊` the future retained kernel, and
`Z₊𝒯_Υg - K₊𝒯_ΥΠ₋g = (Z₊ - K₊)𝒯_Υg + K₊𝒯_Υ(I - Π₋)g`. The model bound composes the kernel
bound, the transport and the old scalar bound; the first error term composes the fast remainder,
the transport and the old negative bound; the second the kernel bound, the transport, the cutoff
complement and the old negative bound. Supported data have weighted `L²` norm bounded by their
`L²` norm. The constants are `g₁ = min` of the ingredients' thresholds, `Q = Q₁ + Q₂ + Q₃`
(shape only), `qΥ = max(m₋, k + N_mod)` (the transport orders `m₋`, `k` and `N + k`, `N ≤ N_mod`)
and `c = min c₂ c₃`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

theorem sqrt_vecDot_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (x : Vec 2) :
    Real.sqrt (vecDot (c • x) (c • x)) = c * Real.sqrt (vecDot x x) := by
  have hx : vecDot (c • x) (c • x) = c ^ 2 * vecDot x x := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  rw [hx, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The rescaled cutoff vanishes outside the disc of radius `√η ξ₀`. -/
theorem seam_cutoff_multiplier_support (χm : Vec 2 → ℝ) (ξ0 η : ℝ) (hη : 0 < η)
    (hχ : ∀ ξ, ξ0 ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) :
    ∀ θ, Real.sqrt η * ξ0 ≤ Real.sqrt (vecDot θ θ) → χm ((Real.sqrt η)⁻¹ • θ) = 0 := by
  intro θ hθ
  apply hχ
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  rw [sqrt_vecDot_smul_of_nonneg _ (inv_nonneg.mpr hs.le)]
  rw [le_inv_mul_iff₀ hs]
  exact hθ

/-- Four composed bounds with real prices. -/
theorem ennreal_chain4 {A B C D E : ℝ≥0∞} {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : A ≤ ENNReal.ofReal a * B) (h2 : B ≤ ENNReal.ofReal b * C)
    (h3 : C ≤ ENNReal.ofReal c * D) (h4 : D ≤ ENNReal.ofReal d * E) :
    A ≤ ENNReal.ofReal (a * b * c * d) * E := by
  calc A ≤ ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * (ENNReal.ofReal d * E))) :=
        h1.trans (by gcongr; exact h2.trans (by gcongr; exact h3.trans (by gcongr)))
    _ = ENNReal.ofReal (a * b * c * d) * E := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc),
          ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha]
        ring

/-- The price comparison of the error terms. -/
theorem seam_error_price {A₁ A₂ Θ P P₁ P₃ E₃ Ec s : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hΘ : 0 ≤ Θ) (hP₁ : 0 ≤ P₁) (hP₁P : P₁ ≤ P) (hP₁₃ : P₁ * P₃ ≤ P)
    (hE₃ : 0 ≤ E₃) (hE : E₃ ≤ Ec) (hs : 0 ≤ s) :
    A₁ * (Θ * (P₁ * P₃ * E₃)) + A₂ * (Θ * (P₁ * s)) ≤ (A₁ + A₂ + 1) * Θ * P * (Ec + s) := by
  have hEc : 0 ≤ Ec := hE₃.trans hE
  have hP : 0 ≤ P := hP₁.trans hP₁P
  have h1 : P₁ * P₃ * E₃ ≤ P * (Ec + s) :=
    mul_le_mul hP₁₃ (hE.trans (le_add_of_nonneg_right hs)) hE₃ hP
  have h2 : P₁ * s ≤ P * (Ec + s) :=
    mul_le_mul hP₁P (le_add_of_nonneg_left hEc) hs hP
  have hX : 0 ≤ Θ * (P * (Ec + s)) := mul_nonneg hΘ (mul_nonneg hP (add_nonneg hEc hs))
  calc A₁ * (Θ * (P₁ * P₃ * E₃)) + A₂ * (Θ * (P₁ * s))
      ≤ A₁ * (Θ * (P * (Ec + s))) + A₂ * (Θ * (P * (Ec + s))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hΘ) hA₁
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hΘ) hA₂
    _ ≤ A₁ * (Θ * (P * (Ec + s))) + A₂ * (Θ * (P * (Ec + s))) + 1 * (Θ * (P * (Ec + s))) :=
        le_add_of_nonneg_right (by rw [one_mul]; exact hX)
    _ = (A₁ + A₂ + 1) * Θ * P * (Ec + s) := by ring

theorem seam_power_le {Pe S : ℝ} (hPe : 1 ≤ Pe) (hS : 0 ≤ S) {Q₁ Q : ℕ} (hQ : Q₁ ≤ Q) :
    Pe ^ Q₁ * (1 + S) ^ Q₁ ≤ Pe ^ Q * (1 + S) ^ Q :=
  mul_le_mul (pow_le_pow_right₀ hPe hQ) (pow_le_pow_right₀ (by linarith) hQ)
    (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)

/-- The block scale factor at a smaller power and a larger rate. -/
theorem seam_block_scale_le {Pe S J B c₁ c : ℝ} (hPe : 1 ≤ Pe) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hB : 0 ≤ B) (hc : c ≤ c₁) {Q₁ Q : ℕ} (hQ : Q₁ ≤ Q) :
    Pe ^ Q₁ * (1 + S) ^ Q₁ * (1 + J) * Real.exp (-c₁ * B) ≤
      Pe ^ Q * (1 + S) ^ Q * (1 + J) * Real.exp (-c * B) := by
  have hP := seam_power_le hPe hS hQ
  have hexp : Real.exp (-c₁ * B) ≤ Real.exp (-c * B) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hc hB
    linarith
  have h0 : 0 ≤ Pe ^ Q * (1 + S) ^ Q * (1 + J) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
      (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by linarith)) hexp (Real.exp_pos _).le h0

theorem seam_power_add {Pe S : ℝ} (Q₁ Q₃ : ℕ) :
    Pe ^ Q₁ * (1 + S) ^ Q₁ * (Pe ^ Q₃ * (1 + S) ^ Q₃) = Pe ^ (Q₁ + Q₃) * (1 + S) ^ (Q₁ + Q₃) := by
  rw [pow_add, pow_add]
  ring

/-- The chain hypothesis in the form of the seam statements (a separate declaration: the two
elaborations of the zero source agree only after unfolding). -/
theorem seamChain_of_isPlaneChain {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D N : ℕ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hc : IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) u w) :
    seamChain G letters X₀ δ κ a b v f u w :=
  hc

/-- **`cycle_seam` from its ingredients.** The exact statement from the five seam
ingredients (a conditional helper). -/
theorem cycle_seam_of_ingredients
    (hold : SeamOldNegativeStatement.{u, v}) (hscalar : SeamOldScalarStatement.{u, v})
    (hfut : SeamFutureKernelStatement.{u, v}) (htrans : SeamTransportStatement.{u, v})
    (hcut : SeamCutoffComplementStatement.{u, v}) (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ (D H Kmax pout k : ℕ) (_hD : 2 ≤ D) (Nm Np : ℕ) (dO KsO : Fin Nm → ℕ) (posO : Fin Nm → Bool)
      (dF KsF : Fin Np → ℕ) (posF : Fin Np → Bool) (_hk : Kmax + ∑ i, dO i + 2 ≤ k),
    ∃ Q : ℕ, ∀ Mmod Nmod : ℕ, ∃ qΥ : ℕ,
    ∀ (Cout C0 Cs CU CH : ℝ) (_hCout : 0 < Cout) (_hCH : 0 < CH) (χm : Vec 2 → ℝ)
      (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χm) (_hχ_even : ∀ ξ, χm (-ξ) = χm ξ)
      (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
      (_hχ_one : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1),
    ∃ (c : ℝ) (CM CN : ℕ → ℝ), 0 < c ∧ (∀ M, 0 < CM M) ∧ (∀ N, 0 < CN N) ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (lettersF : Fin Np → CycleLetter ι h D)
        (_hlF : ∀ i, (lettersF i).order = dF i ∧ (lettersF i).slow = KsF i ∧
          (lettersF i).positive = posF i)
        -- the common scales
        (η S ηg rstar ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
        (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout) (_hϖ : ϖ = Real.sqrt (η / S))
        -- the future complete block
        (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ)
        (_hGmF : IsCellMetric (fun t _ => GF t)) (_hvF : IsCellDrift vF)
        (_hv0F : ∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0)
        (_hvsF : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t))
        (_hvwF : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ K.Cw)
        (_hvjF : ∀ (j : ℕ) t z,
          ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ K.Cvj j)
        (_hg0F : 0 ≤ gF) (_hgF : gF ≤ K.g0) (_hg₁F : gF ≤ g₁) (_hGnF : IsMetricNearIdentity (fun t _ => GF t) gF)
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
          (_hg0O : 0 ≤ gO) (_hgO : gO ≤ K.g0) (_hg₁O : gO ≤ g₁) (_hGnO : IsMetricNearIdentity (fun t _ => GO t) gO)
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
            (fun _ _ _ => 0) uO wO)
          (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
          (_hfF : ∀ x, planeValue (fF x) =ᵐ[volume]
            fun z => planeValue (uO (Fin.last Nm) x bO) (Υ z))
          (uF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
          (wF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x))
          (_hchainF : IsPlaneChain (wordChainData GF lettersF X₀F δ) κF tF (tF + S) vF fF
            (fun _ _ _ => 0) uF wF),
        (∀ x, ∀ M : ℕ, ContDiff ℝ M
          (Kp (fun x' z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
              (planeValue (uO (Fin.last Nm) x' bO)) (Υ z)) x)) ∧
        (∀ M : ℕ, M ≤ Mmod →
          weightedJetNorm π (pout : ℝ) M ϖ ϖ⁻¹
              (fun x _ wd z => orderedDerivative wd
                (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                  (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z) ≤
            ENNReal.ofReal (CM M * (wordTheta ηg lettersO * wordTheta ηg lettersF)) *
              momentNorm π 0 ϖ (fun x => planeValue (f x))) ∧
        (∀ N : ℕ, 1 ≤ N → N ≤ Nmod →
          weightedJetNorm π (pout : ℝ) Kmax ϖ rstar
              (fun x a' wd z => if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
                orderedDerivative wd
                  (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                    (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z else 0) ≤
            ENNReal.ofReal (CN N * (wordTheta ηg lettersO * wordTheta ηg lettersF) *
                peFactor η ^ Q * (1 + S) ^ Q *
                (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
                  Real.exp (-c * a) + S ^ (-(N : ℝ) / 2))) *
              momentNorm π 0 ϖ (fun x => planeValue (f x))) := by
  classical
  obtain ⟨g1a, hg1a, hold'⟩ := hold K
  obtain ⟨g1b, hg1b, hscalar'⟩ := hscalar K
  obtain ⟨g1c, hg1c, hfut'⟩ := hfut K
  refine ⟨min g1a (min g1b g1c), lt_min hg1a (lt_min hg1b hg1c), ?_⟩
  intro D H Kmax pout k hD Nm Np dO KsO posO dF KsF posF hk
  have hgA : min g1a (min g1b g1c) ≤ g1a := min_le_left _ _
  have hgB : min g1a (min g1b g1c) ≤ g1b := (min_le_right _ _).trans (min_le_left _ _)
  have hgC : min g1a (min g1b g1c) ≤ g1c := (min_le_right _ _).trans (min_le_right _ _)
  let σ : SeamShape := ⟨K, D, H, Kmax, pout, k, Nm, Np, dO, KsO, posO, dF, KsF, posF, hD, hk⟩
  -- the integer orders: from the shape only
  obtain ⟨pin, Q3, hpin, hfutQ⟩ := hfut' σ rfl
  obtain ⟨m, q, Q2, hscalarQ⟩ := hscalar' σ rfl pin (by omega)
  obtain ⟨Q1, holdQ⟩ := hold' σ rfl
  have hk2 : 2 ≤ k := by omega
  refine ⟨Q1 + Q2 + Q3, fun Mmod Nmod => ⟨max m (k + Nmod), ?_⟩⟩
  have hq2 : 2 ≤ max m (k + Nmod) := le_max_of_le_right (by omega)
  have hqm : max m 2 ≤ max m (k + Nmod) := max_le (le_max_left _ _) hq2
  have hqk : max k 2 ≤ max m (k + Nmod) := max_le (le_max_of_le_right (by omega)) hq2
  have hqN : ∀ N, N ≤ Nmod → max (N + k) 2 ≤ max m (k + Nmod) := fun N hN =>
    max_le (le_max_of_le_right (by omega)) hq2
  -- the real constants
  intro Cout C0 Cs CU CH hCout hCH χm hχ_smooth hχ_even hχ_supp hχ_one
  obtain ⟨C3, c3, CK, hC3, hc3, hCK, hfutσ⟩ := hfutQ Cout hCout
  obtain ⟨C2, c2, hC2, hc2, hscalarp⟩ := hscalarQ CH C0 χm hCH hχ_smooth hχ_even hχ_supp hχ_one
  obtain ⟨C4m, hC4m, htransm⟩ := htrans m pin CU K.g0
  obtain ⟨C4k, hC4k, htransk⟩ := htrans k pin CU K.g0
  have hold1 := holdQ CH hCH
  obtain ⟨C1k, hC1k, holdk⟩ := hold1 pin
  choose C4N hC4N htransN using fun N : ℕ => htrans (N + k) pin CU K.g0
  choose C5N hC5N hcutN using fun N : ℕ =>
    hcut (2 * K.ξlo) χm hχ_smooth hχ_even hχ_supp hχ_one k N pin
  choose C1N hC1N holdN using fun N : ℕ => hold1 pin
  have hW : ∀ p : ℕ, 0 ≤ (1 + Cs ^ 2) ^ p := fun p => by positivity
  refine ⟨min c2 c3,
    fun M => CK m M * C4m * C2 * (1 + Cs ^ 2) ^ (pin + q) + 1,
    fun N => C3 * C4k * C1k * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i) +
      CK (N + k) Kmax * C4N N * C5N N * C1N N * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i) + 1,
    lt_min hc2 hc3, fun M => ?_, fun N => ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (mul_nonneg (hCK m M) hC4m) hC2) (hW _)) one_pos
  · exact add_pos_of_nonneg_of_pos (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC3 hC4k) hC1k) (hW _))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hCK _ _) (hC4N N)) (hC5N N)) (hC1N N))
        (hW _))) one_pos
  intro ι _ h _ _ _ _ _ _ π hπ lettersF hlF η S ηg rstar ϖ hη hη1 hS hηg hηg1 hrstar hrstarC hϖ
    tF GF vF gF hGmF hvF hv0F hvsF hvwF hvjF hg0F hgF hg₁F hGnF regF pkgF hletF htransF hquietF
    hmeasF a ha haS hquietMargin X₀F hC0'
  obtain ⟨Kp, hKsmooth, hKkernel, hKfast⟩ := hfutσ π hπ lettersF hlF η S ηg rstar ϖ (ϖ * ηg)
    hη hη1 hS hηg hηg1 hrstar hrstarC hϖ rfl tF GF vF gF hGmF hvF hv0F hvsF hvwF hvjF hg0F hgF
    (hg₁F.trans hgC) hGnF regF pkgF hletF htransF hquietF
    hmeasF a ha haS hquietMargin X₀F
  refine ⟨Kp, ?_⟩
  intro κF Kout hKout hκFf hκF lettersO hlO Υ Υinv gU δ hδ hgU hΥ hΥs tO SO aO bO GO vO gO hGmO
    hvO hv0O hvsO hvwO hvjO hg0O hgO hg₁O hGnO regO pkgO hwin hdur hC0O' hseam hletO htransO hquietO hmeasO X₀O κO hκO _hκmatch f
    hfsupp uO wO hchainO fF hfF uF wF hchainF
  subst hδ
  have hcO := seamChain_of_isPlaneChain GO lettersO X₀O (ϖ * ηg) κO aO bO vO f uO wO hchainO
  -- scales
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hϖpos : 0 < ϖ := hϖ ▸ Real.sqrt_pos.mpr (div_pos hη hSpos)
  have hϖ1 : ϖ ≤ 1 := hϖ ▸ Real.sqrt_le_one.mpr ((div_le_one hSpos).mpr (hη1.trans hS))
  have hϖinv : 1 ≤ ϖ⁻¹ := (one_le_inv₀ hϖpos).mpr hϖ1
  have hPe : 1 ≤ peFactor η := by
    unfold peFactor
    have := inv_nonneg.mpr (Real.sqrt_nonneg η)
    linarith
  have hPe0 : 0 ≤ peFactor η := zero_le_one.trans hPe
  have hrinv : ϖ⁻¹ ≤ max 1 Cout * ϖ⁻¹ :=
    le_mul_of_one_le_left (inv_nonneg.mpr hϖpos.le) (le_max_left _ _)
  have hrstar' : rstar ≤ max 1 Cout * ϖ⁻¹ :=
    hrstarC.trans ((le_max_right 1 Cout).trans
      (le_mul_of_one_le_right (zero_le_one.trans (le_max_left 1 Cout)) hϖinv))
  have hΘO : 0 ≤ wordTheta ηg lettersO :=
    wordTheta_nonneg_of_admissible ηg hηg.le lettersO π _ _ _ hletO
  have hΘF : 0 ≤ wordTheta ηg lettersF :=
    wordTheta_nonneg_of_admissible ηg hηg.le lettersF π _ _ _ hletF
  have hB : 0 ≤ regF.buffer := pkgF.buffer_nonneg
  -- the cutoff, the transport and the data
  have hmχR := seam_cutoff_multiplier_support χm (2 * K.ξlo) η hη hχ_supp
  have hmχs : ContDiff ℝ (⊤ : ℕ∞) (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) :=
    hχ_smooth.comp (contDiff_const_smul _)
  have hΥmp : MeasurePreserving Υ volume volume :=
    centeredTransition_measurePreserving Υ Υinv gU (ϖ * ηg) CU (hΥ.mono hq2)
  have hgOm : ∀ x, MemLp (planeValue (uO (Fin.last Nm) x bO)) 2 volume := fun x =>
    planeValue_memLp _
  have hPi : ∀ x, MemLp (fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
      (planeValue (uO (Fin.last Nm) x bO))) 2 volume := fun x =>
    fourierCutoff_memLp_of_memLp _ _ hmχR hmχs (hgOm x)
  have hG1 : ∀ x, MemLp (fun z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
      (planeValue (uO (Fin.last Nm) x bO)) (Υ z)) 2 volume := fun x =>
    (hPi x).comp_measurePreserving hΥmp
  have hF0 : ∀ x, MemLp (planeValue (fF x)) 2 volume := fun x => planeValue_memLp _
  have hsupp := fun p : ℕ => weightedJetNorm_value_le_of_support π ϖ Cs hϖpos p f hfsupp
  -- the old negative bounds
  have hT1d := holdk π hπ lettersO hlO η S ηg ϖ (ϖ * ηg) hη hη1 hS hηg hηg1 hϖ rfl
    tO SO aO bO GO vO gO hGmO hvO hv0O hvsO hvwO hvjO hg0O hgO
    (hg₁O.trans hgA) hGnO regO pkgO hwin hdur
    hletO htransO hquietO hmeasO X₀O κO hκO f uO wO ⟨Cs / ϖ, hfsupp⟩ hcO
  have hT2e' := fun n : ℕ => holdN n π hπ lettersO hlO η S ηg ϖ (ϖ * ηg) hη hη1 hS hηg hηg1 hϖ
    rfl tO SO aO bO GO vO gO hGmO hvO hv0O hvsO hvwO hvjO hg0O hgO
    (hg₁O.trans hgA) hGnO regO pkgO hwin hdur
    hletO htransO hquietO hmeasO X₀O κO hκO f uO wO ⟨Cs / ϖ, hfsupp⟩ hcO
  refine ⟨fun x M => hKsmooth _ hG1 x M, fun M _hM => ?_, fun n _hn hnmod => ?_⟩
  · -- the model
    have hscale : peFactor η ^ Q2 * (1 + S) ^ Q2 * Real.exp (-c2 * regF.buffer) ≤ C0 := by
      refine le_trans ?_ hC0'
      have hexp : Real.exp (-c2 * regF.buffer) ≤ Real.exp (-(min c2 c3) * regF.buffer) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right (min_le_left c2 c3) hB
        linarith
      have hj : (1 : ℝ) ≤ 1 + regF.joins := le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hP := seam_power_le hPe hSpos.le (show Q2 ≤ Q1 + Q2 + Q3 by omega)
      have hP0 : 0 ≤ peFactor η ^ (Q1 + Q2 + Q3) * (1 + S) ^ (Q1 + Q2 + Q3) :=
        mul_nonneg (pow_nonneg hPe0 _) (pow_nonneg (by linarith) _)
      calc peFactor η ^ Q2 * (1 + S) ^ Q2 * Real.exp (-c2 * regF.buffer)
          ≤ peFactor η ^ (Q1 + Q2 + Q3) * (1 + S) ^ (Q1 + Q2 + Q3) * 1 *
              Real.exp (-(min c2 c3) * regF.buffer) := by
            rw [mul_one]
            exact mul_le_mul hP hexp (Real.exp_pos _).le hP0
        _ ≤ peFactor η ^ (Q1 + Q2 + Q3) * (1 + S) ^ (Q1 + Q2 + Q3) * (1 + regF.joins) *
              Real.exp (-(min c2 c3) * regF.buffer) := by
            gcongr
    have h1 := hKkernel m M ϖ⁻¹ _ (inv_pos.mpr hϖpos) hrinv hG1
    have h2 := htransm π hπ Υ Υinv gU (ϖ * ηg) ϖ ηg ϖ⁻¹ hgU.1 hgU.2 (hΥ.mono hqm) hΥs hϖpos hϖ1 hηg.le hηg1 rfl
      (inv_pos.mpr hϖpos) le_rfl _ hPi
    have hscaleO : peFactor η ^ Q2 * (1 + S) ^ Q2 * (1 + regO.joins) *
        Real.exp (-c2 * regO.buffer) ≤ C0 :=
      (seam_block_scale_le hPe hSpos.le (Nat.cast_nonneg _) pkgO.buffer_nonneg
        (min_le_left c2 c3) (show Q2 ≤ Q1 + Q2 + Q3 by omega)).trans hC0O'
    have h3 := hscalarp π hπ lettersO hlO η S ηg ϖ (ϖ * ηg) hη hη1 hS hηg hηg1 hϖ rfl
      tO SO aO bO GO vO gO hGmO hvO hv0O hvsO hvwO hvjO hg0O hgO
      (hg₁O.trans hgB) hGnO regO pkgO hwin hdur hscaleO
      regF.buffer hB hseam hscale hletO htransO hquietO hmeasO X₀O κO hκO f uO wO
      ⟨Cs / ϖ, hfsupp⟩ hcO
    have hc := ennreal_chain4 (mul_nonneg (hCK m M) hΘF) hC4m (mul_nonneg hC2 hΘO) h1 h2 h3
      (hsupp (pin + q))
    refine hc.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    beta_reduce
    calc CK m M * wordTheta ηg lettersF * C4m * (C2 * wordTheta ηg lettersO) *
          (1 + Cs ^ 2) ^ (pin + q)
        = (CK m M * C4m * C2 * (1 + Cs ^ 2) ^ (pin + q)) *
            (wordTheta ηg lettersO * wordTheta ηg lettersF) := by ring
      _ ≤ (CK m M * C4m * C2 * (1 + Cs ^ 2) ^ (pin + q) + 1) *
            (wordTheta ηg lettersO * wordTheta ηg lettersF) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (mul_nonneg hΘO hΘF)
  · -- the error
    -- split `uF - K₊𝒯Π₋g = (uF - K₊𝒯g) + K₊𝒯(I - Π₋)g`
    have hsplit : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a') (z : Vec 2),
        planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
            orderedDerivative wd (Kp (fun x' z' => fourierCutoff
              (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
              x) z =
          (planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z) +
          orderedDerivative wd (Kp (fun x' z' => planeValue (fF x') z' - fourierCutoff
              (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
              x) z := by
      intro x a' wd z
      have hlin : Kp (fun x' z' => planeValue (fF x') z' - fourierCutoff
            (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x =
          fun z' => Kp (fun x' => planeValue (fF x')) x z' - Kp (fun x' z' => fourierCutoff
            (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
            x z' := by
        have hm := map_sub Kp (fun x' => planeValue (fF x')) (fun x' z' => fourierCutoff
          (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
        funext z'
        exact congrFun (congrFun hm x) z'
      rw [hlin, orderedDerivative_sub wd (hKsmooth _ hF0 x a') (hKsmooth _ hG1 x a')]
      exact (sub_add_sub_cancel _ _ _).symm
    have hmeasF : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a'), AEStronglyMeasurable
        (fun z => planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
          orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z) volume := fun x a' wd =>
      (planeJetOrder_aestronglyMeasurable _ a' wd).sub
        (orderedDerivative_continuous wd (hKsmooth _ hF0 x a')).aestronglyMeasurable
    have hmeasK : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a'), AEStronglyMeasurable
        (fun z => orderedDerivative wd (Kp (fun x' z' => planeValue (fF x') z' - fourierCutoff
          (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
          x) z) volume := fun x a' wd =>
      (orderedDerivative_continuous wd
        (hKsmooth _ (fun x => (hF0 x).sub (hG1 x)) x a')).aestronglyMeasurable
    have hsplit' : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a') (z : Vec 2),
        (if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
            orderedDerivative wd (Kp (fun x' z' => fourierCutoff
              (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO)) (Υ z'))
              x) z else 0) =
          (if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z else 0) +
          (if a' ≤ Kout x then orderedDerivative wd (Kp (fun x' z' => planeValue (fF x') z' -
              fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z else 0) := by
      intro x a' wd z
      split_ifs
      · exact hsplit x a' wd z
      · simp
    have hmeasF' : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a'), AEStronglyMeasurable
        (fun z => if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
          orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z else 0) volume := by
      intro x a' wd
      split_ifs
      · exact hmeasF x a' wd
      · exact aestronglyMeasurable_const
    have hmeasK' : ∀ (x : ι) (a' : ℕ) (wd : DerivativeWord2 a'), AEStronglyMeasurable
        (fun z => if a' ≤ Kout x then orderedDerivative wd (Kp (fun x' z' => planeValue (fF x') z' -
          fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x' bO))
            (Υ z')) x) z else 0) volume := by
      intro x a' wd
      split_ifs
      · exact hmeasK x a' wd
      · exact aestronglyMeasurable_const
    refine (le_of_eq (weightedJetNorm_congr _ _ _ _ _ hsplit')).trans ?_
    refine (weightedJetNorm_add_le _ _ _ _ _ _ _ hmeasF' hmeasK').trans ?_
    -- the first term: fast remainder, transport, old negative bound, support
    -- the moments of the seam datum
    have hmomF : momentNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ)) ϖ
        (fun x => planeValue (fF x)) < ⊤ := by
      have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
      have hbO : ∀ t x, ∑ k, vO t x k ^ 2 ≤ (σ.K.Cw / Real.sqrt η) ^ 2 := by
        intro t x
        have h1 := hvwO t x
        have h2 : Real.sqrt (∑ i, vO t x i ^ 2) ≤ σ.K.Cw / Real.sqrt η := by
          rw [le_div_iff₀ hsη, mul_comm]
          exact h1
        calc ∑ k, vO t x k ^ 2 = Real.sqrt (∑ i, vO t x i ^ 2) ^ 2 :=
              (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
          _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      have hmeas' : ∀ j x u o (k : Fin ((lettersO j).edge x u o).length), ∀ wd X z,
          Measurable (fun t => (((lettersO j).edge x u o).get k).coeff wd t X z) :=
        fun j x u o k wd X z => hmeasO j x u o _ (List.get_mem _ _) wd X z
      have hreserve : ∑ j, (lettersO j).order ≤ σ.Jstar := by
        rw [Finset.sum_congr rfl fun j _ => (hlO j).1]
        have hkk : Kmax + Finset.univ.sum dO + 2 ≤ k := σ.hk
        simp only [σ, SeamShape.Jstar]
        omega
      have hO := Seam.compactChainEndpointMoments σ.hD π hπ lettersO σ.Jstar σ.H aO bO hwin.2.1
        hletO κO hreserve hκO X₀O (ϖ * ηg) hmeas' vO hvO hvsO η hη σ.K.Cvj hvjO ϖ hϖpos GO
        hGmO tO SO σ.K.Cwt pkgO.weights hwin.1 hwin.2.2 f uO wO hchainO (Cs / ϖ) hfsupp
        (σ.K.Cw / Real.sqrt η) hbO (σ.pout + ∑ i, σ.KsF i + 2)
      have hCg : 0 ≤ CU * gU := (norm_nonneg _).trans (hΥ.dev.1 0)
      have hT := Seam.centeredTransitionMoments (σ.pout + ∑ i, σ.KsF i + 2) Υ Υinv gU (ϖ * ηg)
        CU _ (le_trans (by norm_num) hq2) hCg hΥ π hπ ϖ
        (fun x => planeValue (uO (Fin.last Nm) x bO))
        (fun x => (planeValue_memLp _).aestronglyMeasurable) hO
      rw [momentNorm_congr_ae hfF]
      exact hT
    have hT1a := hKfast κF Kout hKout hκFf hκF fF uF wF hmomF
      (seamChain_of_isPlaneChain GF lettersF X₀F (ϖ * ηg) κF tF (tF + S) vF fF uF wF hchainF)
    have hT1b : negJetNorm π pin k ϖ 1 (fun x => planeValue (fF x)) =
        negJetNorm π pin k ϖ 1 (fun x z => planeValue (uO (Fin.last Nm) x bO) (Υ z)) :=
      negJetNorm_congr_ae _ _ _ _ _ hfF
    have hT1c := htransk π hπ Υ Υinv gU (ϖ * ηg) ϖ ηg 1 hgU.1 hgU.2 (hΥ.mono hqk) hΥs hϖpos hϖ1 hηg.le hηg1 rfl
      one_pos hϖinv _ hgOm
    have hE3 : 0 ≤ Real.exp (-c3 * S) + (1 + regF.joins) * Real.exp (-c3 * regF.buffer) +
        Real.exp (-c3 * a) := by positivity
    have hP1 : 0 ≤ peFactor η ^ Q1 * (1 + S) ^ Q1 :=
      mul_nonneg (pow_nonneg hPe0 _) (pow_nonneg (by linarith) _)
    have hP3 : 0 ≤ peFactor η ^ Q3 * (1 + S) ^ Q3 :=
      mul_nonneg (pow_nonneg hPe0 _) (pow_nonneg (by linarith) _)
    have ha1 : 0 ≤ C3 * wordTheta ηg lettersF * peFactor η ^ Q3 * (1 + S) ^ Q3 *
        (Real.exp (-c3 * S) + (1 + (regF.joins : ℝ)) * Real.exp (-c3 * regF.buffer) +
          Real.exp (-c3 * a)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC3 hΘF) (pow_nonneg hPe0 _))
        (pow_nonneg (by linarith) _)) hE3
    have hc1 : 0 ≤ C1k * wordTheta ηg lettersO * peFactor η ^ Q1 * (1 + S) ^ Q1 :=
      mul_nonneg (mul_nonneg (mul_nonneg hC1k hΘO) (pow_nonneg hPe0 _)) (pow_nonneg (by linarith) _)
    have hT1 := ennreal_chain4 ha1 hC4k hc1 hT1a ((le_of_eq hT1b).trans hT1c) hT1d
      (hsupp (pin + ∑ i, KsO i))
    -- the second term: kernel, transport, cutoff complement, old negative bound, support
    have hT2a := (weightedJetNorm_ite_le π (pout : ℝ) Kmax ϖ rstar Kout _).trans
      (hKkernel (n + k) Kmax rstar _ hrstar hrstar' (fun x => (hF0 x).sub (hG1 x)))
    have hT2b : negJetNorm π pin (n + k) ϖ ϖ⁻¹ (fun x z => planeValue (fF x) z - fourierCutoff
          (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x bO)) (Υ z)) =
        negJetNorm π pin (n + k) ϖ ϖ⁻¹ (fun x z =>
          (fun x z => planeValue (uO (Fin.last Nm) x bO) z - fourierCutoff
            (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (uO (Fin.last Nm) x bO)) z) x
            (Υ z)) :=
      negJetNorm_congr_ae _ _ _ _ _ fun x => (hfF x).mono fun z hz => by simp only [hz]
    have hT2c := htransN n π hπ Υ Υinv gU (ϖ * ηg) ϖ ηg ϖ⁻¹ hgU.1 hgU.2 (hΥ.mono (hqN n hnmod)) hΥs
      hϖpos hϖ1 hηg.le hηg1 rfl
      (inv_pos.mpr hϖpos) le_rfl _ fun x => (hgOm x).sub (hPi x)
    have hT2d := hcutN n π hπ η S ϖ hη hη1 hS hϖ _ hgOm
    have hT2e := hT2e' n
    have hs : 0 ≤ S ^ (-(n : ℝ) / 2) := Real.rpow_nonneg hSpos.le _
    have hT2 := ennreal_chain4 (mul_nonneg (hCK _ _) hΘF) (hC4N n) (mul_nonneg (hC5N n) hs)
      hT2a ((le_of_eq hT2b).trans hT2c) hT2d
      (hT2e.trans (mul_le_mul_right (hsupp (pin + ∑ i, KsO i)) _))
    refine (add_le_add hT1 hT2).trans ?_
    have hW1 := hW (pin + ∑ i, KsO i)
    have hW2 := hW (pin + ∑ i, KsO i)
    have hX1 : 0 ≤ C3 * wordTheta ηg lettersF * peFactor η ^ Q3 * (1 + S) ^ Q3 *
        (Real.exp (-c3 * S) + (1 + (regF.joins : ℝ)) * Real.exp (-c3 * regF.buffer) +
          Real.exp (-c3 * a)) * C4k * (C1k * wordTheta ηg lettersO * peFactor η ^ Q1 *
          (1 + S) ^ Q1) * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i) :=
      mul_nonneg (mul_nonneg (mul_nonneg ha1 hC4k) hc1) hW1
    have hX2 : 0 ≤ CK (n + k) Kmax * wordTheta ηg lettersF * C4N n *
        (C5N n * S ^ (-(n : ℝ) / 2)) * (C1N n * wordTheta ηg lettersO * peFactor η ^ Q1 *
          (1 + S) ^ Q1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hCK _ _) hΘF) (hC4N n))
        (mul_nonneg (hC5N n) hs)) (mul_nonneg (mul_nonneg (mul_nonneg (hC1N n) hΘO)
          (pow_nonneg hPe0 _)) (pow_nonneg (by linarith) _))
    rw [← mul_assoc (ENNReal.ofReal (CK (n + k) Kmax * wordTheta ηg lettersF * C4N n *
        (C5N n * S ^ (-(n : ℝ) / 2)) * (C1N n * wordTheta ηg lettersO * peFactor η ^ Q1 *
          (1 + S) ^ Q1))), ← ENNReal.ofReal_mul hX2, ← add_mul,
      ← ENNReal.ofReal_add hX1 (mul_nonneg hX2 hW2)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    beta_reduce
    have hP1P := seam_power_le hPe hSpos.le (show Q1 ≤ Q1 + Q2 + Q3 by omega)
    have hP13 : peFactor η ^ Q1 * (1 + S) ^ Q1 * (peFactor η ^ Q3 * (1 + S) ^ Q3) ≤
        peFactor η ^ (Q1 + Q2 + Q3) * (1 + S) ^ (Q1 + Q2 + Q3) := by
      rw [seam_power_add]
      exact seam_power_le hPe hSpos.le (by omega)
    have hexp : ∀ x : ℝ, 0 ≤ x → Real.exp (-c3 * x) ≤ Real.exp (-(min c2 c3) * x) := by
      intro x hx
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right (min_le_right c2 c3) hx
      linarith
    have hj : (0 : ℝ) ≤ 1 + regF.joins := by positivity
    have hE : Real.exp (-c3 * S) + (1 + (regF.joins : ℝ)) * Real.exp (-c3 * regF.buffer) +
          Real.exp (-c3 * a) ≤
        Real.exp (-(min c2 c3) * S) + (1 + (regF.joins : ℝ)) *
          Real.exp (-(min c2 c3) * regF.buffer) + Real.exp (-(min c2 c3) * a) :=
      add_le_add (add_le_add (hexp S hSpos.le) (mul_le_mul_of_nonneg_left (hexp _ hB) hj))
        (hexp a ha)
    have key := seam_error_price
      (A₁ := C3 * C4k * C1k * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i))
      (A₂ := CK (n + k) Kmax * C4N n * C5N n * C1N n * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i))
      (Θ := wordTheta ηg lettersO * wordTheta ηg lettersF)
      (mul_nonneg (mul_nonneg (mul_nonneg hC3 hC4k) hC1k) hW1)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hCK _ _) (hC4N n)) (hC5N n)) (hC1N n)) hW2)
      (mul_nonneg hΘO hΘF) hP1 hP1P hP13 hE3 hE hs
    calc _ = C3 * C4k * C1k * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i) *
            (wordTheta ηg lettersO * wordTheta ηg lettersF *
              (peFactor η ^ Q1 * (1 + S) ^ Q1 * (peFactor η ^ Q3 * (1 + S) ^ Q3) *
                (Real.exp (-c3 * S) + (1 + (regF.joins : ℝ)) * Real.exp (-c3 * regF.buffer) +
                  Real.exp (-c3 * a)))) +
          CK (n + k) Kmax * C4N n * C5N n * C1N n * (1 + Cs ^ 2) ^ (pin + ∑ i, KsO i) *
            (wordTheta ηg lettersO * wordTheta ηg lettersF *
              (peFactor η ^ Q1 * (1 + S) ^ Q1 * S ^ (-(n : ℝ) / 2))) := by ring
      _ ≤ _ := key
      _ = _ := by ring

end AVRegularity.CycleWords.Assembly
