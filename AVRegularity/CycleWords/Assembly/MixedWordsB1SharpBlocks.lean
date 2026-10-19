-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpSlow
public import AVRegularity.CycleDamping.ConstructedCanonicalGraph

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleDamping
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Conditional assembly of `scalar_package_interior` from the five ingredients of
`InteriorScalarIngredients`.

The uniform drift bound is the constructed budget `constructedGraphBudget`, so the actual fibre
symbol is the canonical band symbol, whose Gaussian (`bandChain_scalar_gaussian`) and phase jets
(`constructedCanonical_phase_jets`) are proved. The jet prices and contrast orders of the fibre
constants are raised to cover the smoothing and phase constants; fibre records, replacement
bounds, marks, contraction and quiet means are the proved producers. -/

/-- A proved complete-core contraction time for the cutoff `ξlo`. -/
def interiorMarkTime (ξlo : ℝ) (hlo : 0 < ξlo) : ℝ :=
  Classical.choose (constructed_core_complex_marks_contraction_time ξlo hlo)

/-- The package constants: fibre constants `K₀` with metric smallness `g`, jet prices `C` and
contrast orders `Q`. -/
def interiorPackageConstants (K₀ : ScalarConstants) (g : ℝ) (C : ℕ → ℝ) (Q : ℕ → ℕ) :
    ScalarConstants :=
  { K₀ with g0 := g, Cj := C, Qj := Q }

/-- Raising jet prices and contrast orders keeps a fibre record and its coefficients. -/
def fibreScalarDataRaise {K₀ : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K₀ η G v t₀ S) (g : ℝ) (C : ℕ → ℝ) (Q : ℕ → ℕ)
    (hC : ∀ j, K₀.Cj j ≤ C j) (hQ : ∀ j, K₀.Qj j ≤ Q j) (hC0 : ∀ j, 0 ≤ K₀.Cj j) :
    FibreScalarData (interiorPackageConstants K₀ g C Q) η G v t₀ S :=
  let d₂ := fibreScalarDataWithContrastOrders (fibreScalarDataWithJetPrices d C hC) Q hQ
    (fun j => (hC0 j).trans (hC j))
  { r := d₂.r, lam := d₂.lam, ell := d₂.ell, graph := d₂.graph,
    row_summable := d₂.row_summable, row_mean := d₂.row_mean, row_taylor := d₂.row_taylor,
    real_ratio := d₂.real_ratio, graph_jets := d₂.graph_jets, row_jets := d₂.row_jets,
    fast_decay := d₂.fast_decay, fast_smoothing := d₂.fast_smoothing,
    adjoint_decay := d₂.adjoint_decay, adjoint_smoothing := d₂.adjoint_smoothing }

theorem interior_price_le {a b P R x : ℝ} {Q Q' : ℕ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hQ : Q ≤ Q') (hx : 0 ≤ x) :
    a * P ^ Q * R ^ Q * x ≤ b * P ^ Q' * R ^ Q' * x := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  apply mul_le_mul_of_nonneg_right _ hx
  exact mul_le_mul (mul_le_mul hab (pow_le_pow_right₀ hP hQ) (pow_nonneg hP0 _)
    (ha.trans hab)) (pow_le_pow_right₀ hR hQ) (pow_nonneg hR0 _)
    (mul_nonneg (ha.trans hab) (pow_nonneg hP0 _))

/-- A complete block from its prepared data, raised constants and per-block bounds. -/
def interiorScalarPackage {K₀ : ScalarConstants} (d : InteriorBlockContext K₀)
    (p : PreparedInteriorData d) (g : ℝ) (C : ℕ → ℝ) (Q : ℕ → ℕ)
    (hC : ∀ j, K₀.Cj j ≤ C j) (hQ : ∀ j, K₀.Qj j ≤ Q j) (hC0 : ∀ j, 0 ≤ K₀.Cj j)
    (hpos : 0 < K₀.ξ0 ∧ 0 < K₀.ξlo ∧ 2 * K₀.ξlo < K₀.ξ0 ∧ 0 < K₀.Cg ∧ 0 < K₀.cGauss ∧
      0 < K₀.θs ∧ 0 < K₀.cadm ∧ (∀ j, 0 < C j ∧ 0 < K₀.cj j) ∧ (∀ m, 0 < K₀.Cwt m) ∧
      (2 + K₀.Cw * K₀.Cg) * (2 * K₀.ξlo) ^ 2 ≤ Real.pi ^ 2 / 16)
    (hcadm : K₀.cadm ≤ (1 - Real.exp (-2)) / 288)
    {Csm : ℕ → ℝ} {Qsm : ℕ → ℕ} (hCsm : ∀ j, Csm j ≤ C j) (hCsm0 : ∀ j, 0 ≤ Csm j)
    (hQsm : ∀ j, Qsm j ≤ Q j) (hsmooth : CellHighSmoothingBounds Csm Qsm d.eta d.G d.drift)
    (hgap : CellQuietGapBounds d.eta d.G d.drift)
    (hweights : CellChartWeightsBounds K₀.Cwt d.eta d.G d.drift)
    (hneg : CellNegativeAdjointBounds K₀.Cneg K₀.Qneg d.eta d.G d.drift)
    (hgauss : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ 2 * K₀.ξlo →
      (∫ τ in d.left..(d.left + d.length), fibreSeriesC p.actual.lam ξ τ).re ≤
          -K₀.cGauss * d.length * fibreNorm ξ ^ 2 ∧
        ∀ N : ℕ, 2 ≤ N →
          (∫ τ in d.left..(d.left + d.length),
            ∑ n ∈ Finset.range (N + 1), fibreHomogeneous p.actual.lam ξ n τ).re ≤
            -K₀.cGauss * d.length * fibreNorm ξ ^ 2)
    (hphase : ∀ (n : ℕ) (j : Fin n → Fin 2) (ξ : Fin 2 → ℂ), 1 ≤ n → fibreNorm ξ < K₀.ξ0 →
      ∀ s t : ℝ, d.left ≤ s → s ≤ t → t ≤ d.left + d.length →
        ‖iteratedFDeriv ℂ n
            (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC p.actual.lam ξ' τ) ξ
            (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
          C n * Real.sqrt d.length ^ n *
            (if n = 1 then Real.sqrt d.length * fibreNorm ξ else 1))
    (hmarks : ∀ ξ : Fin 2 → ℂ,
      (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt d.eta) →
      K₀.ξlo ≤ fibreNorm ξ → ∃ j : Fin 2, ∀ m ∈ p.reg.marks j, ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc m (m + K₀.θs))
          (fibreCoefficients d.eta d.G d.drift ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellValue D (m + K₀.θs)) ≤
          ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D m)) :
    ScalarPackage (interiorPackageConstants K₀ g C Q) d.eta d.G d.drift d.left d.length
      d.weight p.reg := by
  have hS : 1 ≤ d.length := d.threshold.trans d.admissible.2.1
  have hθ : 0 < K₀.θs := hpos.2.2.2.2.2.1
  have hPe : 1 ≤ peFactor d.eta := by
    unfold peFactor
    have := inv_nonneg.mpr (Real.sqrt_nonneg d.eta)
    linarith
  have hreplace (j : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      ENNReal.ofReal (K₀.Cj j * peFactor d.eta ^ K₀.Qj j * x * y) ≤
        ENNReal.ofReal (C j * peFactor d.eta ^ Q j * x * y) := by
    apply ENNReal.ofReal_le_ofReal
    have h := interior_price_le (R := 1) (hC j) (hC0 j) hPe le_rfl (hQ j) hx
    simp only [one_pow, mul_one] at h
    exact mul_le_mul_of_nonneg_right h hy
  refine
    { consts_pos := hpos
      actual := fibreScalarDataRaise p.actual g C Q hC hQ hC0
      contraction := ?_
      high_smoothing := ?_
      quiet_zero := p.quiet_zero
      quiet_mean := ?_
      quiet_gap := ?_
      cover := p.cover
      buffer_nonneg := p.buffer_nonneg
      buffer_le := p.buffer_le
      joins_ge := p.joins_ge
      buffer_inside := p.buffer_inside
      buffer_quiet := p.buffer_quiet
      ext := p.ext
      ext_local := fun q => fibreScalarDataRaise (p.ext_local q) g C Q hC hQ hC0
      ext_shear := p.ext_shear
      ext_drift := p.ext_drift
      ext_agree := p.ext_agree
      replace_graph := ?_
      replace_row := ?_
      replace_symbol := ?_
      weights := fun M => Classical.choice (hweights d.left d.length hS M)
      neg_adjoint := hneg d.left d.length (zero_lt_one.trans_le hS)
      gauss := hgauss
      phase_jets := hphase
      marks_in := ?_
      marks_sep := p.marks_sep
      marks_count := ?_
      high_marks := hmarks }
  · intro ξ hreal s t _hst hst _ht D hD
    exact cellRaw_real_fibre_contraction d.eta d.G d.metric d.drift d.inputs.drift
      d.inputs.bound d.inputs.drift_bound ξ hreal hst D hD
  · intro j ξ hξ s t _hs hst _ht
    have hR : 1 ≤ 1 + (t - s) := by linarith
    have hy : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) :=
      add_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _)
    have hprice : ENNReal.ofReal (Csm j * peFactor d.eta ^ Qsm j * (1 + (t - s)) ^ Qsm j *
          (1 + (t - s) ^ (-(j : ℝ) / 2))) ≤
        ENNReal.ofReal (C j * peFactor d.eta ^ Q j * (1 + (t - s)) ^ Q j *
          (1 + (t - s) ^ (-(j : ℝ) / 2))) :=
      ENNReal.ofReal_le_ofReal (interior_price_le (hCsm j) (hCsm0 j) hPe hR (hQsm j) hy)
    obtain ⟨hfwd, hrev⟩ := hsmooth j ξ hξ s t hst
    refine ⟨fun D hD => ?_, fun Ψ hΨ => ?_⟩
    · obtain ⟨g₁, hg₁, hae, hb⟩ := hfwd D hD
      exact ⟨g₁, hg₁, hae, hb.trans (mul_le_mul_left hprice _)⟩
    · obtain ⟨g₁, hg₁, hae, hb⟩ := hrev Ψ hΨ
      exact ⟨g₁, hg₁, hae, hb.trans (mul_le_mul_left hprice _)⟩
  · intro ξ _hreal a b hab hquiet hwindow D hD
    exact cellRaw_quiet_mean_evolution d.eta d.inputs.Cw d.inputs.contrast_nonneg
      d.inputs.hCw d.G d.metric d.drift d.inputs.drift d.inputs.bound
      d.inputs.drift_bound d.inputs.scaled_bound ξ hab
      (fun t ht => p.quiet_zero t ⟨hquiet ht, hwindow ht⟩) D hD
  · intro ξ hξ a b hab hquiet hwindow D hD
    exact hgap ξ hξ a b hab (fun t ht => p.quiet_zero t ⟨hquiet ht, hwindow ht⟩) D hD
  · intro j q ξ hreal hξ t ht
    exact (p.replace_graph j q ξ hreal hξ t ht).trans
      (hreplace j _ _ (fibreNorm_nonneg ξ) (Real.exp_pos _).le)
  · intro j q ξ hreal hξ t ht
    exact (p.replace_row j q ξ hreal hξ t ht).trans
      (hreplace j _ _ (fibreNorm_nonneg ξ) (Real.exp_pos _).le)
  · intro q ξ hreal hξ t ht
    refine (p.replace_symbol q ξ hreal hξ t ht).trans ?_
    have h := interior_price_le (R := 1) (hC 0) (hC0 0) hPe le_rfl (hQ 0)
      (pow_nonneg (fibreNorm_nonneg ξ) 2)
    simp only [one_pow, mul_one] at h
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  · intro j t ht
    obtain ⟨h1, h2⟩ := p.marks_in j t ht
    exact ⟨h1, h2.trans_eq d.right_eq⟩
  · intro j
    calc K₀.cadm * d.length / K₀.θs = K₀.cadm * (d.length / K₀.θs) := by ring
         _ ≤ (1 - Real.exp (-2)) / 288 * (d.length / K₀.θs) :=
           mul_le_mul_of_nonneg_right hcadm (div_nonneg (zero_le_one.trans hS) hθ.le)
         _ = (1 - Real.exp (-2)) / 288 * d.length / K₀.θs := by ring
         _ ≤ ((p.reg.marks j).card : ℝ) := p.marks_count j

/-- `(2 + A) x² ≤ π²/16` for `0 ≤ x ≤ π/(4√(2 + A))`. -/
theorem slowFast_separation_le {A x : ℝ} (hA : 0 ≤ A) (hx0 : 0 ≤ x)
    (hx : x ≤ Real.pi / (4 * Real.sqrt (2 + A))) : (2 + A) * x ^ 2 ≤ Real.pi ^ 2 / 16 := by
  have hs : 0 < Real.sqrt (2 + A) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (2 + A) ^ 2 = 2 + A := Real.sq_sqrt (by linarith)
  have h1 : x * (4 * Real.sqrt (2 + A)) ≤ Real.pi := (le_div_iff₀ (by positivity)).mp hx
  have h2 : (x * (4 * Real.sqrt (2 + A))) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  calc (2 + A) * x ^ 2 = (x * (4 * Real.sqrt (2 + A))) ^ 2 / 16 := by
        rw [mul_pow, mul_pow, hss]
        ring
    _ ≤ Real.pi ^ 2 / 16 := by linarith

/-- The disc radius of the fibre constants at the constructed budget. -/
def interiorRadius : ℝ :=
  min (fibreCoefficientMajorantRadius constructedGraphBudget / 2048)
    (fibreWordRadius constructedGraphBudget)

theorem interiorRadius_pos : 0 < interiorRadius :=
  lt_min (div_pos (fibreCoefficientMajorantRadius_pos constructedGraphBudget_pos.le)
    (by norm_num)) (fibreWordRadius_pos constructedGraphBudget_pos.le)

theorem interiorRadius_lt_phase : interiorRadius < constructedGraphRadius / 2 := by
  have h := constructedGraphRadius_pos
  unfold constructedGraphRadius at h ⊢
  exact (min_le_left _ _).trans_lt (by linarith)

/-- The seed of the package constants: the cutoff, the Gaussian rate, the mark length and
density, and the weight, adjoint and drift constants. The other fields are set by the fibre
constants. -/
def interiorSeed (ξlo c θ : ℝ) (Cneg : ℕ → ℕ → ℝ) (Qneg : ℕ → ℕ) (Cwt Cvj : ℕ → ℝ) :
    ScalarConstants where
  ξ0 := 0
  ξlo := ξlo
  Cg := 0
  Cw := 0
  g0 := 0
  cGauss := c
  θs := θ
  cadm := (1 - Real.exp (-2)) / 288
  Cj := fun _ => 0
  cj := fun _ => 0
  Qj := fun _ => 0
  Cneg := Cneg
  Qneg := Qneg
  Cwt := Cwt
  Cvj := Cvj

/-- The exact conclusion, with its source premises, from the five ingredients. -/
theorem scalar_package_interior_thresholds_of_ingredients
    (hscale : InteriorDriftScaleStatement) (hgap : CellQuietGapStatement)
    (hsmooth : InteriorHighSmoothingStatement) (hweights : CellChartWeightsStatement)
    (hneg : CellNegativeAdjointStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧
      ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
      ∀ ξlo : ℝ, 0 < ξlo → 2 * ξlo ≤ ξmax →
      ∃ (K : ScalarConstants) (Θ₀ : ℝ), K.ξlo = ξlo ∧ K.g0 = g₀ ∧ K.ξ0 = ξ₀ ∧ K.Cg = Cg ∧
        K.cGauss = c ∧ 1 ≤ Θ₀ ∧ Θ₀ = 3 * K.θs ∧ 1 ≤ K.θs ∧
        ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
          ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
          ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
            IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ K.g0 →
            IsMetricNearIdentity (fun t _ => G t) g →
            IsCellDrift (ocCellDrift α q Λ ζ m ν y₀) ∧
            (∀ t (k : Fin 2),
              cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x k : ℂ)) = 0) ∧
            (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t)) ∧
            (∀ t x, Real.sqrt (ν / B) *
              Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ K.Cw) ∧
            (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
              (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ K.Cvj j) ∧
            ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ K.θs ta T →
              ∃ reg : BlockRegions,
                (∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
                  t ∈ reg.quiet ↔
                    ∀ s ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                        (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                      ∀ z, ocCellDrift α q Λ ζ m ν y₀ s z = 0) ∧
                (∀ p, ∃ k : ℤ, Odd k ∧
                  (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
                    |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
                  reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
                ((∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2 - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      (ta / ocEll q Λ m ν ^ 2 + 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) ∪
                    Set.Icc ((ta + T) / ocEll q Λ m ν ^ 2 - 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      ((ta + T) / ocEll q Λ m ν ^ 2 + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                    ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) →
                  min (ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2)) (T / ocEll q Λ m ν ^ 2) ≤
                    reg.buffer) ∧
                (reg.joins : ℝ) ≤ T / ocTau α q Λ m + 4 ∧
                Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
                  (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
                  (Real.sqrt ((ν / B) / (T / ocEll q Λ m ν ^ 2))) reg) := by
  classical
  let Cw := constructedGraphBudget
  have hCw : 0 ≤ Cw := constructedGraphBudget_pos.le
  obtain ⟨Λg, hΛg, g₀g, ξg, cg, hg₀g, hξg, hcg, hgaussΛ⟩ :=
    bandChain_scalar_gaussian hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, _hΛr, hrel⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  obtain ⟨Λd, hscaleΛ⟩ := hscale α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Λh, hsmoothΛ⟩ := hsmooth α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨max (max (max Λg Λr) Λd) Λh,
    hΛg.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))), ?_⟩
  intro Λ hΛ
  have hΛ' : max (max Λg Λr) Λd ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛg' : Λg ≤ Λ := ((le_max_left _ _).trans (le_max_left _ _)).trans hΛ'
  have hΛr' : Λr ≤ Λ := ((le_max_right _ _).trans (le_max_left _ _)).trans hΛ'
  have hΛ1 : 1 ≤ Λ := by omega
  obtain ⟨Cψ, Cvj, hdrift⟩ := hscaleΛ Λ ((le_max_right _ _).trans hΛ')
  obtain ⟨Csm, Qsm, hCsm, hsmB⟩ := hsmoothΛ Λ ((le_max_right _ _).trans hΛ)
  obtain ⟨Cwt, hCwt, hwB⟩ := hweights Cw Cψ Cvj
  obtain ⟨Cneg, Qneg, hnB⟩ := hneg Cw Cψ Cvj
  let g₀ := min (1 / 16) g₀g
  -- the low disc is small against the fast rate
  let ξmax := min ξg (min (interiorRadius / 2)
    (Real.pi / (4 * Real.sqrt (2 + Cw * constructedScalarGraphPrice Cw))))
  have hξmax : ξmax < interiorRadius :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [interiorRadius_pos])
  have hsep : 0 < Real.pi / (4 * Real.sqrt (2 + Cw * constructedScalarGraphPrice Cw)) := by
    have : 0 < 2 + Cw * constructedScalarGraphPrice Cw := by
      have := mul_nonneg hCw (constructedScalarGraphPrice_pos Cw).le
      linarith
    have := Real.sqrt_pos.mpr this
    positivity
  refine ⟨g₀, interiorRadius, ξmax, cg, constructedScalarGraphPrice Cw,
    lt_min (by norm_num) hg₀g, lt_min hξg (lt_min (by linarith [interiorRadius_pos]) hsep),
    hξmax, hcg, constructedScalarGraphPrice_pos Cw, ?_⟩
  intro ξlo hlo hξlo
  let θ := max (interiorMarkTime ξlo hlo) 1
  let K₀ := scalarBufferedComparisonConstants (constructedScalarFibreConstants
    (interiorSeed ξlo cg θ Cneg Qneg Cwt Cvj) Cw hCw)
  have hK₀pos := constructedScalarFibreConstants_positive
    (interiorSeed ξlo cg θ Cneg Qneg Cwt Cvj) Cw hCw
  have hC0 : ∀ j, 0 ≤ K₀.Cj j := fun j =>
    (hK₀pos.2.2.2 j).1.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  let C : ℕ → ℝ := fun j => max (K₀.Cj j) (max (Csm j) (fibrePhaseJetConstant Cw j))
  let Q : ℕ → ℕ := fun j => max (K₀.Qj j) (Qsm j)
  let K := interiorPackageConstants K₀ g₀ C Q
  have hθ1 : 1 ≤ θ := le_max_right _ _
  refine ⟨K, 3 * θ, rfl, rfl, rfl, rfl, rfl, by linarith, rfl, hθ1, ?_⟩
  intro M κ hband m hm2 hmM ν B hνeq hBeq y₀ G g hG hg0 hgK hnear
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hband.2 m (by omega) hmM, hνeq]
  have hBpos : 0 < B := by
    rw [hBmean]
    exact hν.trans_le (CycleReference.meanFlux_ge_input hΛ1 hζ hν)
  have hη : ν / B ≤ 1 := (div_le_one hBpos).mpr (by
    rw [hBmean]
    exact CycleReference.meanFlux_ge_input hΛ1 hζ hν)
  have hη0 : 0 ≤ ν / B := (div_pos hν hBpos).le
  have hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m := hνeq ▸ hrel Λ hΛr' M κ hband m hm2 hmM
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ1 hζ ν y₀
  obtain ⟨V, hV⟩ := hv.2.1
  have hw : ∀ t x, Real.sqrt (ν / B) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw := by
    intro t x
    rw [hBmean]
    exact ocCellDrift_weighted_uniform_bound hΛ1 hζ hν hr y₀ x t
  have hmean : ∀ t (k : Fin 2),
      cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x k : ℂ)) = 0 := by
    intro t k
    unfold cellMean
    rw [integral_complex_ofReal, ocCellDrift_mean_zero hΛ1 hζ ν t y₀ k, Complex.ofReal_zero]
  have hsm : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t) := fun t =>
    cellDrift_spatial_contDiff hΛ1 hζ ν t y₀
  obtain ⟨hjets, hstream⟩ := hdrift M κ hband m hm2 hmM ν B hνeq hBeq y₀
  have hbounds : CellProblemBounds Cw Cψ Cvj (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) :=
    ⟨div_pos hν hBpos, hη, hG, hv, hmean, hsm, hw, hjets, hstream⟩
  refine ⟨hv, hmean, hsm, hw, hjets, ?_⟩
  intro ta T hadm
  have hL : 0 < ocEll q Λ m ν ^ 2 := by
    unfold ocEll
    exact pow_pos (div_pos (AVRegularity.Construction.Stream.ocEpsilon_pos
      (q := q) (n := m) hΛ1) (Real.sqrt_pos.2 hν)) 2
  let inputs : InteriorPhysicalInputs K₀ α q Λ ζ m ν B y₀ :=
    { seed := interiorSeed ξlo cg θ Cneg Qneg Cwt Cvj, Cw := Cw, hCw := hCw,
      constants_eq := rfl, hΛ := hΛ1, hζ := hζ, hν := hν, flux_eq := hBmean,
      scale_pos := hL, pulse_ratio := hr, drift := hv, bound := V,
      drift_bound := hV, scaled_bound := hw, contrast_nonneg := hη0,
      contrast_le_one := hη, mean_zero := hmean, smooth := hsm, drift_jets := hjets }
  let d : InteriorBlockContext K₀ :=
    { α := α, q := q, Λ := Λ, ζ := ζ, m := m, ν := ν, B := B, y₀ := y₀
      inputs := inputs, G := G, metric := hG, g := g, metric_near := hnear
      metric_small := hgK.trans (min_le_left _ _)
      Θ := 3 * θ, threshold := by linarith, ta := ta, T := T, admissible := hadm }
  obtain ⟨p⟩ := preparedInteriorData_exists d
  have hright : d.left + d.length = (ta + T) / ocEll q Λ m ν ^ 2 := d.right_eq.symm
  have hS : 1 ≤ d.length := d.threshold.trans d.admissible.2.1
  have hgauss : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ 2 * K₀.ξlo →
      (∫ τ in d.left..(d.left + d.length), fibreSeriesC p.actual.lam ξ τ).re ≤
          -K₀.cGauss * d.length * fibreNorm ξ ^ 2 ∧
        ∀ N : ℕ, 2 ≤ N →
          (∫ τ in d.left..(d.left + d.length),
            ∑ n ∈ Finset.range (N + 1), fibreHomogeneous p.actual.lam ξ n τ).re ≤
            -K₀.cGauss * d.length * fibreNorm ξ ^ 2 := by
    intro ξ hreal hξ
    rw [p.lam_eq hη hw, hright]
    exact hgaussΛ Λ hΛg' M κ hband m hm2 hmM ν B hνeq hBeq y₀ G g hG hg0
      (hgK.trans (min_le_right _ _)) hnear (3 * θ) θ ta T (by linarith) hadm hη hv hw ξ hreal
      (hξ.trans (hξlo.trans (min_le_left _ _)))
  have hphase : ∀ (n : ℕ) (j : Fin n → Fin 2) (ξ : Fin 2 → ℂ), 1 ≤ n → fibreNorm ξ < K₀.ξ0 →
      ∀ s t : ℝ, d.left ≤ s → s ≤ t → t ≤ d.left + d.length →
        ‖iteratedFDeriv ℂ n
            (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC p.actual.lam ξ' τ) ξ
            (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
          C n * Real.sqrt d.length ^ n *
            (if n = 1 then Real.sqrt d.length * fibreNorm ξ else 1) := by
    intro n j ξ hn hξ s' t hs ht htS
    rw [p.lam_eq hη hw]
    have h := constructedCanonical_phase_jets (ν / B) hη0 hη G hG hv hw d.length hS d.left s' t
      hs ht htS n j hn ξ (hξ.trans interiorRadius_lt_phase)
    refine h.trans ?_
    have hif : 0 ≤ (if n = 1 then Real.sqrt d.length * fibreNorm ξ else 1) := by
      split_ifs
      · exact mul_nonneg (Real.sqrt_nonneg _) (fibreNorm_nonneg ξ)
      · exact zero_le_one
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (pow_nonneg (Real.sqrt_nonneg _) _)) hif
  have hmarked : ∀ ξ : Fin 2 → ℂ,
      (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt d.eta) →
      K₀.ξlo ≤ fibreNorm ξ → ∃ j : Fin 2, ∀ m ∈ p.reg.marks j, ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc m (m + K₀.θs))
          (fibreCoefficients d.eta d.G d.drift ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellValue D (m + K₀.θs)) ≤
          ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D m) := by
    intro ξ hξ hnorm
    have hdrop := (Classical.choose_spec
      (constructed_core_complex_marks_contraction_time ξlo hlo)).2
    have hflux : d.eta = ν / ocMeanFlux α q Λ ζ m ν := by
      change ν / B = _
      rw [hBmean]
    obtain ⟨j, hj⟩ := hdrop α q Λ m ζ hΛ1 hζ ν hν hr y₀ G hG hv V hV ξ
      (by simpa only [hflux] using hξ) hnorm
    refine ⟨j, ?_⟩
    intro t ht D hD
    obtain ⟨n, hn, hcore, hstart, hend⟩ := p.marks_core j t ht
    apply hj t (t + K₀.θs) (le_add_of_nonneg_right (zero_le_one.trans (le_max_right _ _)))
      (by
        have hθ : interiorMarkTime ξlo hlo ≤ K₀.θs := le_max_left _ _
        rw [add_sub_cancel_left]
        exact hθ)
      (ocLabel α q Λ m n) n hcore hn
    · intro s hs
      exact ⟨hstart.trans (mul_le_mul_of_nonneg_left hs.1 hL.le),
        (mul_le_mul_of_nonneg_left hs.2 hL.le).trans hend⟩
    · simpa only [hflux, InteriorBlockContext.drift, d] using hD
  have hpos : 0 < K₀.ξ0 ∧ 0 < K₀.ξlo ∧ 2 * K₀.ξlo < K₀.ξ0 ∧ 0 < K₀.Cg ∧ 0 < K₀.cGauss ∧
      0 < K₀.θs ∧ 0 < K₀.cadm ∧ (∀ j, 0 < C j ∧ 0 < K₀.cj j) ∧ (∀ m, 0 < K₀.Cwt m) ∧
      (2 + K₀.Cw * K₀.Cg) * (2 * K₀.ξlo) ^ 2 ≤ Real.pi ^ 2 / 16 :=
    ⟨interiorRadius_pos, hlo, hξlo.trans_lt hξmax, constructedScalarGraphPrice_pos Cw, hcg,
      zero_lt_one.trans_le (le_max_right _ _),
      div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (by norm_num),
      fun j => ⟨(hK₀pos.2.2.2 j).1.trans_le ((le_max_left _ _).trans
        ((le_max_left _ _).trans (le_max_left _ _))),
        scalarBufferedComparisonConstants_rate_pos _ j⟩, hCwt,
      slowFast_separation_le (A := Cw * constructedScalarGraphPrice Cw) (x := 2 * ξlo)
        (mul_nonneg hCw (constructedScalarGraphPrice_pos Cw).le) (by linarith)
        (hξlo.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  let pkg := interiorScalarPackage d p g₀ C Q (fun j => le_max_left _ _)
    (fun j => le_max_left _ _) hC0 hpos le_rfl
    (fun j => (le_max_left _ _).trans (le_max_right _ _)) (fun j => (hCsm j).le)
    (fun j => le_max_right _ _) (hsmB M κ hband m hm2 hmM ν B hνeq hBeq y₀ G hG)
    (hgap (ν / B) G _ (div_pos hν hBpos) hG hv) (hwB (ν / B) G _ hbounds)
    (hnB (ν / B) G _ hbounds) hgauss hphase hmarked
  have h24 : d.tau / 24 = ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2) := by
    change (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 24 = _
    ring
  have h7 : 7 * d.tau / 24 = 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2) := by
    change 7 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 24 = _
    ring
  refine ⟨p.reg, fun t _ => ?_, p.orientation, ?_, p.joins_upper, ⟨pkg⟩⟩
  · rw [p.quiet_iff t, h24]
    exact Iff.rfl
  have hquarter : d.tau / 4 = ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2) := by
    change (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4 = _
    ring
  simpa only [hquarter, h24, h7, InteriorBlockContext.left, InteriorBlockContext.right,
    InteriorBlockContext.length, InteriorBlockContext.drift, d] using p.buffer_lower

/-- The assembly without the threshold bookkeeping (`Θ₀ = 3K.θs`, `1 ≤ K.θs`). -/
theorem scalar_package_interior_of_ingredients
    (hscale : InteriorDriftScaleStatement) (hgap : CellQuietGapStatement)
    (hsmooth : InteriorHighSmoothingStatement) (hweights : CellChartWeightsStatement)
    (hneg : CellNegativeAdjointStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧
      ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
      ∀ ξlo : ℝ, 0 < ξlo → 2 * ξlo ≤ ξmax →
      ∃ (K : ScalarConstants) (Θ₀ : ℝ), K.ξlo = ξlo ∧ K.g0 = g₀ ∧ K.ξ0 = ξ₀ ∧ K.Cg = Cg ∧
        K.cGauss = c ∧ 1 ≤ Θ₀ ∧
        ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
          ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
          ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
            IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ K.g0 →
            IsMetricNearIdentity (fun t _ => G t) g →
            IsCellDrift (ocCellDrift α q Λ ζ m ν y₀) ∧
            (∀ t (k : Fin 2),
              cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x k : ℂ)) = 0) ∧
            (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t)) ∧
            (∀ t x, Real.sqrt (ν / B) *
              Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ K.Cw) ∧
            (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
              (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ K.Cvj j) ∧
            ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ K.θs ta T →
              ∃ reg : BlockRegions,
                (∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
                  t ∈ reg.quiet ↔
                    ∀ s ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                        (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                      ∀ z, ocCellDrift α q Λ ζ m ν y₀ s z = 0) ∧
                (∀ p, ∃ k : ℤ, Odd k ∧
                  (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
                    |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
                  reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
                ((∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2 - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      (ta / ocEll q Λ m ν ^ 2 + 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) ∪
                    Set.Icc ((ta + T) / ocEll q Λ m ν ^ 2 - 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      ((ta + T) / ocEll q Λ m ν ^ 2 + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                    ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) →
                  min (ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2)) (T / ocEll q Λ m ν ^ 2) ≤
                    reg.buffer) ∧
                (reg.joins : ℝ) ≤ T / ocTau α q Λ m + 4 ∧
                Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
                  (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
                  (Real.sqrt ((ν / B) / (T / ocEll q Λ m ν ^ 2))) reg) := by
  obtain ⟨Λ₀, h128, hΛ⟩ := scalar_package_interior_thresholds_of_ingredients hscale hgap hsmooth
    hweights hneg α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, h128, fun Λ hΛ' => ?_⟩
  obtain ⟨g₀, ξ₀, ξmax, c, Cg, h1, h2, h3, h4, h5, hξ⟩ := hΛ Λ hΛ'
  refine ⟨g₀, ξ₀, ξmax, c, Cg, h1, h2, h3, h4, h5, fun ξlo hlo hξlo => ?_⟩
  obtain ⟨K, Θ₀, e1, e2, e3, e4, e5, hΘ, -, -, hrest⟩ := hξ ξlo hlo hξlo
  exact ⟨K, Θ₀, e1, e2, e3, e4, e5, hΘ, hrest⟩

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: the sharp stage-transform families (statement)

The families `Φ` (the stage test transforms, same level and letter) are split in the
sharp H3s/H4 along the slow test, with coefficients `⟨1 + R, Φ⟩`, where `R` is the graph at the
time. The sharp bounds hold with `ζ = min(1, |ξ| + S^{-1/2})` and use only `‖R‖₂ ≤ M₀|ξ|`. That
norm is free of `P_e` everywhere (`IsFibreGraph`), unlike the graph's `H^j` norms at the block
start. The bounds (`SharpFamilyFacts`):
* general tests: `‖(⟨1 + R, Φ_{i'}⟩)_{i'}‖ ≤ Cζ‖ψ‖` (slow–fast);
* slow tests `ψ_i = β_i (E + D)`, with `‖D‖_{H^N} ≤ M₀|ξ||E|`:
  `‖(⟨1 + R, Φ_{i'}⟩)‖ ≤ Cζ²|E|‖β‖` (slow–slow) and `‖(Φ_{i'})‖_{H^n} ≤ Cζ|E|‖β‖`.

Why these hold (sharp pass and its refinement):
* `⟨1 + R, Tg⟩ = mean(Tg) + ⟨R, Tg⟩`. The mean has a zero from the divergence form (letters) or
  from `ϖ ≤ S^{-1/2} ≤ ζ` and the mean-zero drift (same level).
* On `1 + D/E`, the transforms are `O(|θ| + |ξ|)`: `T1 = O(|θ|)`, and `T(D/E) = O(‖D/E‖)`.
* Inside a window (`IsLeastWindow`) the transforms commute with the transverse projection: the
  letter coefficients are transverse on pulses (`IsWordPiece.htrans`), the drift is a shear
  (`ext_agree`, `ext_shear`), and the metric is constant in space. So the transversality defect of
  a family is controlled by that of its tests (the last clause).
* Letters: the transverse block bounds (`LC1 = O(ε²)`, `C*ℓ = O(ε)` in `L²`), with the scale ratio
  cancelling `θ_l`, as for the crude transform families.
* Same level: the first-order terms carry `ϖ`, with `ϖ|ξ| ≤ ζ²` and `ϖ‖v‖_∞ ≤ S^{-1/2}C_w ≤ ζC_w`;
  the second-order terms carry `ϖ² ≤ ζ²`. -/

universe u v

/-- The sharp facts of a family `Φ` built from tests `ψ` (stage `k` to stage `k'`). -/
def SharpFamilyFacts {I : Type*} [Fintype I] (st : I → ℕ) (k k' : ℕ) {N n : ℕ}
    (ψ : I → TorusHk N ℂ) (Φ : I → TorusHk n ℂ) (C M₀ ζ x : ℝ) : Prop :=
  (∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * x →
    ∑ i' ∈ stageSet st k', ‖cellComplexPair (R + cellConstantCLM 1) (torusHkValueCLM (Φ i'))‖ ^ 2
      ≤ C ^ 2 * ζ ^ 2 * ∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) ∧
  ∀ (E : ℂ) (β : I → ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * x * ‖E‖ →
    (∀ i ∈ stageSet st k, ψ i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + Dd)) →
    (∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * x →
      ∑ i' ∈ stageSet st k',
        ‖cellComplexPair (R + cellConstantCLM 1) (torusHkValueCLM (Φ i'))‖ ^ 2 ≤
        C ^ 2 * ζ ^ 4 * ‖E‖ ^ 2 * ∑ i ∈ stageSet st k, ‖β i‖ ^ 2) ∧
    ∑ i' ∈ stageSet st k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ζ ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ stageSet st k, ‖β i‖ ^ 2

/-- **The sharp same-level families.**

For `ξ = 0`, `S → ∞` one has `ζ → 0`, and the slow pairings vanish (the transforms of
constants are `ϖ`-small). For `v = 0`, `G = I` only `ϖ`-weighted derivatives occur. For `|β| = 0`,
`Φ = 0`. The constant `C` is chosen after the word parameters, `ρ`, `n` and `M₀`. -/
def SharpSameLevelStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ) (M₀ : ℝ),
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
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 ∧
      SharpFamilyFacts b1wSt k k' ψ Φ C M₀
        (min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹))
        (fibreNorm (planeFibreFrequency F.η θ)) ∧
      ∀ p, IsLeastWindow F.reg p r →
      ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
        (∀ U, torusHkValueCLM (PN U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        (∀ U, torusHkValueCLM (Pn U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i' - Pn (Φ i')‖ ^ 2 ≤
          C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i - PN (ψ i)‖ ^ 2

/-- **The sharp letter families**, for almost every time (as for the letter bound of the crude transform families).

For a letter with no edges (`θ_l = 0`), `Φ = 0`. For `ξ = 0`, `S → ∞` the slow pairings
vanish (two zeros: divergence form and `∇(1 + D/E) = O(|ξ|)`). The constant `C` is chosen after
the word parameters, `ρ`, `n` and `M₀`. -/
def SharpLetterAEStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ) (M₀ : ℝ),
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
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 ∧
      SharpFamilyFacts b1wSt k k' ψ Φ C M₀
        (min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹))
        (fibreNorm (planeFibreFrequency F.η θ)) ∧
      ∀ p, IsLeastWindow F.reg p r →
      ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
        (∀ U, torusHkValueCLM (PN U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        (∀ U, torusHkValueCLM (Pn U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i' - Pn (Φ i')‖ ^ 2 ≤
          C ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i - PN (ψ i)‖ ^ 2

end AVRegularity.CycleWords.Assembly
end
