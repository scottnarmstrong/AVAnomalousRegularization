-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LocalEnergy.AEIdent

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # Zero-extended flux integrals and `L²` bookkeeping

Integrability of the flux of the zero-extended data (`integrableOn_flux_bars`), agreement with the
flux of the original data on slabs inside `[ta,tb]` (`flux_bars_eq`), and the identification of
`L²` integrals with norms and distances in `Lp`. -/

open AVRegularity.Applications
open scoped ENNReal

theorem integrableOn_flux_bars {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) (τ₁ τ₂ : ℝ) :
    IntegrableOn (fluxIntegrand ζ ((Set.Ioo ta tb ×ˢ B).indicator U)
        (zeroExt (Set.Ioo ta tb ×ˢ B) P) (zeroExt (Set.Ioo ta tb ×ˢ B) DU)
        ((Set.Ioo ta tb ×ˢ B).indicator g)) (Set.Ioc τ₁ τ₂ ×ˢ B) := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  set S := Set.Ioo ta tb ×ˢ B with hSdef
  obtain ⟨Z, Zg, hZ0, hZg0, hZ, hZg⟩ := exists_bounds hζ.1 hζ.2.1
  set μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ) with hμ
  have hμv : μ ≤ volume := Measure.restrict_le_self
  have mU : MemLp (S.indicator U) 2 μ := ((memLp_indicator_iff_restrict hS).2 h.hU).mono_measure hμv
  have mg : MemLp (S.indicator g) 2 μ := ((memLp_indicator_iff_restrict hS).2 h.hg).mono_measure hμv
  have mD : ∀ i, MemLp (S.indicator (fun q => DU q i)) 2 μ := fun i =>
    ((memLp_indicator_iff_restrict hS).2 (h.hDU i)).mono_measure hμv
  have mP : ∀ i, MemLp (S.indicator (fun q => P q i)) 2 μ := fun i =>
    ((memLp_indicator_iff_restrict hS).2 (h.hP i)).mono_measure hμv
  have m₁ : Measurable fun p : ℝ × Vec 2 => ζ p.2 ^ 2 :=
    ((hζ.1.continuous.comp continuous_snd).pow 2).measurable
  have mφ : ∀ i : Fin 2, Measurable fun p : ℝ × Vec 2 => 2 * ζ p.2 * spGrad ζ p.2 i := fun i => by
    have h1 : Continuous fun p : ℝ × Vec 2 => ζ p.2 := hζ.1.continuous.comp continuous_snd
    have h2 : Continuous fun p : ℝ × Vec 2 => spGrad ζ p.2 i :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
        ((hζ.1.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero |>.comp continuous_snd)
    exact ((continuous_const.mul h1).mul h2).measurable
  have b₁ : ∀ p : ℝ × Vec 2, |ζ p.2 ^ 2| ≤ Z ^ 2 + 2 * Z * Zg + 1 := fun p => by
    rw [abs_pow]
    have := pow_le_pow_left₀ (abs_nonneg _) (hZ p.2) 2
    nlinarith [mul_nonneg hZ0 hZg0]
  have b₂ : ∀ (i : Fin 2) (p : ℝ × Vec 2), |2 * ζ p.2 * spGrad ζ p.2 i| ≤ Z ^ 2 + 2 * Z * Zg + 1 :=
    fun i p => by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul (hZ p.2) (hZg p.2 i) (abs_nonneg _) hZ0
      nlinarith [mul_nonneg hZ0 hZg0]
  have i1 := integrable_weighted_mul m₁ b₁ (mP 0) (mD 0)
  have i2 := integrable_weighted_mul m₁ b₁ (mP 1) (mD 1)
  have i3 := integrable_weighted_mul (mφ 0) (b₂ 0) (mP 0) mU
  have i4 := integrable_weighted_mul (mφ 1) (b₂ 1) (mP 1) mU
  have i5 := integrable_weighted_mul m₁ b₁ mg mU
  have hT : IntegrableOn (fluxIntegrand ζ (S.indicator U) (zeroExt S P) (zeroExt S DU)
      (S.indicator g)) (Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ) volume := by
    have := ((((i1.add i2).add i3).add i4).sub i5)
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [flux_expand]
    rfl
  refine hT.of_forall_sdiff_eq_zero (measurableSet_Ioc.prod hB.measurableSet) fun p hp => ?_
  exact flux_zero_off p fun h' => hp.2 ⟨hp.1.1, h'⟩

theorem flux_bars_eq {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (ζ : Vec 2 → ℝ) {τ₁ τ₂ : ℝ} (h1 : ta ≤ τ₁) (h2 : τ₂ ≤ tb) :
    ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ ((Set.Ioo ta tb ×ˢ B).indicator U)
        (zeroExt (Set.Ioo ta tb ×ˢ B) P) (zeroExt (Set.Ioo ta tb ×ˢ B) DU)
        ((Set.Ioo ta tb ×ˢ B).indicator g) p =
      ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ U P DU g p := by
  refine setIntegral_congr_ae (measurableSet_Ioc.prod hB.measurableSet) ?_
  have hnull : ∀ᵐ p : ℝ × Vec 2 ∂volume, p.1 ≠ tb := by
    rw [Measure.volume_eq_prod]
    have : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ tb := by
      simpa using (Set.countable_singleton tb).ae_notMem (μ := volume)
    exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Vec 2)))).ae this
  filter_upwards [hnull] with p hp hpm
  have hpS : p ∈ Set.Ioo ta tb ×ˢ B := ⟨⟨lt_of_le_of_lt h1 hpm.1.1, lt_of_le_of_ne (hpm.1.2.trans h2) hp⟩, hpm.2⟩
  have e1 : (Set.Ioo ta tb ×ˢ B).indicator U p = U p := Set.indicator_of_mem hpS _
  have e2 : (Set.Ioo ta tb ×ˢ B).indicator g p = g p := Set.indicator_of_mem hpS _
  have e3 : zeroExt (Set.Ioo ta tb ×ˢ B) P p = P p := by
    funext i; simp [zeroExt, Set.indicator_of_mem hpS]
  have e4 : zeroExt (Set.Ioo ta tb ×ˢ B) DU p = DU p := by
    funext i; simp [zeroExt, Set.indicator_of_mem hpS]
  simp only [fluxIntegrand, e1, e2, e3, e4]

theorem integral_sq_sub_lp {α : Type*} [MeasurableSpace α] {μ : Measure α} (u v : Lp ℝ 2 μ) :
    ∫ x, ((u : α → ℝ) x - (v : α → ℝ) x) ^ 2 ∂μ = dist u v ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub u v] with x hx
  rw [hx]
  simp [sq]

theorem integral_sq_lp {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    ∫ x, ((u : α → ℝ) x) ^ 2 ∂μ = ‖u‖ ^ 2 := by
  have := integral_sq_sub_lp u 0
  rw [dist_zero_right] at this
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
  rw [hx]; simp

end AVRegularity.Applications.LocalEnergy
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set Filter Topology
namespace AVRegularity.Applications

/-! # Setup for the Caccioppoli inequality

The standing hypotheses `CaccHyp`, the flux `caccP`, the field `caccS = ∇(χ (U - c))`,
and the `L²` consequences on `Q = (-1,0) × B₁`. -/

/-- The flux `P_c = (I + K) DU - (U - c) d`. -/
def caccP (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (c : ℝ) (p : ℝ × Vec 2) : Vec 2 :=
  (1 + K p).mulVec (DU p) - (U p - c) • d p

/-- `∇(χ (U - c)) = χ DU + (U - c) ∇χ`. -/
def caccS (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (c : ℝ) (p : ℝ × Vec 2) : Vec 2 :=
  caccCut p.2 • DU p + (U p - c) • spGrad caccCut p.2

/-- The vector multiplying the flux in the energy identity. -/
def caccW (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (c : ℝ) (p : ℝ × Vec 2) : Vec 2 :=
  caccCut p.2 ^ 2 • DU p + (2 * caccCut p.2 * (U p - c)) • spGrad caccCut p.2

/-- The drift term `χ (U - c) d·∇(χ (U - c))`. -/
def caccH (d : ℝ × Vec 2 → Vec 2) (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (c : ℝ)
    (p : ℝ × Vec 2) : ℝ :=
  (caccCut p.2 * (U p - c)) * vecDot (d p) (caccS U DU c p)

/-- The standing hypotheses of the Caccioppoli inequality. -/
structure CaccHyp (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd : ℝ) : Prop where
  hkK : 0 ≤ kK
  hkd : 0 ≤ kd
  hsum : kK + kd ≤ 1
  hKm : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))
  hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))
  hskew : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p
  hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
    (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧ vecNormSq (d p) ≤ kd ^ 2
  hdiv : IsDivFreeQ1 d
  hU : IsEnergyClassQ1 U DU
  hw : IsSkewDriftWeak K d U DU

/-- The unit space-time cylinder `Q = (-1,0) × B₁`. -/
abbrev caccQ : Set (ℝ × Vec 2) := Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1

theorem isFiniteMeasure_restrict_caccQ : IsFiniteMeasure (volume.restrict caccQ) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (by simp) (volume_euclidBall_zero_lt_top 1)

namespace CaccHyp

variable {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
  {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd : ℝ}

theorem hKmQ (h : CaccHyp K d U DU kK kd) (i j : Fin 2) :
    AEStronglyMeasurable (fun p => K p i j) (volume.restrict caccQ) := by
  have := h.hKm i j; rwa [openCyl_one] at this

theorem hdmQ (h : CaccHyp K d U DU kK kd) (i : Fin 2) :
    AEStronglyMeasurable (fun p => d p i) (volume.restrict caccQ) := by
  have := h.hdm i; rwa [openCyl_one] at this

theorem hskewQ (h : CaccHyp K d U DU kK kd) :
    ∀ᵐ p ∂(volume.restrict caccQ), (K p).transpose = -K p := by
  have := h.hskew; rwa [openCyl_one] at this

theorem hKbdQ (h : CaccHyp K d U DU kK kd) :
    ∀ᵐ p ∂(volume.restrict caccQ), ∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e := by
  have := h.hbound; rw [openCyl_one] at this
  filter_upwards [this] with p hp using hp.1

theorem hdbdQ (h : CaccHyp K d U DU kK kd) :
    ∀ᵐ p ∂(volume.restrict caccQ), vecNormSq (d p) ≤ kd ^ 2 := by
  have := h.hbound; rw [openCyl_one] at this
  filter_upwards [this] with p hp using hp.2

theorem hUQ (h : CaccHyp K d U DU kK kd) : MemLp U 2 (volume.restrict caccQ) := by
  have := h.hU.1; rwa [openCyl_one] at this

theorem hDUQ (h : CaccHyp K d U DU kK kd) (i : Fin 2) :
    MemLp (fun p => DU p i) 2 (volume.restrict caccQ) := by
  have := h.hU.2.1 i; rwa [openCyl_one] at this

theorem hgradQ (h : CaccHyp K d U DU kK kd) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      HasWeakGradientOn (euclidBall 0 1) (fun y => U (τ, y)) (fun y => DU (τ, y)) :=
  h.hU.2.2.1

theorem hVQ (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    MemLp (fun p => U p - c) 2 (volume.restrict caccQ) := by
  have := isFiniteMeasure_restrict_caccQ
  exact h.hUQ.sub (memLp_const c)

theorem hPQ (h : CaccHyp K d U DU kK kd) (c : ℝ) (i : Fin 2) :
    MemLp (fun p => caccP K d U DU c p i) 2 (volume.restrict caccQ) := by
  have h1 := memLp_mulVec h.hKmQ h.hKbdQ h.hDUQ i
  have h2 := memLp_bdd_mul h.hdmQ h.hdbdQ (h.hVQ c) i
  refine ((h.hDUQ i).add h1 |>.sub h2).ae_eq (Eventually.of_forall fun p => ?_)
  simp [caccP, Matrix.add_mulVec]

theorem hSQ (h : CaccHyp K d U DU kK kd) (c : ℝ) (i : Fin 2) :
    MemLp (fun p => caccS U DU c p i) 2 (volume.restrict caccQ) := by
  have h1 := memLp_cut_mul (pos := Prod.snd) measurable_snd (h.hDUQ i)
  have h2 := memLp_grad_mul (pos := Prod.snd) measurable_snd (h.hVQ c) i
  refine (h1.add h2).ae_eq (Eventually.of_forall fun p => ?_)
  simp [caccS, mul_comm]

theorem hWQ (h : CaccHyp K d U DU kK kd) (c : ℝ) (i : Fin 2) :
    MemLp (fun p => caccW U DU c p i) 2 (volume.restrict caccQ) := by
  have h1 := memLp_cut_sq_mul (pos := Prod.snd) measurable_snd (h.hDUQ i)
  have h2 := memLp_grad_mul (pos := Prod.snd) measurable_snd
    (memLp_cut_mul (pos := Prod.snd) measurable_snd (h.hVQ c)) i
  refine (h1.add (h2.const_mul 2)).ae_eq (Eventually.of_forall fun p => ?_)
  simp [caccW]
  ring

theorem hψQ (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    MemLp (fun p => caccCut p.2 * (U p - c)) 2 (volume.restrict caccQ) :=
  memLp_cut_mul (pos := Prod.snd) measurable_snd (h.hVQ c)

theorem integrable_G (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    Integrable (fun p => vecDot (caccP K d U DU c p) (caccW U DU c p)) (volume.restrict caccQ) :=
  integrable_vecDot_of_memLp (h.hPQ c) (h.hWQ c)

theorem integrable_H (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    Integrable (caccH d U DU c) (volume.restrict caccQ) := by
  have hd : ∀ i : Fin 2, MemLp (fun p => (caccCut p.2 * (U p - c)) * d p i) 2
      (volume.restrict caccQ) := fun i => memLp_bdd_mul h.hdmQ h.hdbdQ (h.hψQ c) i
  have := integrable_vecDot_of_memLp hd (h.hSQ c)
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [caccH, vecDot, Fin.sum_univ_two]
  ring

theorem integrable_S (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    Integrable (fun p => vecNormSq (caccS U DU c p)) (volume.restrict caccQ) :=
  integrable_vecDot_of_memLp (h.hSQ c) (h.hSQ c)

theorem integrable_V (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    Integrable (fun p => (U p - c) ^ 2) (volume.restrict caccQ) :=
  (h.hVQ c).integrable_sq

theorem hbdOpenCyl (h : CaccHyp K d U DU kK kd) :
    ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), vecNormSq (d p) ≤ kd ^ 2 := by
  filter_upwards [h.hbound] with p hp using hp.2

/-- The weak formulation for `V = U - c` with flux `P_c` and zero forcing. -/
theorem hweakV (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1) φ →
      ∫ p in Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1,
        (-((U p - c) * stTimeDeriv φ p) + vecDot (caccP K d U DU c p) (stSpaceGrad φ p)
          - 0 * φ p) = 0 := by
  intro φ hφ
  have hφ' : IsSTTest (openCyl 0 1) φ := by rw [openCyl_one]; exact hφ
  have hflux := skewDrift_flux_form h.hKm h.hdm h.hbound h.hdiv h.hU h.hw c φ hφ'
  rw [openCyl_one] at hflux
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ φ) := hφ.2.1.fderiv ℝ
  have hfinite := isFiniteMeasure_restrict_caccQ
  have hφt : MemLp (stTimeDeriv φ) 2 (volume.restrict caccQ) := by
    refine Continuous.memLp_of_hasCompactSupport ?_ ?_
    · exact hfc.clm_apply continuous_const
    · exact hcs.comp_left (g := fun L : (ℝ × Vec 2) →L[ℝ] ℝ => L (1, 0)) (by simp)
  have hgφ : ∀ i : Fin 2, MemLp (fun p => stSpaceGrad φ p i) 2 (volume.restrict caccQ) := by
    intro i
    refine Continuous.memLp_of_hasCompactSupport ?_ ?_
    · exact hfc.clm_apply continuous_const
    · exact hcs.comp_left (g := fun L : (ℝ × Vec 2) →L[ℝ] ℝ => L (0, basisVec i)) (by simp)
  have i1 : Integrable (fun p => -(U p * stTimeDeriv φ p)) (volume.restrict caccQ) :=
    (h.hUQ.integrable_mul hφt).neg
  have i2 : Integrable (fun p => vecDot (caccP K d U DU c p) (stSpaceGrad φ p))
      (volume.restrict caccQ) := integrable_vecDot_of_memLp (h.hPQ c) hgφ
  have i3 : Integrable (fun p => stTimeDeriv φ p) (volume.restrict caccQ) :=
    hφt.integrable (by norm_num)
  have hz : ∫ p in caccQ, stTimeDeriv φ p = 0 := by
    have := integral_stTimeDeriv_eq_zero_Q1 hφ'
    rwa [openCyl_one] at this
  have hsplit : ∫ p in caccQ, (-((U p - c) * stTimeDeriv φ p)
      + vecDot (caccP K d U DU c p) (stSpaceGrad φ p) - 0 * φ p) =
      (∫ p in caccQ, (-(U p * stTimeDeriv φ p)
        + vecDot (caccP K d U DU c p) (stSpaceGrad φ p))) + c * ∫ p in caccQ, stTimeDeriv φ p := by
    rw [← integral_const_mul, ← integral_add
      (f := fun p => -(U p * stTimeDeriv φ p) + vecDot (caccP K d U DU c p) (stSpaceGrad φ p))
      (g := fun p => c * stTimeDeriv φ p) (i1.add i2) (i3.const_mul c)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [zero_mul, sub_zero]
    ring
  rw [hsplit, hz, mul_zero, add_zero]
  exact hflux

/-- For a.e. time, the drift term `∫_{B₁} χ V d·∇(χ V)` vanishes. -/
theorem slice_H (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∫ y in euclidBall (0 : Vec 2) 1, caccH d U DU c (τ, y) = 0 := by
  have hB := isOpen_euclidBall_zero 1
  filter_upwards [divFree_integral_mul_grad h.hdm h.hbdOpenCyl h.hdiv, h.hgradQ,
    memLp_slice (h.hVQ c), memLp_slice (h.hDUQ 0), memLp_slice (h.hDUQ 1)]
    with τ H hgr hV hD0 hD1
  have hD : ∀ i : Fin 2, MemLp (fun y => DU (τ, y) i) 2 (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
    intro i; fin_cases i
    · exact hD0
    · exact hD1
  have hweak := hasWeakGradientOn_smul_smooth hB (hasWeakGradientOn_sub_const hB hgr c) hV hD
    caccCut_isSpTest
  have hψ : MemLp (fun y => caccCut y * (U (τ, y) - c)) 2 (volume.restrict (euclidBall (0 : Vec 2) 1)) :=
    memLp_cut_mul (pos := id) measurable_id hV
  have hDψ : ∀ i : Fin 2, MemLp (fun y => (caccCut y • DU (τ, y) + (U (τ, y) - c) • spGrad caccCut y) i)
      2 (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
    intro i
    have h1 := memLp_cut_mul (pos := id) measurable_id (hD i)
    have h2 := memLp_grad_mul (pos := id) measurable_id hV i
    refine (h1.add h2).ae_eq (Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have hK : ∃ Kc : Set (Vec 2), IsCompact Kc ∧ Kc ⊆ euclidBall 0 1 ∧
      ∀ y, y ∉ Kc → caccCut y * (U (τ, y) - c) = 0 :=
    ⟨tsupport caccCut, caccCut_isSpTest.2.1, caccCut_isSpTest.2.2, fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]⟩
  exact H _ _ hψ hDψ hweak hK

end CaccHyp

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # Forward and backward mollifier families

Shifted kernel sequences `shiftedKernel (∓2 rₙ) rₙ` whose translated supports stay inside
`(ta,tb) × B` on `[ta, b]` (forward, any `b < tb`) respectively on `[a, tb]` (backward, any `a > ta`),
so that the mollified slices are controlled up to the two endpoints of the time interval. -/

section
open AVRegularity.Applications
open scoped ENNReal

theorem window_shifted {ta tb a b s r δ : ℝ} {B T : Set (Vec 2)} (hr : 0 < r) (hrδ : r ≤ δ)
    (hcth : Metric.cthickening δ T ⊆ B) (hlow : ta < a - s - r) (hup : b - s + r < tb) :
    Window (Set.Ioo ta tb ×ˢ B) (shiftedKernel s r hr) (Set.Icc a b) T := by
  intro τ hτ y hy q hq
  obtain ⟨h1, h2, h3⟩ := shiftedKernel_tsupport_coord q hq
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Prod.fst_sub]
    linarith [hτ.1]
  · simp only [Prod.fst_sub]
    linarith [hτ.2]
  · simp only [Prod.snd_sub]
    apply hcth
    refine Metric.mem_cthickening_of_dist_le _ y δ T hy ?_
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact (h3 i).trans hrδ

theorem mollSeq_shifted (s r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hsr : Tendsto (fun n => |s n| + r n) atTop (𝓝 0)) :
    MollSeq (fun n => shiftedKernel (s n) (r n) (hr n)) where
  contDiff := fun _ => shiftedKernel_contDiff _
  compact := fun _ => shiftedKernel_hasCompactSupport
  conv := fun _ hf => tendsto_eLpNorm_mollify_shifted hf hr hsr

theorem eqOn_of_ae_eq_continuousOn {E : Type*} [MetricSpace E] {F G : ℝ → E} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Set.Icc a b)) (hG : ContinuousOn G (Set.Icc a b))
    (hae : ∀ᵐ τ ∂(volume.restrict (Set.Icc a b)), F τ = G τ) :
    ∀ τ ∈ Set.Icc a b, F τ = G τ := fun _ hτ =>
  Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hab.ne hae hF hG hτ

/-- The radii `δ / (n+1)`. -/
theorem tendsto_radius (δ : ℝ) : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def] using this

theorem exists_forward_family {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {ζ : Vec 2 → ℝ}
    (hζ : IsSpTest B ζ) :
    ∃ k : ℕ → ℝ × Vec 2 → ℝ, MollSeq k ∧ ∀ b < tb, ∃ N0 : ℕ, ∀ n ≥ N0,
      Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc ta b) (tsupport ζ) := by
  obtain ⟨δ, hδ, hcth⟩ := hζ.2.1.isCompact.exists_cthickening_subset_open hB hζ.2.2
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrδ : ∀ n, r n ≤ δ := fun n => by
    simp only [hr]
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_radius δ
  refine ⟨fun n => shiftedKernel (-2 * r n) (r n) (hr0 n),
    mollSeq_shifted (fun n => -2 * r n) r hr0 ?_, fun b hb => ?_⟩
  · have : Tendsto (fun n => 3 * r n) atTop (𝓝 0) := by simpa using hrt.const_mul 3
    refine this.congr fun n => ?_
    rw [abs_mul, abs_neg, abs_two, abs_of_pos (hr0 n)]
    ring
  · have hev : ∀ᶠ n in atTop, 3 * r n < tb - b := by
      have : Tendsto (fun n => 3 * r n) atTop (𝓝 0) := by simpa using hrt.const_mul 3
      exact (tendsto_order.1 this).2 _ (by linarith)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    exact ⟨N0, fun n hn => window_shifted (hr0 n) (hrδ n) hcth (by linarith [hr0 n])
      (by linarith [hN0 n hn])⟩

theorem exists_backward_family {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {ζ : Vec 2 → ℝ}
    (hζ : IsSpTest B ζ) :
    ∃ k : ℕ → ℝ × Vec 2 → ℝ, MollSeq k ∧ ∀ a > ta, ∃ N0 : ℕ, ∀ n ≥ N0,
      Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc a tb) (tsupport ζ) := by
  obtain ⟨δ, hδ, hcth⟩ := hζ.2.1.isCompact.exists_cthickening_subset_open hB hζ.2.2
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrδ : ∀ n, r n ≤ δ := fun n => by
    simp only [hr]
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_radius δ
  refine ⟨fun n => shiftedKernel (2 * r n) (r n) (hr0 n),
    mollSeq_shifted (fun n => 2 * r n) r hr0 ?_, fun a ha => ?_⟩
  · have : Tendsto (fun n => 3 * r n) atTop (𝓝 0) := by simpa using hrt.const_mul 3
    refine this.congr fun n => ?_
    rw [abs_mul, abs_two, abs_of_pos (hr0 n)]
    ring
  · have hev : ∀ᶠ n in atTop, 3 * r n < a - ta := by
      have : Tendsto (fun n => 3 * r n) atTop (𝓝 0) := by simpa using hrt.const_mul 3
      exact (tendsto_order.1 this).2 _ (by linarith)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    exact ⟨N0, fun n hn => window_shifted (hr0 n) (hrδ n) hcth (by linarith [hN0 n hn])
      (by linarith [hr0 n])⟩
end

/-! # Assembly of the continuous `L²` trace and the energy identity

`trace_of_families` glues the forward limit `Wf` (continuous on `[ta, tb)`) and the backward limit
`Wb` (continuous on `(ta, tb]`) into one `L²(B)`-valued function `W`, continuous on `[ta, tb]`,
equal to `ζ U(τ, ·)` for almost every `τ`, whose squared norm satisfies the energy identity. -/

section
open AVRegularity.Applications
open scoped ENNReal

theorem trace_of_families {ta tb : ℝ} (hab : ta < tb) {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {kF kB : ℕ → ℝ × Vec 2 → ℝ}
    (hF : MollSeq kF)
    (hFw : ∀ b < tb, ∃ N0 : ℕ, ∀ n ≥ N0,
      Window (Set.Ioo ta tb ×ˢ B) (kF n) (Set.Icc ta b) (tsupport ζ))
    (hBk : MollSeq kB)
    (hBw : ∀ a > ta, ∃ N0 : ℕ, ∀ n ≥ N0,
      Window (Set.Ioo ta tb ×ˢ B) (kB n) (Set.Icc a tb) (tsupport ζ)) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict B), ContinuousOn W (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict B] fun y => ζ y * U (τ, y)) ∧
      ∀ τ₁ ∈ Set.Icc ta tb, ∀ τ₂ ∈ Set.Icc ta tb, τ₁ ≤ τ₂ →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 =
          -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ U P DU g p := by
  set S := Set.Ioo ta tb ×ˢ B with hSdef
  set Wf := phiLim B ζ S U kF with hWf
  set Wb := phiLim B ζ S U kB with hWb
  -- forward facts
  have hFf : ∀ b, ta < b → b < tb → ContinuousOn Wf (Set.Icc ta b) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Icc ta b)), (Wf τ : Vec 2 → ℝ) =ᵐ[volume.restrict B]
        fun y => ζ y * S.indicator U (τ, y)) ∧
      ∀ τ₁ ∈ Set.Icc ta b, ∀ τ₂ ∈ Set.Icc ta b, τ₁ ≤ τ₂ →
        ‖Wf τ₂‖ ^ 2 - ‖Wf τ₁‖ ^ 2 = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ
          (S.indicator U) (zeroExt S P) (zeroExt S DU) (S.indicator g) p := by
    intro b hb1 hb2
    obtain ⟨N0, hN0⟩ := hFw b hb2
    exact ⟨(phi_tendsto_and_continuous hB h hζ hF hb1 hN0).2, phiLim_ae_eq hB h hζ hF hb1 hN0,
      fun τ₁ h1 τ₂ h2 h12 => energy_identity_limit hB h hζ hF hb1 hN0 h1 h2 h12⟩
  have hBf : ∀ a, ta < a → a < tb → ContinuousOn Wb (Set.Icc a tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Icc a tb)), (Wb τ : Vec 2 → ℝ) =ᵐ[volume.restrict B]
        fun y => ζ y * S.indicator U (τ, y)) ∧
      ∀ τ₁ ∈ Set.Icc a tb, ∀ τ₂ ∈ Set.Icc a tb, τ₁ ≤ τ₂ →
        ‖Wb τ₂‖ ^ 2 - ‖Wb τ₁‖ ^ 2 = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ
          (S.indicator U) (zeroExt S P) (zeroExt S DU) (S.indicator g) p := by
    intro a ha1 ha2
    obtain ⟨N0, hN0⟩ := hBw a ha1
    exact ⟨(phi_tendsto_and_continuous hB h hζ hBk ha2 hN0).2, phiLim_ae_eq hB h hζ hBk ha2 hN0,
      fun τ₁ h1 τ₂ h2 h12 => energy_identity_limit hB h hζ hBk ha2 hN0 h1 h2 h12⟩
  have hEq : ∀ τ ∈ Set.Ioo ta tb, Wf τ = Wb τ := by
    intro τ hτ
    have ha₀ : ta < (ta + τ) / 2 := by linarith [hτ.1]
    have hb₀ : (τ + tb) / 2 < tb := by linarith [hτ.2]
    have hlt : (ta + τ) / 2 < (τ + tb) / 2 := by linarith [hτ.1, hτ.2]
    obtain ⟨c1, a1, -⟩ := hFf ((τ + tb) / 2) (by linarith [hτ.1, hτ.2]) hb₀
    obtain ⟨c2, a2, -⟩ := hBf ((ta + τ) / 2) ha₀ (by linarith [hτ.1, hτ.2])
    have hsub1 : Set.Icc ((ta + τ) / 2) ((τ + tb) / 2) ⊆ Set.Icc ta ((τ + tb) / 2) :=
      Set.Icc_subset_Icc ha₀.le le_rfl
    have hsub2 : Set.Icc ((ta + τ) / 2) ((τ + tb) / 2) ⊆ Set.Icc ((ta + τ) / 2) tb :=
      Set.Icc_subset_Icc le_rfl hb₀.le
    have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc ((ta + τ) / 2) ((τ + tb) / 2))), Wf σ = Wb σ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub1 a1,
        ae_restrict_of_ae_restrict_of_subset hsub2 a2] with σ h1 h2
      exact Lp.ext (h1.trans h2.symm)
    exact eqOn_of_ae_eq_continuousOn hlt (c1.mono hsub1) (c2.mono hsub2) hae τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  classical
  set W : ℝ → Lp ℝ 2 (volume.restrict B) := fun τ => if τ < tb then Wf τ else Wb τ with hW
  have hWf : ∀ τ, τ < tb → W τ = Wf τ := fun τ hτ => by simp [hW, hτ]
  have hWb : ∀ τ, ta < τ → τ ≤ tb → W τ = Wb τ := fun τ h1 h2 => by
    rcases lt_or_eq_of_le h2 with h3 | h3
    · rw [hWf τ h3]; exact hEq τ ⟨h1, h3⟩
    · subst h3; simp [hW]
  refine ⟨W, ?_, ?_, ?_⟩
  · -- continuity
    intro τ hτ
    rcases lt_or_eq_of_le hτ.2 with hlt | heq
    · set b := (τ + tb) / 2 with hb
      have hb1 : ta < b := by linarith [hτ.1]
      have hb2 : b < tb := by linarith
      have hc : ContinuousOn W (Set.Icc ta b) :=
        (hFf b hb1 hb2).1.congr fun σ hσ => hWf σ (lt_of_le_of_lt hσ.2 hb2)
      refine (hc.continuousWithinAt ⟨hτ.1, by linarith⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Set.Iio b, isOpen_Iio, by simp [hb]; linarith,
        fun σ hσ => ⟨hσ.2.1, le_of_lt hσ.1⟩⟩
    · subst heq
      set a := (ta + τ) / 2 with ha
      have ha1 : ta < a := by linarith
      have ha2 : a < τ := by linarith
      have hc : ContinuousOn W (Set.Icc a τ) :=
        (hBf a ha1 ha2).1.congr fun σ hσ => hWb σ (lt_of_lt_of_le ha1 hσ.1) hσ.2
      refine (hc.continuousWithinAt ⟨ha2.le, le_rfl⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Set.Ioi a, isOpen_Ioi, by simpa using ha2,
        fun σ hσ => ⟨le_of_lt hσ.1, hσ.2.2⟩⟩
  · -- almost everywhere identification
    have hcover : Set.Ioo ta tb ⊆ ⋃ m : ℕ, Set.Icc ta (tb - (tb - ta) / ((m : ℝ) + 2)) := by
      intro τ hτ
      obtain ⟨m, hm⟩ := exists_nat_gt ((tb - ta) / (tb - τ))
      refine Set.mem_iUnion.2 ⟨m, hτ.1.le, ?_⟩
      have hpos : 0 < tb - τ := by linarith [hτ.2]
      have h1 : (tb - ta) / ((m : ℝ) + 2) ≤ tb - τ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hm
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      linarith
    refine ae_restrict_of_ae_restrict_of_subset hcover ?_
    rw [ae_restrict_iUnion_iff]
    intro m
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hpos : 0 < (tb - ta) / ((m : ℝ) + 2) := div_pos (by linarith) hm2
    have hb1 : ta < tb - (tb - ta) / ((m : ℝ) + 2) := by
      have : (tb - ta) / ((m : ℝ) + 2) < tb - ta := by
        rw [div_lt_iff₀ hm2]
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), sub_pos.2 hab]
      linarith
    have hb2 : tb - (tb - ta) / ((m : ℝ) + 2) < tb := by linarith
    obtain ⟨-, hae, -⟩ := hFf _ hb1 hb2
    have hne : ∀ᵐ τ ∂(volume.restrict (Set.Icc ta (tb - (tb - ta) / ((m : ℝ) + 2)))), τ ≠ ta :=
      ae_restrict_of_ae (by simpa using (Set.countable_singleton ta).ae_notMem (μ := volume))
    filter_upwards [hae, hne, ae_restrict_mem measurableSet_Icc] with τ h1 h2 h3
    have hτ : τ ∈ Set.Ioo ta tb := ⟨lt_of_le_of_ne h3.1 (Ne.symm h2), lt_of_le_of_lt h3.2 hb2⟩
    rw [hWf τ hτ.2]
    refine h1.trans ?_
    filter_upwards [ae_restrict_mem hB.measurableSet] with y hy
    simp [Set.indicator_of_mem (show (τ, y) ∈ S from ⟨hτ, hy⟩)]
  · -- energy identity
    have hbars := fun τ₁ τ₂ (h1 : ta ≤ τ₁) (h2 : τ₂ ≤ tb) =>
      flux_bars_eq (g := g) (DU := DU) (P := P) (U := U) hB ζ h1 h2
    have claimA : ∀ τ₁ τ₂, ta ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ < tb →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 =
          -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ U P DU g p := by
      intro τ₁ τ₂ h1 h12 h2
      set b := (τ₂ + tb) / 2 with hb
      have hb1 : ta < b := by linarith
      have hb2 : b < tb := by linarith
      rw [hWf τ₁ (by linarith), hWf τ₂ h2, ← hbars τ₁ τ₂ h1 h2.le]
      exact (hFf b hb1 hb2).2.2 τ₁ ⟨h1, by linarith⟩ τ₂ ⟨by linarith, by linarith⟩ h12
    have claimB : ∀ τ₁ τ₂, ta < τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ tb →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 =
          -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ U P DU g p := by
      intro τ₁ τ₂ h1 h12 h2
      set a := (ta + τ₁) / 2 with ha
      have ha1 : ta < a := by linarith
      have ha2 : a < tb := by linarith
      rw [hWb τ₁ h1 (h12.trans h2), hWb τ₂ (lt_of_lt_of_le h1 h12) h2, ← hbars τ₁ τ₂ h1.le h2]
      exact (hBf a ha1 ha2).2.2 τ₁ ⟨by linarith, h12.trans h2⟩ τ₂ ⟨by linarith, h2⟩ h12
    intro τ₁ h1 τ₂ h2 h12
    rcases lt_or_eq_of_le h2.2 with h2lt | h2eq
    · exact claimA τ₁ τ₂ h1.1 h12 h2lt
    · rcases lt_or_eq_of_le h1.1 with h1lt | h1eq
      · exact claimB τ₁ τ₂ h1lt h12 h2.2
      · rw [h2eq, ← h1eq]
        set m := (ta + tb) / 2 with hm
        have hm1 : ta < m := by linarith
        have hm2 : m < tb := by linarith
        have e1 := claimA ta m le_rfl hm1.le hm2
        have e2 := claimB m tb hm1 hm2.le le_rfl
        have hsplit : ∫ p in Set.Ioc ta tb ×ˢ B, fluxIntegrand ζ U P DU g p =
            (∫ p in Set.Ioc ta m ×ˢ B, fluxIntegrand ζ U P DU g p) +
              ∫ p in Set.Ioc m tb ×ˢ B, fluxIntegrand ζ U P DU g p := by
          rw [← hbars ta tb le_rfl le_rfl, ← hbars ta m le_rfl hm2.le, ← hbars m tb hm1.le le_rfl]
          have hu : Set.Ioc ta tb ×ˢ B = Set.Ioc ta m ×ˢ B ∪ Set.Ioc m tb ×ˢ B := by
            rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hm1.le hm2.le]
          rw [hu]
          refine setIntegral_union ?_ (measurableSet_Ioc.prod hB.measurableSet)
            (integrableOn_flux_bars hB h hζ ta m) (integrableOn_flux_bars hB h hζ m tb)
          rw [Set.disjoint_left]
          intro p hp1 hp2
          exact absurd hp2.1.1 (not_lt.2 hp1.1.2)
        rw [hsplit]
        linarith
end

end AVRegularity.Applications.LocalEnergy
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications

/-! # Local energy identity and local `L²` trace

For a weak solution of `∂ₜU = div P + g` in `(ta,tb) × B` with `U, ∇U, P, g ∈ L²` and a spatial
cutoff `ζ ∈ C^∞_c(B)`:

* `local_energy_identity`: `τ ↦ ∫ ζ² U(τ)²` has a representative `E`, continuous on `[ta,tb]`,
  satisfying the integrated energy identity;
* `local_trace_aux`: `τ ↦ ζ U(τ)` has a representative continuous into `L²(B)` on `[ta,tb]`.

Both follow from one-sided time mollification (forward kernels control `[ta, b]`, `b < tb`;
backward kernels control `[a, tb]`, `a > ta`), a uniform Cauchy estimate obtained from the
energy identity for the mollified difference, and gluing of the two limits. -/

open LocalEnergy

/-- The common output of the two general tools: an `L²(B)`-valued function `W`, continuous on
`[ta,tb]`, equal to `ζ U(τ,·)` for a.e. `τ`, whose squared norm satisfies the energy identity. -/
theorem local_trace_aux {ta tb : ℝ} (hab : ta < tb) {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn B (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hP : ∀ i : Fin 2, MemLp (fun p => P p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ B) φ →
      ∫ p in Set.Ioo ta tb ×ˢ B,
        (-(U p * stTimeDeriv φ p) + vecDot (P p) (stSpaceGrad φ p) - g p * φ p) = 0)
    (ζ : Vec 2 → ℝ) (hζ : IsSpTest B ζ) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict B), ContinuousOn W (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict B] fun y => ζ y * U (τ, y)) ∧
      ∀ τ₁ ∈ Set.Icc ta tb, ∀ τ₂ ∈ Set.Icc ta tb, τ₁ ≤ τ₂ →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B,
          (vecDot (P p) (ζ p.2 ^ 2 • DU p + (2 * ζ p.2 * U p) • spGrad ζ p.2)
            - g p * ζ p.2 ^ 2 * U p) := by
  have h : WeakEq ta tb B U g DU P := ⟨hU, hDU, hgrad, hP, hg, hweak⟩
  obtain ⟨kF, hF, hFw⟩ := exists_forward_family (ta := ta) (tb := tb) hB hζ
  obtain ⟨kB, hBk, hBw⟩ := exists_backward_family (ta := ta) (tb := tb) hB hζ
  exact trace_of_families hab hB h hζ hF hFw hBk hBw

/-- **Local energy identity.** -/
theorem local_energy_identity {ta tb : ℝ} (hab : ta < tb) {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn B (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hP : ∀ i : Fin 2, MemLp (fun p => P p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ B) φ →
      ∫ p in Set.Ioo ta tb ×ˢ B,
        (-(U p * stTimeDeriv φ p) + vecDot (P p) (stSpaceGrad φ p) - g p * φ p) = 0)
    (ζ : Vec 2 → ℝ) (hζ : IsSpTest B ζ) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)), E τ = ∫ y in B, ζ y ^ 2 * U (τ, y) ^ 2) ∧
      ∀ τ₁ ∈ Set.Icc ta tb, ∀ τ₂ ∈ Set.Icc ta tb, τ₁ ≤ τ₂ →
        E τ₂ - E τ₁ = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B,
          (vecDot (P p) (ζ p.2 ^ 2 • DU p + (2 * ζ p.2 * U p) • spGrad ζ p.2)
            - g p * ζ p.2 ^ 2 * U p) := by
  obtain ⟨W, hc, hae, hid⟩ := local_trace_aux hab hB hU hDU hgrad hP hg hweak ζ hζ
  refine ⟨fun τ => ‖W τ‖ ^ 2, (hc.norm).pow 2, ?_, hid⟩
  filter_upwards [hae] with τ hτ
  rw [← integral_sq_lp]
  refine integral_congr_ae (hτ.mono fun y hy => ?_)
  simp only [hy]
  ring

end AVRegularity.Applications
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Set Filter Topology
namespace AVRegularity.Applications

/-! # The Caccioppoli inequality for a fixed cutoff

For the cutoff `caccCut` with gradient bound `L`, the energy identity yields
`∫_{Q_{3/4}} |DU|² ≤ (16/7 + 11 L² + 2 L) ∫_{Q₁} (U - c)²`. -/

theorem caccioppoli_core {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ y, vecNormSq (spGrad caccCut y) ≤ L ^ 2)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2} {U : ℝ × Vec 2 → ℝ}
    {DU : ℝ × Vec 2 → Vec 2} {kK kd : ℝ} (h : CaccHyp K d U DU kK kd) (c : ℝ) :
    ∫ p in openCyl 0 (3 / 4), vecNormSq (DU p) ≤
      (16 / 7 + (11 * L ^ 2 + 2 * L)) * ∫ p in openCyl 0 1, (U p - c) ^ 2 := by
  have hB := isOpen_euclidBall_zero 1
  have hfin := isFiniteMeasure_restrict_caccQ
  rw [openCyl_one]
  set M : ℝ := ∫ p in caccQ, (U p - c) ^ 2 with hMdef
  have hgrad : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      HasWeakGradientOn (euclidBall 0 1) (fun y => U (τ, y) - c) (fun y => DU (τ, y)) := by
    filter_upwards [h.hgradQ] with τ hτ using hasWeakGradientOn_sub_const hB hτ c
  obtain ⟨E, hEc, hEae, hEid⟩ := local_energy_identity (ta := -1) (tb := 0) (by norm_num) hB
    (U := fun p => U p - c) (g := fun _ => 0) (DU := DU) (P := caccP K d U DU c)
    (h.hVQ c) h.hDUQ hgrad (h.hPQ c) (memLp_const 0) (h.hweakV c) caccCut caccCut_isSpTest
  -- the slice energies
  set m : ℝ → ℝ := fun τ => ∫ y in euclidBall (0 : Vec 2) 1,
    caccCut y ^ 2 * (U (τ, y) - c) ^ 2 with hm
  have hF : Integrable (fun p : ℝ × Vec 2 => caccCut p.2 ^ 2 * (U p - c) ^ 2)
      (volume.restrict caccQ) := by
    refine (h.hψQ c).integrable_sq.congr (Eventually.of_forall fun p => ?_)
    simp only [mul_pow]
  have hμ : volume.restrict caccQ =
      (volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hmi : IntegrableOn m (Ioo (-1) 0) := by
    have hF2 := hF
    rw [hμ] at hF2
    exact hF2.integral_prod_left
  have hm0 : ∀ τ, 0 ≤ m τ := fun τ => integral_nonneg fun y => by positivity
  have hmint : ∫ τ in Ioo (-1 : ℝ) 0, m τ = ∫ p in caccQ, caccCut p.2 ^ 2 * (U p - c) ^ 2 := by
    have hF' : IntegrableOn (fun p : ℝ × Vec 2 => caccCut p.2 ^ 2 * (U p - c) ^ 2)
        (Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hF
    have := setIntegral_prod _ hF'
    rw [Measure.volume_eq_prod] at *
    exact this.symm
  have hmM : ∫ τ in Ioo (-1 : ℝ) 0, m τ ≤ M := by
    rw [hmint]
    refine setIntegral_mono hF (h.integrable_V c) fun p => ?_
    have h1 : caccCut p.2 ^ 2 ≤ 1 := by
      nlinarith [caccCut_nonneg p.2, caccCut_le_one p.2]
    nlinarith [sq_nonneg (U p - c)]
  have hEm : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), E τ = m τ := hEae
  obtain ⟨τ₁, hτ₁, hEτ₁⟩ := exists_tau_le_of_avg hEc hEm hmi hm0 hmM
  have hE0 : 0 ≤ E 0 :=
    nonneg_zero_of_ae hEc (by filter_upwards [hEm] with τ hτ using hτ ▸ hm0 τ)
  have hτ₁' : τ₁ ∈ Icc (-1 : ℝ) 0 := ⟨hτ₁.1, hτ₁.2.trans (by norm_num)⟩
  have hid := hEid τ₁ hτ₁' 0 ⟨by norm_num, le_rfl⟩ hτ₁'.2
  -- the cylinder `(τ₁, 0) × B₁`
  set Q1 : Set (ℝ × Vec 2) := Ioo τ₁ 0 ×ˢ euclidBall (0 : Vec 2) 1 with hQ1
  have hsub : Q1 ⊆ caccQ := prod_mono (Ioo_subset_Ioo hτ₁.1 le_rfl) subset_rfl
  have hle : volume.restrict Q1 ≤ volume.restrict caccQ := Measure.restrict_mono hsub le_rfl
  have hid' : E 0 - E τ₁ = -2 * ∫ p in Q1, vecDot (caccP K d U DU c p) (caccW U DU c p) := by
    rw [hid, setIntegral_Ioc_prod_eq]
    congr 2
    funext p
    simp only [zero_mul, sub_zero]
    rfl
  have iG := (h.integrable_G c).mono_measure hle
  have iH := (h.integrable_H c).mono_measure hle
  have iS := (h.integrable_S c).mono_measure hle
  have iV := (h.integrable_V c).mono_measure hle
  -- the drift term has zero integral
  have hH0 : ∫ p in Q1, caccH d U DU c p = 0 := by
    have iH' : IntegrableOn (caccH d U DU c) (Ioo τ₁ 0 ×ˢ euclidBall (0 : Vec 2) 1)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact iH
    have := setIntegral_prod _ iH'
    rw [Measure.volume_eq_prod] at *
    rw [this]
    have hslice : ∀ᵐ τ ∂(volume.restrict (Ioo τ₁ 0)),
        ∫ y in euclidBall (0 : Vec 2) 1, caccH d U DU c (τ, y) = 0 :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hτ₁.1 le_rfl) (h.slice_H c)
    rw [integral_congr_ae hslice]
    simp
  -- the pointwise estimate
  have hpt : ∀ᵐ p ∂(volume.restrict Q1),
      -2 * vecDot (caccP K d U DU c p) (caccW U DU c p) - 2 * caccH d U DU c p ≤
        -vecNormSq (caccS U DU c p) + (11 * L ^ 2 + 2 * L) * (U p - c) ^ 2 := by
    have h1 := ae_mono hle h.hskewQ
    have h2 := ae_mono hle h.hKbdQ
    have h3 := ae_mono hle h.hdbdQ
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    exact caccioppoli_pointwise h.hkK h.hkd h.hsum hL0 (caccCut_nonneg p.2) (caccCut_le_one p.2)
      hp1 hp2 hp3 (hL p.2)
  have hint1 : ∫ p in Q1, (-2 * vecDot (caccP K d U DU c p) (caccW U DU c p)
      - 2 * caccH d U DU c p) ≤
      ∫ p in Q1, (-vecNormSq (caccS U DU c p) + (11 * L ^ 2 + 2 * L) * (U p - c) ^ 2) :=
    integral_mono_ae ((iG.const_mul (-2)).sub (iH.const_mul 2))
      (iS.neg.add (iV.const_mul _)) hpt
  have e0 : ∫ p in Q1, (-2 * vecDot (caccP K d U DU c p) (caccW U DU c p)
      - 2 * caccH d U DU c p) = -2 * (∫ p in Q1, vecDot (caccP K d U DU c p) (caccW U DU c p)) := by
    rw [integral_sub (iG.const_mul (-2)) (iH.const_mul 2), integral_const_mul, integral_const_mul,
      hH0]
    ring
  have e1 : ∫ p in Q1, (-vecNormSq (caccS U DU c p) + (11 * L ^ 2 + 2 * L) * (U p - c) ^ 2) =
      -(∫ p in Q1, vecNormSq (caccS U DU c p)) +
        (11 * L ^ 2 + 2 * L) * (∫ p in Q1, (U p - c) ^ 2) := by
    rw [integral_add (f := fun p => -vecNormSq (caccS U DU c p))
      (g := fun p => (11 * L ^ 2 + 2 * L) * (U p - c) ^ 2) iS.neg (iV.const_mul _),
      integral_neg, integral_const_mul]
  rw [e0, e1] at hint1
  have hV1 : ∫ p in Q1, (U p - c) ^ 2 ≤ M :=
    setIntegral_mono_set (h.integrable_V c) (Eventually.of_forall fun p => sq_nonneg _)
      hsub.eventuallyLE
  have hC : 0 ≤ 11 * L ^ 2 + 2 * L := by positivity
  have hS1 : ∫ p in Q1, vecNormSq (caccS U DU c p) ≤ (16 / 7 + (11 * L ^ 2 + 2 * L)) * M := by
    have := mul_le_mul_of_nonneg_left hV1 hC
    linarith
  -- compare with `Q_{3/4}`
  have hQ34 : openCyl 0 (3 / 4) ⊆ Q1 := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (0 : ℝ) - (3 / 4) ^ 2 < t := ht.1
      have := hτ₁.2
      norm_num at *
      linarith
    · simpa using ht.2
    · have hy' : vecNormSq y < (3 / 4) ^ 2 := by simpa [euclidBall] using hy
      simp only [euclidBall, sub_zero, mem_ofPred_eq]
      linarith
  have hmeas : MeasurableSet (openCyl 0 (3 / 4)) :=
    measurableSet_Ioo.prod (isOpen_euclidBall_zero _).measurableSet
  have hDS : ∫ p in openCyl 0 (3 / 4), vecNormSq (DU p) =
      ∫ p in openCyl 0 (3 / 4), vecNormSq (caccS U DU c p) := by
    refine setIntegral_congr_fun hmeas fun p hp => ?_
    have hy : p.2 ∈ euclidBall (0 : Vec 2) (3 / 4) := by simpa using hp.2
    have hy' : vecNormSq p.2 ≤ 9 / 16 := by
      have : vecNormSq p.2 < (3 / 4) ^ 2 := by simpa [euclidBall] using hy
      norm_num at this; linarith
    have hg : spGrad caccCut p.2 = 0 := funext fun i => spGrad_caccCut_eq_zero hy i
    simp [caccS, caccCut_eq_one hy', hg]
  rw [hDS]
  refine le_trans ?_ hS1
  exact setIntegral_mono_set iS (Eventually.of_forall fun p => vecNormSq_nonneg _)
    hQ34.eventuallyLE

end AVRegularity.Applications
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications

/-! # Caccioppoli inequality for the small skew/drift equation

`skewDrift_caccioppoli` (with a non-optimized universal constant `C₀`).  The proof is
assembled in `caccioppoli_core` from the local energy identity, the divergence-free
cancellation of the drift term, and Young's inequality (`caccioppoli_remainder_le`). -/

theorem skewDrift_caccioppoli : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2) (U : ℝ × Vec 2 → ℝ)
      (DU : ℝ × Vec 2 → Vec 2) (kK kd : ℝ), 0 ≤ kK → 0 ≤ kd → kK + kd ≤ 1 →
      (∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) →
      (∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) →
      (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
      (∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
        (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
          vecNormSq (d p) ≤ kd ^ 2) →
      IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
      ∀ c : ℝ, ∫ p in openCyl 0 (3 / 4), vecNormSq (DU p) ≤
        C₀ * ∫ p in openCyl 0 1, (U p - c) ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_caccCut_grad_bound
  refine ⟨16 / 7 + (11 * L ^ 2 + 2 * L), by positivity, ?_⟩
  intro K d U DU kK kd hkK hkd hsum hKm hdm hskew hbound hdiv hU hw c
  exact caccioppoli_core hL0 hL ⟨hkK, hkd, hsum, hKm, hdm, hskew, hbound, hdiv, hU, hw⟩ c

end AVRegularity.Applications
end
end
end
