-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
import AVRegularity.CycleWords.NormalizedProductSquare
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
public import AVRegularity.CycleComparison.LiftSetting.Metric
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleComparison.LiftSetting

/-! The drift fields of the lift setting of an observed pulse. On one enlarged pulse the drift
`v = V(𝗍,z_⊥)e_∥` has zero mean, and the fast jets of `w` are controlled through `q_f`,
independently of `η`.

The drift of the lift is the cell drift `v = ocPulseCellDrift k₁` of the single odd pulse `k₁`, a
shear with profile `V = pulseShearProfile k₁` along `e_∥ = basisVec (pulseParallel k₁)`. Its jets
are bounded by the Péclet number `ε_m^{1+α}/ν` times a numerical constant, and for the normalized
drift `w = √η v`, `η = ν/B`,

`√(ν/B) ε_m^{1+α}/ν = ε_m^{1+α}/√(νB) ≤ √C`,

because `ν + ε_m^{2(1+α)}/ν ≤ C B` along the diffusivity chain (`bandChain_enhancement_bound`).
The constant `C`, hence the bound of the jets of `w`, depends on `(α, s, q, ζ)` only. -/

/-! ### The shear -/

/-- `IsLiftSetting.v_shear`. -/
theorem v_shear {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (ζ : ℝ → ℝ) {ν : ℝ} (hν : 0 < ν)
    {k₁ : ℤ} (hk : Odd k₁) (t : ℝ) (z : Vec 2) :
    ocPulseCellDrift α q Λ ζ m ν k₁ t z =
      EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁ t
          (z (EntryWeakProofs.pulseParallel k₁).rev) •
        basisVec (EntryWeakProofs.pulseParallel k₁) :=
  EntryWeakProofs.normalizedPulseDrift_shear hΛ hν hk t z

/-- `IsLiftSetting.V_smooth`. -/
theorem V_smooth (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (k₁ : ℤ) (qf : ℕ) (t : ℝ) :
    ContDiff ℝ (qf : ℕ∞) (EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁ t) :=
  (EntryWeakProofs.pulseShearProfile_contDiff α q Λ m ζ ν k₁ t).of_le
    (WithTop.coe_le_coe.mpr le_top)

/-- `IsLiftSetting.V_per`. -/
theorem V_per (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (k₁ : ℤ) (t : ℝ) :
    Function.Periodic (EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁ t) 1 :=
  EntryWeakProofs.pulseShearProfile_periodic α q Λ m ζ ν k₁ t

/-- `IsLiftSetting.V_mean`. -/
theorem V_mean (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (k₁ : ℤ) (t : ℝ) :
    (∫ s in (0 : ℝ)..1, EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁ t s) = 0 :=
  EntryWeakProofs.pulseShearProfile_mean_zero α q Λ m ζ ν k₁ t

/-- `IsLiftSetting.v_meas`: the drift is continuous in the cell time. -/
theorem v_meas {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) {k₁ : ℤ} (hk : Odd k₁) (z : Vec 2) :
    Measurable fun t : ℝ => ocPulseCellDrift α q Λ ζ m ν k₁ t z :=
  ((EntryWeakProofs.normalizedPulseDrift_joint_continuous (m := m) hΛ hν hζ hk).comp
    (continuous_id.prodMk continuous_const)).measurable

/-! ### The jets of the normalized drift -/

/-- `x^{2y} = (x^y)²` for `x ≥ 0`. -/
theorem rpow_two_mul_eq_sq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (2 * y) = (x ^ y) ^ 2 := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_two]

/-- The Péclet number in the normalized drift: `√(ν/B) p/ν ≤ √C` when `ν + p²/ν ≤ CB`. -/
theorem sqrt_contrast_mul_le {ν B C p : ℝ} (hν : 0 < ν) (hB : 0 < B) (hp : 0 ≤ p)
    (h : ν + p ^ 2 / ν ≤ C * B) : Real.sqrt (ν / B) * (p / ν) ≤ Real.sqrt C := by
  have hx0 : 0 ≤ Real.sqrt (ν / B) * (p / ν) :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hp hν.le)
  have h1 : p ^ 2 / ν ≤ C * B := by linarith
  have h2 : p ^ 2 / ν / B ≤ C := (div_le_iff₀ hB).2 h1
  have e : (Real.sqrt (ν / B) * (p / ν)) ^ 2 = (ν * ν⁻¹) * (p ^ 2 / ν / B) := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hν.le hB.le)]
    ring
  have hsq : (Real.sqrt (ν / B) * (p / ν)) ^ 2 ≤ C := by
    rw [e, mul_inv_cancel₀ hν.ne', one_mul]
    exact h2
  calc Real.sqrt (ν / B) * (p / ν)
      = Real.sqrt ((Real.sqrt (ν / B) * (p / ν)) ^ 2) := (Real.sqrt_sq hx0).symm
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hsq

/-- The constants of the fast jets of the normalized drift, for the enhancement constant `C`. -/
def liftDriftConst (C : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt C * EntryWeakProofs.pulseFastDerivativeConstant n

/-- `IsLiftSetting.w_jets`: the fast jets of the normalized drift `w = √(ν/B) v` of an odd pulse
are bounded by constants depending on `(α, s, q, ζ)` only, for every level, every chain and
every window. -/
theorem w_jets (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (Cw : ℕ → ℝ), 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m : ℕ, 2 ≤ m → m ≤ M' →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ k₁ : ℤ, Odd k₁ →
      ∀ (t₀ t₁ : ℝ) (qf q' : ℕ), q' ≤ qf →
        (⨆ t ∈ Set.Icc t₀ t₁, ⨆ z : Vec 2,
          ‖iteratedFDeriv ℝ q'
            (fun z' => Real.sqrt (ν / B) • ocPulseCellDrift α q Λ ζ m ν k₁ t z') z‖ₑ) ≤
          ENNReal.ofReal (Cw q') := by
  obtain ⟨C, -, Λ₀, hΛ₀, hbound⟩ :=
    AVRegularity.CycleReference.bandChain_enhancement_bound hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, liftDriftConst C, hΛ₀, ?_⟩
  intro Λ hΛ M' κ hband m hm2 hmM ν B hν hB k₁ hk _ _ _ q' _
  subst hν
  subst hB
  unfold liftDriftConst
  have hΛ1 : 1 ≤ Λ := by omega
  have hνpos : 0 < κ m := AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hBpos : 0 < κ (m - 1) := AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband
    (show m - 1 ≤ M' by omega)
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have henh := hbound Λ hΛ M' (by omega) κ hband m hm2 hmM
  rw [rpow_two_mul_eq_sq he.le (1 + α)] at henh
  have hfac := sqrt_contrast_mul_le hνpos hBpos (Real.rpow_nonneg he.le (1 + α)) henh
  refine iSup₂_le fun t _ => iSup_le fun z => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : ContDiff ℝ (⊤ : ℕ∞) (ocPulseCellDrift α q Λ ζ m (κ m) k₁ t) :=
    EntryWeakProofs.normalizedPulseDrift_contDiff hΛ1 hνpos hk t
  have htop : ((q' : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hder : iteratedFDeriv ℝ q'
      (fun z' => Real.sqrt (κ m / κ (m - 1)) • ocPulseCellDrift α q Λ ζ m (κ m) k₁ t z') z =
      Real.sqrt (κ m / κ (m - 1)) •
        iteratedFDeriv ℝ q' (ocPulseCellDrift α q Λ ζ m (κ m) k₁ t) z :=
    iteratedFDeriv_const_smul_apply' (a := Real.sqrt (κ m / κ (m - 1)))
      (f := ocPulseCellDrift α q Λ ζ m (κ m) k₁ t) (x := z) (i := q')
      ((hd.of_le htop).contDiffAt)
  have hb := EntryWeakProofs.normalizedPulseDrift_vector_fast_bound (α := α) (q := q) (m := m)
    hΛ1 hνpos hζ hk q' q' le_rfl t z
  rw [hder, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (κ m / κ (m - 1)) *
        ‖iteratedFDeriv ℝ q' (ocPulseCellDrift α q Λ ζ m (κ m) k₁ t) z‖
      ≤ Real.sqrt (κ m / κ (m - 1)) * ((ocEpsilon q Λ m ^ (1 + α) / κ m) *
          EntryWeakProofs.pulseFastDerivativeConstant q') :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = (Real.sqrt (κ m / κ (m - 1)) * (ocEpsilon q Λ m ^ (1 + α) / κ m)) *
          EntryWeakProofs.pulseFastDerivativeConstant q' := (mul_assoc _ _ _).symm
    _ ≤ Real.sqrt C * EntryWeakProofs.pulseFastDerivativeConstant q' :=
        mul_le_mul_of_nonneg_right hfac
          (EntryWeakProofs.pulseFastDerivativeConstant_nonneg q')

end AVRegularity.CycleComparison.LiftSetting
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.LiftSetting

/-! The source edges of the lift of one pulse:
the constituents of `liftEdges c lam (F.fiber p ctx)` are the fluxes of the identities of the
family in the lift variables. From the hypotheses on the family they are measurable in time,
box smooth on the lift window, and transverse on it. The enlarged pulse is shorter than the
lift window; on the two margins the level is quiet, and fast independence gives transversality
there. The graph of the lifted edges has the depth of the family. -/

/-! ### Pulse orientation, window and quiet margins -/

/-- On an odd pulse the parallel direction of the drift is the orientation of
`cycle_comparison`. -/
theorem pulseParallel_eq_of_odd {k : ℤ} (hk : Odd k) :
    EntryWeakProofs.pulseParallel k = if k % 4 = 3 then (0 : Fin 2) else 1 := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    obtain ⟨r, rfl⟩ := hk
    omega
  rcases hk4 with h1 | h3
  · have hn : ¬ k % 4 = 3 := by omega
    rw [EntryWeakProofs.pulseParallel, ite_eq_left h1, ite_eq_right hn]
  · have hn : ¬ k % 4 = 1 := by omega
    rw [EntryWeakProofs.pulseParallel, ite_eq_right hn, ite_eq_left h3]

/-- A cell time of the clipped window is a physical time of both windows. -/
theorem mul_mem_inter_of_mem_Icc {c a b tp tz : ℝ} (hc : 0 < c) {s : ℝ}
    (hs : s ∈ Set.Icc (max a tp / c) (min b tz / c)) :
    c * s ∈ Set.Icc a b ∩ Set.Icc tp tz := by
  have h1 : max a tp ≤ s * c := (div_le_iff₀ hc).mp hs.1
  have h2 : s * c ≤ min b tz := (le_div_iff₀ hc).mp hs.2
  rw [mul_comm]
  exact ⟨⟨(le_max_left a tp).trans h1, h2.trans (min_le_left b tz)⟩,
    ⟨(le_max_right a tp).trans h1, h2.trans (min_le_right b tz)⟩⟩

/-- A cell time of the lift window of the pulse `k` is a physical time of the pulse window and of
the observation window. -/
theorem mul_mem_pulseWindow_inter {α q : ℝ} {Λ m : ℕ} {k : ℤ} {c tp tz : ℝ} (hc : 0 < c) {s : ℝ}
    (hs : s ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / c)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tz / c)) :
    c * s ∈ ocPulseWindow α q Λ m k ∩ Set.Icc tp tz :=
  mul_mem_inter_of_mem_Icc hc hs

/-- The margins of a pulse window outside the enlarged pulse are trimmed quiet times. -/
theorem mem_trimmedQuietTimes_of_window_margin {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) {t : ℝ} (ht : t ∈ ocPulseWindow α q Λ m k)
    (hnot : t ∉ Set.Icc (((k : ℝ) - 3 / 4) * ocTau α q Λ m)
      (((k : ℝ) + 3 / 4) * ocTau α q Λ m)) :
    t ∈ ocTrimmedQuietTimes α q Λ ζ m := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have ht1 : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t := ht.1
  have ht2 : t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := ht.2
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
  rcases hnot with hlt | hgt
  · exact odd_trimmed_gap_left hΛ hζ hk (by linarith) (by linarith)
  · exact odd_trimmed_gap hΛ hζ hk (by linarith) (by linarith)

/-- Lambda form of the composition with a time dilation. -/
theorem measurable_comp_const_mul {β : Type*} [MeasurableSpace β] {g : ℝ → β}
    (hg : Measurable g) (c : ℝ) : Measurable fun t => g (c * t) :=
  hg.comp (measurable_const_mul c)

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-! ### The constituents of the lifted fiber -/

/-- A constituent of `liftEdges` is the reparametrisation of a constituent of the family. -/
theorem mem_liftEdges {c lam : ℝ} {edge : ConstituentEdges D h} {v u : ι} {d : Finset.Icc 2 D}
    {γ : Constituent d.1 (h u) (h v)} (hγ : γ ∈ liftEdges c lam edge v u d) :
    ∃ γ' ∈ edge v u d, γ.map = γ'.map ∧
      γ.coeff = fun w t X z => γ'.coeff w (c * t) (lam • X) z := by
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.mp hγ
  exact ⟨γ', hγ', rfl, rfl⟩

/-- A constituent of the fiber is the flux of an identity whose maximal order reaches `d`. -/
theorem mem_fiber {F : ChartedFamily ι h D P Ctx} {p : P} {ctx : Ctx p} {v u : ι}
    {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)} (hγ : γ ∈ F.fiber p ctx v u d) :
    ∃ γ₀ : F.Γ v u, d.1 ≤ (F.identity v u γ₀).maxOrder ∧
      γ.map = (F.identity v u γ₀).map ∧ γ.coeff = F.flux p ctx v u γ₀ d.1 := by
  obtain ⟨γ₀, -, hγ₀⟩ := List.mem_filterMap.mp hγ
  by_cases hd : d.1 ≤ (F.identity v u γ₀).maxOrder
  · rw [dite_eq_left hd] at hγ₀
    obtain rfl := Option.some.inj hγ₀
    exact ⟨γ₀, hd, rfl, rfl⟩
  · rw [dite_eq_right hd] at hγ₀
    cases hγ₀

/-- A constituent of the lifted fiber is the flux of an identity in the lift variables. -/
theorem mem_liftEdges_fiber {F : ChartedFamily ι h D P Ctx} {c lam : ℝ} {p : P} {ctx : Ctx p}
    {v u : ι} {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)}
    (hγ : γ ∈ liftEdges c lam (F.fiber p ctx) v u d) :
    ∃ γ₀ : F.Γ v u, d.1 ≤ (F.identity v u γ₀).maxOrder ∧
      γ.map = (F.identity v u γ₀).map ∧
      γ.coeff = fun w t X z => F.flux p ctx v u γ₀ d.1 w (c * t) (lam • X) z := by
  obtain ⟨γ', hγ', hmap, hcoeff⟩ := mem_liftEdges hγ
  obtain ⟨γ₀, hd, hmap', hcoeff'⟩ := mem_fiber hγ'
  refine ⟨γ₀, hd, hmap.trans hmap', ?_⟩
  rw [hcoeff, hcoeff']

/-! ### Depth and time measurability -/

/-- The lifted fiber has the depth of the family. -/
theorem hasDepthAtMost_liftEdges_fiber (F : ChartedFamily ι h D P Ctx) (c lam : ℝ) (p : P)
    (ctx : Ctx p) {H : ℕ} (hdepth : F.HasDepthAtMost H) :
    HasDepthAtMost (liftEdges c lam (F.fiber p ctx)) H := by
  intro path
  obtain ⟨j, hj⟩ := hdepth path
  refine ⟨j, fun d => ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro γ hγ
  obtain ⟨γ₀, -⟩ := mem_liftEdges_fiber hγ
  exact hj.false γ₀

/-- The coefficients of the lifted fiber are measurable in time. -/
theorem measurable_coeff_liftEdges_fiber (F : ChartedFamily ι h D P Ctx) (c lam : ℝ) (p : P)
    (ctx : Ctx p) (hmeas : F.IsTimeMeasurable) {v u : ι} {d : Finset.Icc 2 D}
    {γ : Constituent d.1 (h u) (h v)} (hγ : γ ∈ liftEdges c lam (F.fiber p ctx) v u d)
    (w : DerivativeWord2 (d.1 - 1)) (X z : Vec 2) :
    Measurable fun t => γ.coeff w t X z := by
  obtain ⟨γ₀, -, -, hc⟩ := mem_liftEdges_fiber hγ
  rw [hc]
  exact measurable_comp_const_mul (hmeas p ctx v u γ₀ d.1 w (lam • X) z) c

/-! ### Smoothness on the window -/

/-- A time of the window in the output times of the piece is a time of the declared domain, at
every label. -/
theorem mem_onWindow (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) (p : P) (ctx : Ctx p) {t : ℝ}
    (ht : t ∈ (F.piece p).output ∩ W) (Y : Vec 2) :
    (t, Y) ∈ ChartedFamily.Domain.onWindow F W p ctx :=
  show (t, Y) ∈ ((F.piece p).output ∩ W) ×ˢ Set.univ from Set.mk_mem_prod ht (Set.mem_univ Y)

/-- Joint smoothness of a flux at a time of the window. -/
theorem contDiff_flux_joint (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) (E : ℝ) (hE : E ≠ 0)
    (n : ℕ) (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => n)) (p : P)
    (ctx : Ctx p) {t : ℝ} (ht : t ∈ (F.piece p).output ∩ W) (v u : ι) (γ₀ : F.Γ v u) (d : ℕ)
    (w : DerivativeWord2 (d - 1)) :
    ContDiff ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun x : Vec 2 × Vec 2 => F.flux p ctx v u γ₀ d w t x.1 x.2) :=
  CycleWords.molecular_joint_contDiff F (ChartedFamily.Domain.onWindow F W) E hE (fun _ => n) hs
    p ctx t (mem_onWindow F W p ctx ht) v u γ₀ d w

/-- Box smoothness of a flux at a time of the window. -/
theorem isBoxSmooth_flux (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) (E : ℝ) (hE : E ≠ 0)
    {Ks Ls : ℕ} (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => Ks + Ls))
    (p : P) (ctx : Ctx p) {t : ℝ} (ht : t ∈ (F.piece p).output ∩ W) (v u : ι) (γ₀ : F.Γ v u)
    (d : ℕ) (w : DerivativeWord2 (d - 1)) :
    IsBoxSmooth Ks Ls (F.flux p ctx v u γ₀ d w t) :=
  Weighted.isBoxSmooth_of_joint_contDiff Ks Ls (F.flux p ctx v u γ₀ d w t)
    (contDiff_flux_joint F W E hE (Ks + Ls) hs p ctx ht v u γ₀ d w)

/-- Box smoothness of a flux in the lift variables at a time of the window. -/
theorem isBoxSmooth_flux_dilate (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) (E : ℝ)
    (hE : E ≠ 0) (lam : ℝ) {Ks Ls qs qf : ℕ} (hqs : qs ≤ Ks) (hqf : qf ≤ Ls)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => Ks + Ls))
    (p : P) (ctx : Ctx p) {t : ℝ} (ht : t ∈ (F.piece p).output ∩ W) (v u : ι) (γ₀ : F.Γ v u)
    (d : ℕ) (w : DerivativeWord2 (d - 1)) :
    IsBoxSmooth qs qf (fun X z => F.flux p ctx v u γ₀ d w t (lam • X) z) := by
  have hj := contDiff_flux_joint F W E hE (Ks + Ls) hs p ctx ht v u γ₀ d w
  have hmap : ContDiff ℝ ((Ks + Ls : ℕ) : WithTop ℕ∞)
      (fun x : Vec 2 × Vec 2 => (lam • x.1, x.2)) :=
    (contDiff_fst.const_smul lam).prodMk contDiff_snd
  have hcomp : ContDiff ℝ ((Ks + Ls : ℕ) : WithTop ℕ∞)
      (fun x : Vec 2 × Vec 2 => F.flux p ctx v u γ₀ d w t (lam • x.1) x.2) :=
    hj.comp hmap
  have hle : ((qs + qf : ℕ) : WithTop ℕ∞) ≤ ((Ks + Ls : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.add_le_add hqs hqf
  exact Weighted.isBoxSmooth_of_joint_contDiff qs qf
    (fun X z => F.flux p ctx v u γ₀ d w t (lam • X) z) (hcomp.of_le hle)

/-- The coefficients of the lifted fiber are box smooth at the cell times whose physical time
lies in the window and in the output times of the piece. -/
theorem isBoxSmooth_coeff_liftEdges_fiber (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) (E : ℝ)
    (hE : E ≠ 0) (c lam : ℝ) {Ks Ls qs qf : ℕ} (hqs : qs ≤ Ks) (hqf : qf ≤ Ls)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => Ks + Ls))
    (p : P) (ctx : Ctx p) {t : ℝ} (ht : c * t ∈ (F.piece p).output ∩ W) {v u : ι}
    {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)}
    (hγ : γ ∈ liftEdges c lam (F.fiber p ctx) v u d) (w : DerivativeWord2 (d.1 - 1)) :
    IsBoxSmooth qs qf (γ.coeff w t) := by
  obtain ⟨γ₀, -, -, hc⟩ := mem_liftEdges_fiber hγ
  rw [hc]
  exact isBoxSmooth_flux_dilate F W E hE lam hqs hqf hs p ctx ht v u γ₀ d.1 w

/-! ### Transversality on the lift window -/

/-- On the pulse window clipped to the observation window, every flux of the piece is
independent of the parallel fast coordinate of the pulse: by transversality on the enlarged
pulse, and by fast independence on the margins, which are trimmed quiet times. -/
theorem flux_transverse_of_mem_window (F : ChartedFamily ι h D P Ctx) {α q : ℝ} {Λ m : ℕ}
    {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k₁ : ℤ} (hk : Odd k₁) {tp tz : ℝ}
    (htrans : F.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
        (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp tz)
      (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp tz))
    (p : P) (ctx : Ctx p)
    (hout : ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp tz ⊆ (F.piece p).output) {t : ℝ}
    (ht : t ∈ ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp tz) (v u : ι) (γ₀ : F.Γ v u) (d : ℕ)
    (w : DerivativeWord2 (d - 1)) (X z : Vec 2) (s : ℝ) :
    F.flux p ctx v u γ₀ d w t X (z + s • basisVec (EntryWeakProofs.pulseParallel k₁)) =
      F.flux p ctx v u γ₀ d w t X z := by
  by_cases hin : t ∈ Set.Icc (((k₁ : ℝ) - 3 / 4) * ocTau α q Λ m)
      (((k₁ : ℝ) + 3 / 4) * ocTau α q Λ m)
  · rw [pulseParallel_eq_of_odd hk]
    exact htrans ⟨k₁, hk⟩ p ctx v u γ₀ d w t ⟨⟨hin, ht.2⟩, hout ht⟩ X z s
  · have hq : t ∈ ocTrimmedQuietTimes α q Λ ζ m :=
      mem_trimmedQuietTimes_of_window_margin hΛ hζ hk ht.1 hin
    exact hquiet p ctx v u γ₀ d w t ⟨⟨hq, ht.2⟩, hout ht⟩ X
      (z + s • basisVec (EntryWeakProofs.pulseParallel k₁)) z

/-- The coefficients of the lifted fiber of the piece of the pulse are transverse on the lift
window. -/
theorem isTransverseOn_coeff_liftEdges_fiber (F : ChartedFamily ι h D P Ctx) {α q : ℝ}
    {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k₁ : ℤ} (hk : Odd k₁)
    {tp tz : ℝ}
    (htrans : F.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
        (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp tz)
      (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp tz))
    (p : P) (ctx : Ctx p)
    (hout : ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp tz ⊆ (F.piece p).output) (c lam : ℝ)
    {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, c * t ∈ ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp tz)
    {v u : ι} {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)}
    (hγ : γ ∈ liftEdges c lam (F.fiber p ctx) v u d) (w : DerivativeWord2 (d.1 - 1)) :
    IsTransverseOn (EntryWeakProofs.pulseParallel k₁) (Set.Icc t₀ t₁) (γ.coeff w) := by
  obtain ⟨γ₀, -, -, hc⟩ := mem_liftEdges_fiber hγ
  rw [hc]
  intro t ht X z s
  exact flux_transverse_of_mem_window F hΛ hζ hk htrans hquiet p ctx hout (hwin t ht) v u γ₀ d.1
    w (lam • X) z s

end AVRegularity.CycleComparison.LiftSetting
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.LiftSetting

/-! The source envelope of the lift of one pulse: the pointwise
analytic envelope of the family gives `IsScaledJetEnvelope` for the lifted fiber on the lift
window.

The lift coefficient is the flux of the family at the slow label `lam • X`, and the slow flux of
the envelope is the same flux at the label `E⁻¹ • Y`. At `Y = E • lam • X` the two agree, so
a slow jet of order `r` of the lift coefficient is `lam ^ r` times `E ^ r` times the jet of the
slow flux. The suprema of the envelope are over every time of the declared domain, every piece
and every context; they dominate the supremum over the lift window of one piece. The sums over
orders and constituents of the two sides are the same sum, in a different order. -/

/-! ### Dilation of a mixed jet -/

/-- The norm of a jet of a dilated function. -/
theorem norm_iteratedFDeriv_comp_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (r : ℕ) (g : Vec 2 → G) (hg : ContDiff ℝ (r : ℕ∞) g) (a : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' => g (a • X')) X‖ =
      |a| ^ r * ‖iteratedFDeriv ℝ r g (a • X)‖ := by
  rw [iteratedFDeriv_comp_const_smul a hg, norm_smul, norm_pow, Real.norm_eq_abs]

/-- A mixed jet of a field dilated in the slow variable. -/
theorem enorm_jet_dilate {f : Vec 2 → Vec 2 → Vec 2} {Ks Ls : ℕ} (hf : IsBoxSmooth Ks Ls f)
    {r q : ℕ} (hr : r ≤ Ks) (hq : q ≤ Ls) (a : ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q (f (a • X')) z) X‖ₑ =
      ENNReal.ofReal (|a| ^ r) *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q (f X') z) (a • X)‖ₑ := by
  have hg : ContDiff ℝ (r : ℕ∞) (fun X' => iteratedFDeriv ℝ q (f X') z) :=
    (hf.2.1 q hq z).of_le (by exact_mod_cast hr)
  have h : ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q (f (a • X')) z) X‖ =
      |a| ^ r * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q (f X') z) (a • X)‖ :=
    norm_iteratedFDeriv_comp_smul r (fun X' => iteratedFDeriv ℝ q (f X') z) hg a X
  rw [← ofReal_norm, h, ENNReal.ofReal_mul (pow_nonneg (abs_nonneg a) r), ofReal_norm]

/-- The jet of the field at the slow label `lam • X` is `lam ^ r` times `E ^ r` times the jet of
the field at the slow label `E⁻¹ • Y`, taken at `Y = E • lam • X`. -/
theorem enorm_lift_jet_eq {f : Vec 2 → Vec 2 → Vec 2} {Ks Ls : ℕ} (hf : IsBoxSmooth Ks Ls f)
    {r q : ℕ} (hr : r ≤ Ks) (hq : q ≤ Ls) {lam E : ℝ} (hlam : 0 ≤ lam) (hE : 0 < E)
    (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q (f (lam • X')) z) X‖ₑ =
      ENNReal.ofReal (lam ^ r) * (ENNReal.ofReal (E ^ r) *
        ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f (E⁻¹ • Y')) z)
          (E • lam • X)‖ₑ) := by
  rw [enorm_jet_dilate hf hr hq lam X z, enorm_jet_dilate hf hr hq E⁻¹ (E • lam • X) z,
    inv_smul_smul₀ hE.ne', abs_of_nonneg hlam, ← mul_assoc (ENNReal.ofReal (E ^ r)),
    ← ENNReal.ofReal_mul (pow_nonneg hE.le r), abs_of_nonneg (inv_nonneg.mpr hE.le),
    ← mul_pow E E⁻¹ r, mul_inv_cancel₀ hE.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-! ### The bridge between the two suprema -/

/-- A jet at a point of the declared domain is below the supremum of the family. -/
theorem enorm_le_pointwiseJetSupFam {κ : Type*} (dom : κ → Set (ℝ × Vec 2)) (r q : ℕ)
    (f : κ → ℝ → Vec 2 → Vec 2 → Vec 2) (i : κ) {t : ℝ} {Y : Vec 2} (hY : (t, Y) ∈ dom i)
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f i t Y') z) Y‖ₑ ≤
      pointwiseJetSupFam dom r q f := by
  unfold pointwiseJetSupFam pointwiseJetSupOn
  exact le_iSup_of_le i (le_iSup_of_le t (le_iSup₂_of_le Y hY (le_iSup_of_le z le_rfl)))

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **The jet bridge.** The jets of a lift coefficient on the lift window are at most `lam ^ r`
times the normalized jets of the slow flux over the declared domain. -/
theorem jetSup_lift_le (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) {E lam c : ℝ} (hE : 0 < E)
    (hlam : 0 ≤ lam) {Ks Ls : ℕ}
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => Ks + Ls))
    (p : P) (ctx : Ctx p) {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, c * t ∈ (F.piece p).output ∩ W)
    (v u : ι) (γ₀ : F.Γ v u) (d : ℕ) (w : DerivativeWord2 (d - 1)) {r q : ℕ} (hr : r ≤ Ks)
    (hq : q ≤ Ls) :
    jetSup (Set.Icc t₀ t₁) r q (fun t X z => F.flux p ctx v u γ₀ d w (c * t) (lam • X) z) ≤
      ENNReal.ofReal (lam ^ r) * (ENNReal.ofReal (E ^ r) *
        pointwiseJetSupFam (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
          (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w)) := by
  unfold jetSup
  refine iSup₂_le fun t ht => iSup_le fun X => iSup_le fun z => ?_
  have hmem : c * t ∈ (F.piece p).output ∩ W := hwin t ht
  have hbox : IsBoxSmooth Ks Ls (F.flux p ctx v u γ₀ d w (c * t)) :=
    isBoxSmooth_flux F W E hE.ne' hs p ctx hmem v u γ₀ d w
  have heq : ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q
        (F.flux p ctx v u γ₀ d w (c * t) (lam • X')) z) X‖ₑ =
      ENNReal.ofReal (lam ^ r) * (ENNReal.ofReal (E ^ r) *
        ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q
          (F.flux p ctx v u γ₀ d w (c * t) (E⁻¹ • Y')) z) (E • lam • X)‖ₑ) :=
    enorm_lift_jet_eq hbox hr hq hlam hE X z
  have hle : ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q
        (F.flux p ctx v u γ₀ d w (c * t) (E⁻¹ • Y')) z) (E • lam • X)‖ₑ ≤
      pointwiseJetSupFam (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
        (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w) :=
    enorm_le_pointwiseJetSupFam
      (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
      (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w) ⟨p, ctx⟩
      (mem_onWindow F W p ctx hmem (E • lam • X)) z
  exact (le_of_eq heq).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hle))

/-! ### Reindexing the sums -/

/-- The sum over a filtered and mapped list. -/
theorem list_sum_map_filterMap {α β M : Type*} [AddCommMonoid M] (l : List α)
    (φ : α → Option β) (ψ : β → M) :
    ((l.filterMap φ).map ψ).sum = (l.map fun a => (φ a).elim 0 ψ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases h : φ a <;> simp [h, ih]

/-- The constituent sum of one order of the lifted fiber, as a sum over the identities. -/
theorem list_sum_liftEdges_fiber (F : ChartedFamily ι h D P Ctx) (c lam : ℝ) (p : P)
    (ctx : Ctx p) (v u : ι) (d : Finset.Icc 2 D) (I : Set ℝ) (r q : ℕ) :
    ((liftEdges c lam (F.fiber p ctx) v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ w, jetSup I r q (γ.coeff w)).sum =
      ∑ γ₀ : F.Γ v u, if d.1 ≤ (F.identity v u γ₀).maxOrder then
        ENNReal.ofReal ‖(F.identity v u γ₀).map‖ * ∑ w : DerivativeWord2 (d.1 - 1),
          jetSup I r q (fun t X z => F.flux p ctx v u γ₀ d.1 w (c * t) (lam • X) z)
      else 0 := by
  simp only [liftEdges, ChartedFamily.fiber, List.map_map]
  rw [list_sum_map_filterMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun γ₀ _ => ?_
  by_cases hd : d.1 ≤ (F.identity v u γ₀).maxOrder
  · rewrite [dite_eq_left hd, ite_eq_left hd]
    rfl
  · rewrite [dite_eq_right hd, ite_eq_right hd]
    rfl

/-- Exchange of the sum over the orders with the sum over the identities. -/
theorem sum_Icc_subtype_ite {Γ : Type*} [Fintype Γ] (D : ℕ) (mo : Γ → ℕ)
    (hmo : ∀ γ, mo γ ≤ D) (T : Γ → ℕ → ℝ≥0∞) :
    ∑ d : Finset.Icc 2 D, ∑ γ : Γ, (if d.1 ≤ mo γ then T γ d.1 else 0) =
      ∑ γ : Γ, ∑ d ∈ Finset.Icc 2 (mo γ), T γ d := by
  rw [Finset.sum_coe_sort (s := Finset.Icc 2 D)
    (f := fun d => ∑ γ : Γ, if d ≤ mo γ then T γ d else 0), Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  have hγ := hmo γ
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The left side of the lift envelope, summed over the identities first. -/
theorem sum_liftEdges_fiber_eq (F : ChartedFamily ι h D P Ctx) (c lam : ℝ) (p : P)
    (ctx : Ctx p) (v u : ι) (I : Set ℝ) (r q : ℕ) :
    ∑ d : Finset.Icc 2 D, ((liftEdges c lam (F.fiber p ctx) v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ w, jetSup I r q (γ.coeff w)).sum =
      ∑ γ₀ : F.Γ v u, ∑ d ∈ Finset.Icc 2 (F.identity v u γ₀).maxOrder,
        ENNReal.ofReal ‖(F.identity v u γ₀).map‖ * ∑ w : DerivativeWord2 (d - 1),
          jetSup I r q (fun t X z => F.flux p ctx v u γ₀ d w (c * t) (lam • X) z) :=
  Eq.trans
    (Finset.sum_congr rfl fun d _ => list_sum_liftEdges_fiber F c lam p ctx v u d I r q)
    (sum_Icc_subtype_ite D (fun γ₀ : F.Γ v u => (F.identity v u γ₀).maxOrder)
      (fun γ₀ => (F.identity v u γ₀).le_D)
      (fun γ₀ d => ENNReal.ofReal ‖(F.identity v u γ₀).map‖ *
        ∑ w : DerivativeWord2 (d - 1),
          jetSup I r q (fun t X z => F.flux p ctx v u γ₀ d w (c * t) (lam • X) z)))

/-! ### Positive sums -/

/-- One term of a double sum over two ranges. -/
theorem le_sum_range_range (g : ℕ → ℕ → ℝ≥0∞) {Ks Ls r q : ℕ} (hr : r ≤ Ks) (hq : q ≤ Ls) :
    g r q ≤ ∑ r' ∈ Finset.range (Ks + 1), ∑ q' ∈ Finset.range (Ls + 1), g r' q' :=
  (Finset.single_le_sum (f := fun q' => g r q') (fun _ _ => zero_le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))).trans
    (Finset.single_le_sum (f := fun r' => ∑ q' ∈ Finset.range (Ls + 1), g r' q')
      (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))

/-- A common factor of the innermost terms comes out of the sums over identities and orders. -/
theorem mul_sum_sum_le_of_le {Γ : Type*} [Fintype Γ] (mo : Γ → ℕ) (s A : ℝ≥0∞)
    (m : Γ → ℝ≥0∞) (J Y : Γ → ℕ → ℝ≥0∞) (hJY : ∀ γ d, J γ d ≤ A * Y γ d) :
    s * ∑ γ, ∑ d ∈ Finset.Icc 2 (mo γ), m γ * J γ d ≤
      A * (s * ∑ γ, m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) := by
  have h0 : ∀ γ d, m γ * J γ d ≤ A * (m γ * Y γ d) := by
    intro γ d
    calc m γ * J γ d ≤ m γ * (A * Y γ d) := mul_le_mul' le_rfl (hJY γ d)
      _ = A * (m γ * Y γ d) := mul_left_comm (m γ) A (Y γ d)
  have h1 : ∀ γ, ∑ d ∈ Finset.Icc 2 (mo γ), m γ * J γ d ≤
      A * (m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) := by
    intro γ
    calc ∑ d ∈ Finset.Icc 2 (mo γ), m γ * J γ d
        ≤ ∑ d ∈ Finset.Icc 2 (mo γ), A * (m γ * Y γ d) :=
          Finset.sum_le_sum fun d _ => h0 γ d
      _ = A * (m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  calc s * ∑ γ, ∑ d ∈ Finset.Icc 2 (mo γ), m γ * J γ d
      ≤ s * ∑ γ, A * (m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun γ _ => h1 γ)
    _ = s * (A * ∑ γ, m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) := by
        rw [← Finset.mul_sum]
    _ = A * (s * ∑ γ, m γ * ∑ d ∈ Finset.Icc 2 (mo γ), Y γ d) :=
        mul_left_comm s A _

variable (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (W : Set ℝ) {E lam c Ca : ℝ}
  {Ks Ls : ℕ} {b : ι → ι → ℝ}

/-- The word sum of the lift jets is at most `lam ^ r` times the reserved sum of the slow flux
jets. -/
theorem sum_jetSup_lift_le (hE : 0 < E) (hlam : 0 ≤ lam)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun _ => Ks + Ls))
    (p : P) (ctx : Ctx p) {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, c * t ∈ (F.piece p).output ∩ W)
    (v u : ι) {r q : ℕ} (hr : r ≤ Ks) (hq : q ≤ Ls) (γ₀ : F.Γ v u) (d : ℕ) :
    (∑ w : DerivativeWord2 (d - 1), jetSup (Set.Icc t₀ t₁) r q
        (fun t X z => F.flux p ctx v u γ₀ d w (c * t) (lam • X) z)) ≤
      ENNReal.ofReal (lam ^ r) * ∑ w : DerivativeWord2 (d - 1),
        ∑ r' ∈ Finset.range (Ks + 1), ∑ q' ∈ Finset.range (Ls + 1),
          ENNReal.ofReal (E ^ r') *
            pointwiseJetSupFam
              (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r' q'
              (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  exact (jetSup_lift_le F W hE hlam hs p ctx hwin v u γ₀ d w hr hq).trans
    (mul_le_mul' le_rfl (le_sum_range_range
      (fun r' q' => ENNReal.ofReal (E ^ r') *
        pointwiseJetSupFam
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r' q'
          (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w)) hr hq))

/-- The jets of the lifted fiber, of orders within the reserve of the pointwise analytic
envelope, are majorized by the edge matrix with the factor `lam ^ r`. -/
theorem scaled_jets_le (hE : 0 < E) (hlam : 0 ≤ lam)
    (han : IsPointwiseAnalyticEnvelope F π (ChartedFamily.Domain.onWindow F W) E Ca Ks Ls b)
    (p : P) (ctx : Ctx p) {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, c * t ∈ (F.piece p).output ∩ W)
    (v u : ι) {r q : ℕ} (hr : r ≤ Ks) (hq : q ≤ Ls) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
        ∑ d : Finset.Icc 2 D, ((liftEdges c lam (F.fiber p ctx) v u d).map fun γ =>
          ENNReal.ofReal ‖γ.map‖ * ∑ w, jetSup (Set.Icc t₀ t₁) r q (γ.coeff w)).sum ≤
      ENNReal.ofReal (Ca * lam ^ r * b v u) := by
  rw [sum_liftEdges_fiber_eq F c lam p ctx v u (Set.Icc t₀ t₁) r q]
  have h := mul_sum_sum_le_of_le (fun γ₀ : F.Γ v u => (F.identity v u γ₀).maxOrder)
    (ENNReal.ofReal (Real.sqrt (π u / π v))) (ENNReal.ofReal (lam ^ r))
    (fun γ₀ => ENNReal.ofReal ‖(F.identity v u γ₀).map‖)
    (fun γ₀ d => ∑ w : DerivativeWord2 (d - 1), jetSup (Set.Icc t₀ t₁) r q
      (fun t X z => F.flux p ctx v u γ₀ d w (c * t) (lam • X) z))
    (fun γ₀ d => ∑ w : DerivativeWord2 (d - 1),
      ∑ r' ∈ Finset.range (Ks + 1), ∑ q' ∈ Finset.range (Ls + 1),
        ENNReal.ofReal (E ^ r') *
          pointwiseJetSupFam
            (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r' q'
            (fun x => F.slowFlux E x.1 x.2 v u γ₀ d w))
    (sum_jetSup_lift_le F W hE hlam han.1 p ctx hwin v u hr hq)
  refine h.trans ?_
  refine (mul_le_mul' le_rfl (han.2 v u)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (pow_nonneg hlam r)]
  exact congrArg ENNReal.ofReal (by ring)

/-- **The envelope of the lift**: the pointwise analytic envelope of the family on the
window gives the scaled jet envelope of the lifted fiber on the lift window. -/
theorem isScaledJetEnvelope_liftEdges_fiber [Fintype ι] (hE : 0 < E) (hlam : 0 ≤ lam)
    {qs qf : ℕ} (hqs : qs ≤ Ks) (hqf : qf ≤ Ls) {S : ℝ} (hb : ∀ v u, 0 ≤ b v u)
    (hrow : ∀ v, ∑ u, b v u ≤ S) (hcol : ∀ u, ∑ v, b v u ≤ S)
    (han : IsPointwiseAnalyticEnvelope F π (ChartedFamily.Domain.onWindow F W) E Ca Ks Ls b)
    (p : P) (ctx : Ctx p) {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, c * t ∈ (F.piece p).output ∩ W) :
    IsScaledJetEnvelope π (liftEdges c lam (F.fiber p ctx)) (Set.Icc t₀ t₁) lam
      (fun _ _ => Ca) qs qf b S where
  nonneg := hb
  row_sum := hrow
  col_sum := hcol
  jets := fun v u _ hr _ hq =>
    scaled_jets_le F π W hE hlam han p ctx hwin v u (hr.trans hqs) (hq.trans hqf)

end AVRegularity.CycleComparison.LiftSetting
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.CycleComparison.LiftSetting

/-! The lift setting of every observed pulse: the premises of the lift setting, instantiated on
the pulses of the comparison window.

`isLiftSetting_pulse` assembles the structure `IsLiftSetting` for the operator data
`pulseLiftData` of one observed pulse, one lemma per field:
* the scales, from the window cover and the diffusivity chain (`Scales`);
* the metric, from the window cover on the chart of the pulse (`Metric`);
* the drift, the shear of the single pulse (`Drift`);
* the source edges of the lifted fiber, from the hypotheses on the family (`Edges`);
* the source envelope, from the pointwise analytic envelope (`Envelope`).

`lift_setting` is the statement of `cycle_comparison_lift_setting`. Its constants are
those of the fast jets of the normalized drift (`w_jets`), found with the threshold `Λ₀`, and the
metric constants `liftMetricConst g₀ CG`. -/

/-- The cell time scale `ℓ²` is positive. -/
theorem ocEll_sq_pos (q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {ν : ℝ} (hν : 0 < ν) :
    0 < ocEll q Λ m ν ^ 2 := by
  unfold ocEll
  exact pow_pos (div_pos (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ)
    (Real.sqrt_pos.2 hν)) 2

/-- **The lift setting of an observed pulse**, from the data of `cycle_comparison` and the bound
`hw` of the fast jets of the normalized drift of the pulse. -/
theorem isLiftSetting_pulse {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {g₀ Ca : ℝ} {CG : ℕ → ℝ} (hg₀ : g₀ ≤ 1 / 4) {Cw : ℕ → ℝ}
    {H D N K k L qs qf Ks Ls qJ Kmax : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N)
    (hqs : qs = K + 4 * (H + 1) * (N + D) ^ 2)
    (hqf : qf = max k (L + 2) + H * D + 2 * N + 2 * D)
    (hqsK : qs ≤ Ks) (hqfL : qf ≤ Ls) (hqsJ : qs ≤ qJ)
    {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} (hband : IsOCBandChain α q Λ ζ M' κ)
    {m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M') {ν B : ℝ} (hν : κ m = ν) (hB : κ (m - 1) = B)
    {k₁ : ℤ}
    (hw : ∀ (s₀ s₁ : ℝ) (n₀ n : ℕ), n ≤ n₀ →
      (⨆ t ∈ Set.Icc s₀ s₁, ⨆ z : Vec 2,
        ‖iteratedFDeriv ℝ n
          (fun z' => Real.sqrt (ν / B) • ocPulseCellDrift α q Λ ζ m ν k₁ t z') z‖ₑ) ≤
        ENNReal.ofReal (Cw n))
    {hφ : IsAdmissibleStream (Φ (m - 1))} {tp Tobs ρs g a B₀ lam₀ Cb : ℝ} {l₀ : ℤ} {P : ℕ}
    {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) ρs g g₀ a B₀ lam₀ Cb
      qJ Kmax CG l₀ P y₀)
    {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
    (actual : ∀ p, Ctx p) (hdepth : F.HasDepthAtMost H) (hmeas : F.IsTimeMeasurable)
    {b : ι → ι → ℝ} {S : ℝ} (hb : ∀ v u, 0 ≤ b v u)
    (hrow : ∀ v, ∑ u, b v u ≤ S) (hcol : ∀ u, ∑ v, b v u ≤ S)
    (hpointwiseAn : IsPointwiseAnalyticEnvelope F π
      (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
      Ca Ks Ls b)
    (htrans : F.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
        (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
      (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
    (hquiet : F.IsFastIndependentOn
      (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
    (pp : ℤ → P') (hk₁ : k₁ ∈ ocObsPulses α q Λ m tp (tp + Tobs))
    (hout : ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp (tp + Tobs) ⊆
      (F.piece (pp k₁)).output) :
    IsLiftSetting
      (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
        (Real.sqrt (B * ocTauPP α q Λ m))
        (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k₁
        (F.fiber (pp k₁) (actual (pp k₁)))) π
      (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m) ν B (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1))
      (ocEll q Λ m ν) (ocDStar q Λ m ν B)
      (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
      (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
      (EntryWeakProofs.pulseParallel k₁) (EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁)
      H N K k L qs qf (liftMetricConst g₀ CG) Cw (fun _ _ => Ca) b S := by
  have hνpos : 0 < ν := ν_pos cov
  have hBpos : 0 < B := B_pos cov
  have hk : Odd k₁ := obsPulse_odd hk₁
  have hE : 0 < ocEpsilon q Λ (m - 1) := E_pos q hΛ m
  have hρ : 0 < Real.sqrt (B * ocTauPP α q Λ m) := ρ_pos α q hΛ m hBpos
  have hlam : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    (div_pos hρ hE).le
  have hℓ : 0 < ocEll q Λ m ν ^ 2 := ocEll_sq_pos q hΛ m hνpos
  have hwin : ∀ t ∈ Set.Icc
      (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp (tp + Tobs) :=
    fun t ht => mul_mem_pulseWindow_inter hℓ ht
  have hwin' : ∀ t ∈ Set.Icc
      (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      ocEll q Λ m ν ^ 2 * t ∈ (F.piece (pp k₁)).output ∩ Set.Icc tp (tp + Tobs) :=
    fun t ht => ⟨hout (hwin t ht), (hwin t ht).2⟩
  exact
    { window := window ν hk₁
      e_pos := e_pos q hΛ m
      ν_pos := hνpos
      B_pos := hBpos
      ρ_pos := hρ
      E_pos := hE
      ℓ_eq := rfl
      η_eq := rfl
      η_le := η_le hΛ hζ hband (by omega) hmM hν hB
      dstar_eq := dstar_eq q Λ m hνpos.le B
      εc_eq := rfl
      εc_le := εc_le α q hΛ m hνpos.le hBpos cov.ellT
      lam_eq := rfl
      lam_le := lam_le α q hΛ m cov.RE
      N_ge := hN
      D_ge := hD
      qs_eq := hqs
      qf_eq := hqf
      mass_pos := hπ
      G_symm := G_symm α q Λ m Φ hφ ν B k₁
      G_meas := G_meas α q Λ m Φ hφ ν B k₁
      G_smooth := fun t _ => G_smooth α q Λ m Φ hφ ν B k₁ qs t
      G_ellip := G_ellip hΛ cov hg₀ hk₁
      G_jets := G_jets hΛ cov hg₀ hk₁ hqsJ
      v_shear := v_shear (α := α) (q := q) hΛ m ζ hνpos hk
      V_smooth := fun t _ => V_smooth α q Λ m ζ ν k₁ qf t
      V_per := fun t _ => V_per α q Λ m ζ ν k₁ t
      V_mean := fun t _ => V_mean α q Λ m ζ ν k₁ t
      v_meas := v_meas (α := α) (q := q) hΛ m hζ hνpos hk
      w_jets := fun n hn => hw _ _ qf n hn
      depth := hasDepthAtMost_liftEdges_fiber F (ocEll q Λ m ν ^ 2)
        (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) (pp k₁) (actual (pp k₁))
        hdepth
      transverse := fun _ _ _ _ hγ w =>
        isTransverseOn_coeff_liftEdges_fiber F hΛ hζ hk htrans hquiet (pp k₁) (actual (pp k₁))
          hout (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
          hwin hγ w
      coeff_meas := fun _ _ _ _ hγ w X z =>
        measurable_coeff_liftEdges_fiber F (ocEll q Λ m ν ^ 2)
          (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) (pp k₁) (actual (pp k₁))
          hmeas hγ w X z
      coeff_smooth := fun _ _ _ _ hγ w t ht =>
        isBoxSmooth_coeff_liftEdges_fiber F (Set.Icc tp (tp + Tobs)) (ocEpsilon q Λ (m - 1))
          hE.ne' (ocEll q Λ m ν ^ 2)
          (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) hqsK hqfL hpointwiseAn.1
          (pp k₁) (actual (pp k₁)) (hwin' t ht) hγ w
      envelope := isScaledJetEnvelope_liftEdges_fiber F π (Set.Icc tp (tp + Tobs)) hE hlam hqsK
        hqfL hb hrow hcol hpointwiseAn (pp k₁) (actual (pp k₁)) hwin' }

/-- **The lift setting of every observed pulse.** -/
theorem lift_setting (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (Cw : ℕ → ℝ), 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (g₀ Ca : ℝ) (CG : ℕ → ℝ), g₀ ≤ 1 / 4 → ∃ CGl : ℕ → ℝ,
      ∀ (H D N K k L qs qf Ks Ls qJ Kmax : ℕ), 2 ≤ D → 1 ≤ N →
        qs = K + 4 * (H + 1) * (N + D) ^ 2 →
        qf = max k (L + 2) + H * D + 2 * N + 2 * D →
        qs ≤ Ks → qf ≤ Ls → qs ≤ qJ →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tp Tobs ρs g a B₀ lam₀ Cb : ℝ)
        (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) ρs g g₀ a B₀ lam₀ Cb
          qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hmeas : F.IsTimeMeasurable)
        (b : ι → ι → ℝ) (S : ℝ) (_hb : ∀ v u, 0 ≤ b v u)
        (_hrow : ∀ v, ∑ u, b v u ≤ S) (_hcol : ∀ u, ∑ v, b v u ≤ S)
        (_hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls b)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (pp : ℤ → P') (k₁ : ℤ) (_hk₁ : k₁ ∈ ocObsPulses α q Λ m tp (tp + Tobs))
        (_hout : ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp (tp + Tobs) ⊆
          (F.piece (pp k₁)).output),
        ∃ (par : Fin 2) (V : ℝ → ℝ → ℝ),
          IsLiftSetting
            (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
              (Real.sqrt (B * ocTauPP α q Λ m))
              (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k₁
              (F.fiber (pp k₁) (actual (pp k₁)))) π
            (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
            (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
            (ocEpsilon q Λ m) ν B (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1))
            (ocEll q Λ m ν) (ocDStar q Λ m ν B)
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
            par V H N K k L qs qf CGl Cw (fun _ _ => Ca) b S := by
  obtain ⟨Λ₀, Cw, hΛ₀, hw⟩ := w_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, Cw, hΛ₀, ?_⟩
  intro Λ hΛ g₀ Ca CG hg₀
  refine ⟨liftMetricConst g₀ CG, ?_⟩
  intro H D N K k L qs qf Ks Ls qJ Kmax hD hN hqs hqf hqsK hqfL hqsJ ι _ h _ _ π hπ Φ M' κ hband
    m hm2 hmM ν B hν hB hφ tp Tobs ρs g a B₀ lam₀ Cb l₀ P y₀ cov P' Ctx F actual hdepth hmeas
    b S hb hrow hcol hpointwiseAn htrans hquiet pp k₁ hk₁ hout
  have hΛ1 : 1 ≤ Λ := by omega
  exact ⟨EntryWeakProofs.pulseParallel k₁, EntryWeakProofs.pulseShearProfile α q Λ m ζ ν k₁,
    isLiftSetting_pulse hΛ1 hζ hg₀ hD hN hqs hqf hqsK hqfL hqsJ hπ hband hm2 hmM hν hB
      (hw Λ hΛ M' κ hband m hm2 hmM ν B hν hB k₁ (obsPulse_odd hk₁)) cov F actual hdepth
      hmeas hb hrow hcol hpointwiseAn htrans hquiet pp hk₁ hout⟩

end AVRegularity.CycleComparison.LiftSetting
end
end
