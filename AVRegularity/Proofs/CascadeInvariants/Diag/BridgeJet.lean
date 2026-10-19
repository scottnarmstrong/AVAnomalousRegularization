-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Diag.Flat
public import AVRegularity.Proofs.ComplexContext.MetricExtInst
public import AVRegularity.Proofs.ComplexContext.Restrict
import AVRegularity.Proofs.GenSem.Jet.Chart
public import AVRegularity.Proofs.CascadeInvariants.Jet.Ops
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.GenSem.Op.FamChart

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the extension of the quadratic label mean and its flat value.** The
complex extension of the label mean `⟨w_κ χ_j⟩` of an appended family is built from the carrier-calculus
modes: the drift modes `±A_κ/2`, the flux modes `chiF` of the first corrector (transverse primitive
of `−w_j`) and the complex transverse inverse `chiW` with the complex metric of the family
(`metricExtOf`). Its flat counterpart `meanFlat` uses the metric `1`. Here:
* `conv_pm`: a convolution at mode zero against modes supported on `±1`;
* `norm_chiW_sub_flat_le`: the two inverses differ by `metricB(m) · (C_d/2)/(2π|h|(9/10)²)`,
  with `m = ownSize` (the complex metric is within `metricB(m)` of `1`, `norm_metricExtOf_sub_le`);
* `chiFlat_eq`: the flat modes `±1` are `−(2ℓ²)⁻¹ · flatMem`;
* `meanFlat_eq`: the flat label mean is `−A_κ flatMem_j/(2ℓ²)`, so that
  `−κ_{m−1}(meanFlat − η δ_{κj}) = 𝖩_m` by `flat_identity`. -/

section
open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow
  AVRegularity.Providers.ComplexCell AVRegularity.Providers.Transverse

section Defs

variable (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ)

/-- The modes `±A_j/2` of the component `j` of the drift. -/
def driftC (j : Fin 2) (h : ℤ) (t : ℝ) : ℂ :=
  if h = 1 ∨ h = -1 then ((driftAmp D m k j t / 2 : ℝ) : ℂ) else 0

/-- The flux modes of the first corrector: the transverse primitive of the source `−w_j`. -/
def chiF (j : Fin 2) (h : ℤ) (s : ℝ) : ℂ :=
  if h = 0 then 0 else (2 * Real.pi * Complex.I * (h : ℂ))⁻¹ * -driftC D m k j h s

/-- The modes of the source `−w_j`. -/
def srcW (j : Fin 2) (h : ℤ) : Ext := fun dd n t x => -driftW D m k j h dd n t x

/-- The modes of the first corrector with the complex metric of the family. -/
def chiW (j : Fin 2) (h : ℤ) : Ext :=
  invW D m k (metricExtOf D b j₀ m k) (transPrimW (srcW D m k j)) h

/-- The flat modes of the first corrector (metric `1`). -/
def chiFlat (j : Fin 2) (h : ℤ) (t : ℝ) : ℂ :=
  modeWC (D.cellScaleSq m) (fun _ => 1) (chiF D m k j h) (D.slotStart m k) h t

/-- The extension of the label mean `⟨w_κ χ_j⟩`. -/
def meanW (κ j : Fin 2) : Ext := fun dd n t x =>
  conv (fun h => driftW D m k κ h dd n t x) (fun h => chiW D b j₀ m k j h dd n t x) 0

/-- The flat label mean. -/
def meanFlat (κ j : Fin 2) (t : ℝ) : ℂ :=
  conv (fun h => driftC D m k κ h t) (fun h => chiFlat D m k j h t) 0

end Defs

variable {D : OCData} {b : ℝ} {j₀ m : ℕ} {k : ℤ}

theorem driftW_eq (j : Fin 2) (h : ℤ) (dd : ChainData) (n : ℕ) (t : ℝ) (x : ChainParamsC n) :
    driftW D m k j h dd n t x = driftC D m k j h t := rfl

theorem transPrimW_srcW (j : Fin 2) (h : ℤ) (dd : ChainData) (n : ℕ) (s : ℝ)
    (x : ChainParamsC n) : transPrimW (srcW D m k j) h dd n s x = chiF D m k j h s := by
  simp only [transPrimW, srcW, chiF, driftW_eq]

/-- **A convolution at mode zero** against modes supported on `±1`. -/
theorem conv_pm {a c : ℤ → ℂ} (ha : ∀ h, h ≠ 1 → h ≠ -1 → a h = 0) :
    conv a c 0 = a 1 * c (-1) + a (-1) * c 1 := by
  unfold conv
  rw [tsum_eq_sum (s := {1, -1}) fun h hh => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    rw [ha h hh.1 hh.2, zero_mul]]
  rw [Finset.sum_pair (by decide)]
  simp

theorem driftC_eq_zero {j : Fin 2} {h : ℤ} (h1 : h ≠ 1) (h2 : h ≠ -1) (t : ℝ) :
    driftC D m k j h t = 0 := by
  simp [driftC, h1, h2]

theorem norm_driftC_le (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.kap i)
    (hk : Odd k) {Cd : ℝ}
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1))) (j : Fin 2) (h : ℤ)
    (t : ℝ) : ‖driftC D m k j h t‖ ≤ Real.pi * Cd := by
  have hA := abs_driftAmp_le hΛ hζ hκ hk hCd j t
  have hCd0 : 0 ≤ Cd := by
    have := (abs_nonneg _).trans hA
    nlinarith [Real.pi_pos]
  unfold driftC
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    linarith
  · rw [norm_zero]; positivity

theorem norm_chiF_le (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.kap i)
    (hk : Odd k) {Cd : ℝ}
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1))) (j : Fin 2) (h : ℤ)
    (s : ℝ) : ‖chiF D m k j h s‖ ≤ Cd / 2 := by
  have hd := norm_driftC_le hΛ hζ hκ hk hCd j h s
  have hCd0 : 0 ≤ Cd := by
    have := (norm_nonneg _).trans hd
    nlinarith [Real.pi_pos]
  unfold chiF
  split_ifs with h0
  · rw [norm_zero]; positivity
  · rw [norm_mul, norm_neg, norm_inv]
    have hh : (1 : ℝ) ≤ |(h : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    have hn : ‖2 * Real.pi * Complex.I * (h : ℂ)‖ = 2 * Real.pi * |(h : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp
    rw [hn]
    have hp : 0 < 2 * Real.pi * |(h : ℝ)| := by positivity
    rw [inv_mul_le_iff₀ hp]
    have h2 : Real.pi * Cd ≤ Real.pi * Cd * |(h : ℝ)| :=
      le_mul_of_one_le_right (mul_nonneg Real.pi_pos.le hCd0) hh
    calc ‖driftC D m k j h s‖ ≤ Real.pi * Cd * |(h : ℝ)| := hd.trans h2
      _ = 2 * Real.pi * |(h : ℝ)| * (Cd / 2) := by ring

theorem continuous_chiF (hζ : IsFastProfile D.ζ) (j : Fin 2) (h : ℤ) :
    Continuous (chiF D m k j h) := by
  have hc : Continuous (driftAmp D m k j) := by
    unfold driftAmp
    exact continuous_const.mul (continuous_const.mul
      ((CycleReference.ocPulse_continuous hζ k).mul continuous_const))
  unfold chiF driftC
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (hc.div_const 2)).neg
  · exact continuous_const.mul continuous_const.neg

/-- **The complex metric of the family is within `metricB(ownSize)` of `1`.** -/
theorem norm_metricExtOf_sub_le {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (dd : ChainData) (n : ℕ)
    {u : ℝ} (hu : u ∈ ocPulseWindow D.α D.q D.Λ m k) (x : ChainParamsC n) :
    ‖metricExtOf D b j₀ m k dd n u x - 1‖ ≤ metricB (ownSize D m) := by
  unfold metricExtOf
  rw [add_sub_cancel_right]
  exact norm_ownLeafExt_le env m k (metricSub_entryFun _ _) dd n hu (finalZero x)

/-- **The complex and the flat inverses of the first corrector.** -/
theorem norm_chiW_sub_flat_le {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100)
    (hκ : ∀ i, 0 < D.kap i) (hk : Odd k) {Cd : ℝ}
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
    (hc : 0 < D.cellScaleSq m) {dd : ChainData} {n : ℕ} {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (j : Fin 2)
    {h : ℤ} (hh : h ≠ 0) :
    ‖chiW D b j₀ m k j h dd n t x - chiFlat D m k j h t‖ ≤
      metricB (ownSize D m) * (Cd / 2) / (2 * Real.pi * |(h : ℝ)| * (9 / 10) ^ 2) := by
  have hG := metricExtOf_spec (p := k) env hm
  have ht₀ : D.slotStart m k ∈ ocPulseWindow D.α D.q D.Λ m k :=
    history_subset ht ⟨le_rfl, slotStart_le ht⟩
  have hF : (fun s => transPrimW (srcW D m k j) h dd n s x) = chiF D m k j h :=
    funext fun s => transPrimW_srcW j h dd n s x
  unfold chiW invW chiFlat
  rw [hF]
  exact norm_modeWC_sub_le hc (by norm_num : (0 : ℝ) < 9 / 10) hh (slotStart_le ht)
    (hG.intervalIntegrable hx ht₀ ht) intervalIntegrable_const
    ((continuous_chiF env.hζ j h).intervalIntegrable _ _)
    (fun u hu => hG.re dd n u (history_subset ht hu) x hx)
    (fun u _ => by simp only [Complex.one_re]; norm_num)
    (fun u hu => norm_metricExtOf_sub_le env dd n (history_subset ht hu) x)
    (fun s _ => norm_chiF_le env.hΛ1 env.hζ hκ hk hCd j h s)

/-- **The flat modes `±1` of the first corrector.** -/
theorem chiFlat_eq (hc : 0 < D.cellScaleSq m) (j : Fin 2) {h : ℤ} (hh : h = 1 ∨ h = -1)
    (t : ℝ) :
    chiFlat D m k j h t = ((-(1 / (2 * D.cellScaleSq m)) * flatMem D m k j t : ℝ) : ℂ) := by
  have h0 : h ≠ 0 := by rcases hh with rfl | rfl <;> decide
  have hsq : ((h : ℝ)) ^ 2 = 1 := by rcases hh with rfl | rfl <;> norm_num
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast h0
  have hcc : (D.cellScaleSq m : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpt : ∀ s, modeCoup (D.cellScaleSq m) h *
      (modeKC (D.cellScaleSq m) (fun _ => 1) h t s * chiF D m k j h s) =
      ((-(1 / (2 * D.cellScaleSq m)) * (Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s))) *
        driftAmp D m k j s) : ℝ) : ℂ) := by
    intro s
    have hK : modeKC (D.cellScaleSq m) (fun _ => 1) h t s =
        ((Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s))) : ℝ) : ℂ) := by
      unfold modeKC modeRate
      rw [intervalIntegral.integral_const, hsq, Complex.real_smul, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hK]
    simp only [chiF, h0, ↓reduceIte, driftC, hh, modeCoup]
    push_cast
    field_simp
  unfold chiFlat modeWC
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  rfl

/-- **The flat label mean.** -/
theorem meanFlat_eq (hc : 0 < D.cellScaleSq m) (κ j : Fin 2) (t : ℝ) :
    meanFlat D m k κ j t =
      ((-(driftAmp D m k κ t * flatMem D m k j t) / (2 * D.cellScaleSq m) : ℝ) : ℂ) := by
  unfold meanFlat
  rw [conv_pm fun h h1 h2 => driftC_eq_zero h1 h2 t, chiFlat_eq hc j (Or.inr rfl),
    chiFlat_eq hc j (Or.inl rfl)]
  simp only [driftC, true_or, or_true, ↓reduceIte]
  push_cast
  field_simp
  ring

/-- **The flat label mean cancels the reference flux.** -/
theorem meanFlat_identity (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.kap i)
    (hκm : D.kap m = D.κ m) (hc : 0 < D.cellScaleSq m) (hk : Odd k) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (κ j : Fin 2) :
    -(D.kap (m - 1) : ℂ) * (meanFlat D m k κ j t -
        ((D.kap m / D.kap (m - 1) * (if κ = j then 1 else 0) : ℝ) : ℂ)) =
      ((ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t κ j : ℝ) : ℂ) := by
  rw [meanFlat_eq hc, ← flat_identity hΛ hζ hκ hκm hk ht κ j]
  have hB : (D.kap (m - 1) : ℂ) ≠ 0 := by exact_mod_cast (hκ (m - 1)).ne'
  have hc' : (D.cellScaleSq m : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring

/-- **The complex and the flat label means.** -/
theorem norm_meanW_sub_flat_le {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀)
    (hm : ownSize D m ≤ 1 / 100) (hκ : ∀ i, 0 < D.kap i) (hk : Odd k) {Cd : ℝ}
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
    (hc : 0 < D.cellScaleSq m) {dd : ChainData} {n : ℕ} {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k)
    (κ j : Fin 2) :
    ‖meanW D b j₀ m k κ j dd n t x - meanFlat D m k κ j t‖ ≤ Cd ^ 2 * metricB (ownSize D m) := by
  have hd := fun h => norm_driftC_le env.hΛ1 env.hζ hκ hk hCd κ h t
  have hCd0 : 0 ≤ Cd := by
    have := (norm_nonneg _).trans (hd 1)
    nlinarith [Real.pi_pos]
  have hB0 : 0 ≤ metricB (ownSize D m) := (norm_nonneg _).trans
    (norm_metricExtOf_sub_le env dd n ht x)
  have h1 := norm_chiW_sub_flat_le env hm hκ hk hCd hc hx ht j (h := 1) (by decide)
  have h2 := norm_chiW_sub_flat_le env hm hκ hk hCd hc hx ht j (h := -1) (by decide)
  simp only [Int.cast_one, abs_one, Int.cast_neg, abs_neg, mul_one] at h1 h2
  unfold meanW meanFlat
  rw [conv_pm fun h h1 h2 => by rw [driftW_eq]; exact driftC_eq_zero h1 h2 t,
    conv_pm fun h h1 h2 => driftC_eq_zero h1 h2 t]
  simp only [driftW_eq]
  have e : driftC D m k κ 1 t * chiW D b j₀ m k j (-1) dd n t x +
      driftC D m k κ (-1) t * chiW D b j₀ m k j 1 dd n t x -
      (driftC D m k κ 1 t * chiFlat D m k j (-1) t + driftC D m k κ (-1) t * chiFlat D m k j 1 t) =
      driftC D m k κ 1 t * (chiW D b j₀ m k j (-1) dd n t x - chiFlat D m k j (-1) t) +
        driftC D m k κ (-1) t * (chiW D b j₀ m k j 1 dd n t x - chiFlat D m k j 1 t) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hden : 0 < 2 * Real.pi * (9 / 10 : ℝ) ^ 2 := by positivity
  have hq : metricB (ownSize D m) * (Cd / 2) / (2 * Real.pi * (9 / 10) ^ 2) ≤
      Cd * metricB (ownSize D m) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [Real.pi_pos, mul_nonneg hCd0 hB0]
  calc ‖driftC D m k κ 1 t‖ * ‖chiW D b j₀ m k j (-1) dd n t x - chiFlat D m k j (-1) t‖ +
        ‖driftC D m k κ (-1) t‖ * ‖chiW D b j₀ m k j 1 dd n t x - chiFlat D m k j 1 t‖
      ≤ Real.pi * Cd * (Cd * metricB (ownSize D m) / (2 * Real.pi)) +
        Real.pi * Cd * (Cd * metricB (ownSize D m) / (2 * Real.pi)) := by
        gcongr
        · exact hd 1
        · exact h2.trans hq
        · exact hd (-1)
        · exact h1.trans hq
    _ = Cd ^ 2 * metricB (ownSize D m) := by
        field_simp
        ring

/-- **The size of the reference flux** on the pulse window. -/
theorem abs_ocRefFlux_le (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.kap i)
    (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1)) (hc : 0 < D.cellScaleSq m)
    (hk : Odd k) {Cd : ℝ}
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1))) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (κ j : Fin 2) :
    |ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t κ j| ≤ D.kap (m - 1) * (Cd ^ 2 / 2 + 1) := by
  rw [← flat_identity hΛ hζ hκ hκm hk ht κ j]
  have hA := fun c s => abs_driftAmp_le hΛ hζ hκ hk hCd c s
  have hCd0 : 0 ≤ Cd := by
    have := (abs_nonneg _).trans (hA κ t)
    nlinarith [Real.pi_pos]
  have hr : 0 < 4 * Real.pi ^ 2 / D.cellScaleSq m := by positivity
  have hmem : |flatMem D m k j t| ≤ 2 * Real.pi * Cd * (D.cellScaleSq m / (4 * Real.pi ^ 2)) := by
    unfold flatMem
    have hst : D.slotStart m k ≤ t := slotStart_le ht
    refine (intervalIntegral.abs_integral_le_integral_abs hst).trans ?_
    calc ∫ s in D.slotStart m k..t,
          |Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s))) * driftAmp D m k j s|
        ≤ ∫ s in D.slotStart m k..t,
          Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s))) * (2 * Real.pi * Cd) := by
          refine intervalIntegral.integral_mono_on hst ?_ ?_ fun s _ => ?_
          · have hc' : Continuous (driftAmp D m k j) := by
              unfold driftAmp
              exact continuous_const.mul (continuous_const.mul
                ((CycleReference.ocPulse_continuous hζ k).mul continuous_const))
            exact (((Real.continuous_exp.comp (by fun_prop)).mul hc').abs).intervalIntegrable _ _
          · exact ((Real.continuous_exp.comp (by fun_prop)).mul
              continuous_const).intervalIntegrable _ _
          · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (hA j s) (Real.exp_pos _).le
      _ = (∫ s in D.slotStart m k..t,
            Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s)))) * (2 * Real.pi * Cd) := by
          rw [intervalIntegral.integral_mul_const]
      _ ≤ 1 / (4 * Real.pi ^ 2 / D.cellScaleSq m) * (2 * Real.pi * Cd) :=
          mul_le_mul_of_nonneg_right (integral_exp_decay_le hr _ _) (by positivity)
      _ = 2 * Real.pi * Cd * (D.cellScaleSq m / (4 * Real.pi ^ 2)) := by
          field_simp
  have hB0 := hκ (m - 1)
  have hδ : |D.kap m * (if κ = j then (1 : ℝ) else 0)| ≤ D.kap (m - 1) := by
    split_ifs <;> simp [abs_of_pos (hκ m), hκle, hB0.le]
  calc |D.kap (m - 1) * (driftAmp D m k κ t * flatMem D m k j t) / (2 * D.cellScaleSq m) +
        D.kap m * (if κ = j then 1 else 0)|
      ≤ |D.kap (m - 1) * (driftAmp D m k κ t * flatMem D m k j t) / (2 * D.cellScaleSq m)| +
          D.kap (m - 1) := (abs_add_le _ _).trans (add_le_add le_rfl hδ)
    _ ≤ D.kap (m - 1) * (2 * Real.pi * Cd * (2 * Real.pi * Cd *
          (D.cellScaleSq m / (4 * Real.pi ^ 2)))) / (2 * D.cellScaleSq m) + D.kap (m - 1) := by
        gcongr
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hB0, abs_of_pos (by positivity :
          (0 : ℝ) < 2 * D.cellScaleSq m)]
        gcongr
        exact hA κ t
    _ = D.kap (m - 1) * (Cd ^ 2 / 2 + 1) := by
        field_simp
        ring
end

/-! **Ledger, first source: the invariant of the label tensor `Ŝ₀ = K^lab_2 − F⁻¹𝖩_mF⁻ᵀ` with a
small profile.** On the families of level `m` over the finer slot `k` (invariant `FamInv` of the carrier calculus),
the label tensor `sHat` of the bridge has the explicit extension `sHatW`, assembled from the
carrier-calculus constructors (drift, transverse primitive, complex transverse inverse, product, mean, own
letters through `finalZero`, time letters), and its profile is
`14(C_d² + 1) κ_{m−1} ownSize(m)` at the zero mode (`famInv_sHat`): the complex label mean is
within `C_d² metricB` of its flat value (`norm_meanW_sub_flat_le`), the flat value cancels `𝖩_m`
exactly (`meanFlat_identity`), and the letters `𝒢 − I`, `F⁻¹ − I` are of size `metricB`, `invB`
of `ownSize(m)` (`norm_ownLeafExt_le`). -/

section
open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow
  AVRegularity.Providers.ComplexCell AVRegularity.Providers.Transverse

/-! ### Linear bounds of the letter sizes -/

theorem invB_le_two_mul {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 100) :
    m * (1 + m) / (1 - m) ^ 2 ≤ 2 * m := by
  rw [div_le_iff₀ (by nlinarith)]
  have h1 : 1 + m ≤ 2 * (1 - m) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hm0]

theorem metricB_le_five_mul {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 100) : metricB m ≤ 5 * m := by
  unfold metricB
  have h1 := invB_le_two_mul hm0 hm
  have h0 : 0 ≤ m * (1 + m) / (1 - m) ^ 2 := by
    have : 0 < (1 - m) ^ 2 := by nlinarith
    positivity
  nlinarith

theorem ownSize_nonneg' {D : OCData} (hΛ : 1 ≤ D.Λ) (i : ℕ) : 0 ≤ ownSize D i := by
  unfold ownSize
  exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
    (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _))
    (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos hΛ).le)

variable {D : OCData} {b : ℝ} {j₀ i m : ℕ} {p k : ℤ}

/-! ### Family invariants -/

/-- A family invariant with a profile given by a direct bound of its extension. -/
theorem famInv_of_bound {f : GenSort.Sem .fam} {G : Ext} {B B' : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p f G B)
    (h : ∀ mres : ℝ, 0 ≤ mres → mres ≤ 2 → ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
      ∀ dd n, AdmData D b j₀ i p dd n → ∀ x ∈ carrierC D b dd n mres, ‖G dd n t x‖ₑ ≤ B' mres 0 t) :
    AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p f G B' :=
  { hF with mode := h }

/-- **Finite sums of family invariants.** -/
theorem famInv_finsetSum {ι : Type*} (s : Finset ι) {f : ι → GenSort.Sem .fam} {G : ι → Ext}
    {B : ι → ℝ → ℤ → ℝ → ℝ≥0∞} (h : ∀ a ∈ s, AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p (f a) (G a) (B a)) :
    AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p (fun t ch => ∑ a ∈ s, f a t ch) (fun dd n t x => ∑ a ∈ s, G a dd n t x)
      (fun mres h t => ∑ a ∈ s, B a mres h t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := AVRegularity.Providers.ComplexContext.FamInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p)
      (L := TimeLetter.const 0) continuous_const
    simp only [Finset.sum_empty]
    refine famInv_of_bound (h0.congr fun _ _ _ _ => rfl) fun _ _ _ _ _ _ _ _ _ _ => by
      simp
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
    simp only [Finset.sum_insert ha]
    exact h1

/-- **The own letters of a family**, through the final-phase projection. -/
theorem famInv_ownLeaf {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) :
    AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p (fun t ch => φ (ch.famJac D t))
      (fun dd n t x => ownLeafExt D b j₀ i p Φ dd n t (finalZero x))
      (fun _ h _ => if h = 0 then ENNReal.ofReal (B (ownSize D i)) else 0) := by
  have hext := ownLeaf_isHolExtension env i p hΦ
  have hfz : ∀ dd n x, x ∈ carrierC D b dd n 2 → finalZero x ∈ carrierC D b dd n 2 :=
    fun dd n x hx => carrierC_final_zero (by norm_num) hx env.hb0
  have hbd : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x : ChainParamsC n,
      ‖ownLeafExt D b j₀ i p Φ dd n t (finalZero x)‖ ≤ B (ownSize D i) := fun dd n t ht x =>
    norm_ownLeafExt_le env i p hΦ dd n ht (finalZero x)
  refine ⟨fun dd n t ht => ?_, fun dd n x _ => ?_, fun dd n t x z => rfl,
    fun ch t ht hch => ?_, fun dd n t ht x hx k v hv => ?_, fun dd n x _ => ?_,
    fun mres _ _ t ht dd n _ x _ => ?_⟩
  · exact (hext.1 dd n t ht).comp (differentiable_finalZero n).differentiableOn
      fun x hx => hfz dd n x hx
  · exact hext.2.1.1 dd n (finalZero x)
  · have hz : finalZero (ch.paramsC 0) = ch.paramsC 0 := by
      refine Prod.ext rfl (Prod.ext rfl (funext fun a => ?_))
      simp [finalZero, RealChain.paramsC]
    show ownLeafExt D b j₀ i p Φ ch.data ch.children.length t (finalZero (ch.paramsC 0)) = _
    rw [hz]
    exact hext.2.2 ch t ht 0 hch
  · show ownLeafExt D b j₀ i p Φ dd n t (finalZero (x.shiftChild k v)) =
      ownLeafExt D b j₀ i p Φ dd n t (finalZero x)
    rw [show finalZero (x.shiftChild k v) = (finalZero x).shiftChild k v from rfl,
      ownLeafExt_shiftChild env.hΛ1 _ t _ k hv]
  · exact ⟨Set.univ, Filter.univ_mem, B (ownSize D i), fun t ht y _ => hbd dd n t ht y⟩
  · simp only [↓reduceIte]
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hbd dd n t ht x)

/-- A family invariant with an extension that agrees pointwise. -/
theorem famInv_congrW {f : GenSort.Sem .fam} {G G' : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p f G B) (hG : ∀ dd n t x, G dd n t x = G' dd n t x) :
    AVRegularity.Providers.ComplexContext.FamInv D b j₀ i p f G' B := by
  have : G = G' := funext fun dd => funext fun n => funext fun t => funext fun x => hG dd n t x
  subst this
  exact hF

/-- A cell invariant with modes that agree pointwise. -/
theorem cellInv_congrW {f : GenSort.Sem .cell} {W W' : ℤ → Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : AVRegularity.Providers.ComplexContext.CellInv D b j₀ i p f W B) (hW : ∀ h dd n t x, W h dd n t x = W' h dd n t x) :
    AVRegularity.Providers.ComplexContext.CellInv D b j₀ i p f W' B := by
  have : W = W' := funext fun h => funext fun dd => funext fun n => funext fun t => funext fun x =>
    hW h dd n t x
  subst this
  exact hF

/-- A convolution against a single zero mode. -/
theorem conv_delta (c : ℂ) (a : ℤ → ℂ) (h : ℤ) :
    conv (fun k => if k = 0 then c else 0) a h = c * a h := by
  unfold conv
  rw [tsum_eq_single 0 fun k hk => by simp [hk]]
  simp

/-! ### The label tensor -/

/-- The label tensor `Ŝ₀ = K^lab_2 − F⁻¹𝖩_mF⁻ᵀ` of a family. -/
def sHat (D : OCData) (m : ℕ) (k : ℤ) (κ j : Fin 2) : GenSort.Sem .fam :=
  fun t A => kLab D m k κ j t A -
    ((A.famJac D t)⁻¹ * refJ D m t * ((A.famJac D t)⁻¹).transpose) κ j

/-- The own letter `F⁻¹ − I` (entry `(a, c)`) at the family level. -/
def invLetW (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (a c : Fin 2) : Ext :=
  fun dd n t x => ownLeafExt D b j₀ m k (fun A => A⁻¹ a c - (if a = c then 1 else 0)) dd n t
    (finalZero x)

/-- The own letter `𝒢 − I` (entry `(a, c)`) at the family level. -/
def metLetW (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (a c : Fin 2) : Ext :=
  fun dd n t x => ownLeafExt D b j₀ m k
    (fun A => (A⁻¹ * A⁻¹.transpose) a c - (if a = c then 1 else 0)) dd n t (finalZero x)

/-- **The extension of the label tensor.** -/
def sHatW (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (κ j : Fin 2) : Ext := fun dd n t x =>
  ((-D.kap (m - 1) : ℝ) : ℂ) * (meanW D b j₀ m k κ j dd n t x +
    ((-(D.kap m / D.kap (m - 1)) : ℝ) : ℂ) *
      (metLetW D b j₀ m k κ j dd n t x + ((if κ = j then 1 else 0 : ℝ) : ℂ))) +
  ((-1 : ℝ) : ℂ) * ∑ a : Fin 2, ∑ c : Fin 2,
    (invLetW D b j₀ m k κ a dd n t x + ((if κ = a then 1 else 0 : ℝ) : ℂ)) *
      (((ocRefFlux D.α D.q D.Λ D.ζ m (D.kap m) t a c : ℝ) : ℂ) *
        (invLetW D b j₀ m k j c dd n t x + ((if j = c then 1 else 0 : ℝ) : ℂ)))

section Assemble

variable {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100)
  (hκ : ∀ i, 0 < D.kap i) (hk : Odd k) {Cd : ℝ}
  (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
  (hc : 0 < D.cellScaleSq m)
include env hκ hk hCd

/-- The cell invariant of the source of the first corrector. -/
theorem cellInv_src (j : Fin 2) :
    ∃ B, AVRegularity.Providers.ComplexContext.CellInv D b j₀ m k (srcSem D m k j) (srcW D m k j) B := by
  have hd := AVRegularity.Providers.ComplexContext.CellInv.drift (b := b) (j₀ := j₀) env.hΛ1 env.hζ hκ hk hCd j
  have ht := AVRegularity.Providers.ComplexContext.CellInv.time (D := D) (b := b) (j₀ := j₀) (i := m) (p := k)
    (L := TimeLetter.const (-1)) continuous_const
  have h1 := AVRegularity.Providers.ComplexContext.CellInv.mul env.hΛ1 env.hb0 ht hd
  refine ⟨_, (cellInv_congrW h1 fun h dd n t x => ?_).congr fun t _ ch _ η => ?_⟩
  · rw [conv_delta]
    simp [srcW, TimeLetter.eval]
  · simp [GenSort.mul, GenSort.ofTime, TimeLetter.eval, srcSem]

include hm hc in
/-- The cell invariant of the first corrector. -/
theorem cellInv_chi (j : Fin 2) :
    ∃ B, AVRegularity.Providers.ComplexContext.CellInv D b j₀ m k (chiSem D m k j) (chiW D b j₀ m k j) B := by
  obtain ⟨B, hs⟩ := cellInv_src env hκ hk hCd j
  have htp := AVRegularity.Providers.ComplexContext.CellInv.transPrim env.hΛ1 env.hb0 hs
  have hW : AVRegularity.Providers.ComplexContext.CellInv D b j₀ m k (chiFlux D m k j (transverseIndex k)) (transPrimW (srcW D m k j))
      (fun mres h t => modeGain h * B mres h t) := by
    have e : chiFlux D m k j (transverseIndex k) = transversePrimitiveSem k (srcSem D m k j) := by
      simp [chiFlux]
    rw [e]
    exact htp
  exact ⟨_, AVRegularity.Providers.ComplexContext.CellInv.cellInv (fF := chiFlux D m k j) env.hΛ1 env.hb0 hc hW
    (metricExtOf_spec env hm)⟩

include hm hc in
/-- The family invariant of the label mean `⟨w_κ χ_j⟩`. -/
theorem famInv_mean (κ j : Fin 2) :
    ∃ B, AVRegularity.Providers.ComplexContext.FamInv D b j₀ m k (cellMeanSem (GenSort.mul .cell (driftSem D m k κ) (chiSem D m k j)))
      (meanW D b j₀ m k κ j) B := by
  obtain ⟨B, hχ⟩ := cellInv_chi env hm hκ hk hCd hc j
  have hd := AVRegularity.Providers.ComplexContext.CellInv.drift (b := b) (j₀ := j₀) env.hΛ1 env.hζ hκ hk hCd κ
  exact ⟨_, AVRegularity.Providers.ComplexContext.CellInv.mean env.hΛ1 env.hb0 (AVRegularity.Providers.ComplexContext.CellInv.mul env.hΛ1 env.hb0 hd hχ)⟩

include hm hc in
/-- **The family invariant of the label tensor** (structural profile). -/
theorem famInv_sHatW_struct (hκm : D.kap m = D.κ m) (κ j : Fin 2) :
    ∃ B, AVRegularity.Providers.ComplexContext.FamInv D b j₀ m k (sHat D m k κ j) (sHatW D b j₀ m k κ j) B := by
  obtain ⟨Bm, hM⟩ := famInv_mean env hm hκ hk hCd hc κ j
  have hT := fun L => AVRegularity.Providers.ComplexContext.FamInv.time (D := D) (b := b) (j₀ := j₀) (i := m) (p := k) (L := L)
    (continuous_timeLetter D env.hΛ1 env.hζ hκ L)
  have hMet := famInv_ownLeaf env m k (metricSub_entryFun κ j)
  have hInv := fun a c => famInv_ownLeaf env m k (invSub_entryFun a c)
  have h1 := (hT (.const (-D.kap (m - 1)))).mul (hM.add ((hT (.const (-(D.kap m / D.kap (m - 1))))).mul
    (hMet.add (hT (.const (if κ = j then 1 else 0))))))
  have h2 := famInv_finsetSum Finset.univ fun a _ => famInv_finsetSum Finset.univ fun c _ =>
    ((hInv κ a).add (hT (.const (if κ = a then 1 else 0)))).mul
      ((hT (.refFlux m a c)).mul ((hInv j c).add (hT (.const (if j = c then 1 else 0)))))
  have h3 := h1.add ((hT (.const (-1))).mul h2)
  refine ⟨_, famInv_congrW (h3.congr fun t _ A _ => ?_) fun dd n t x => rfl⟩
  simp only [GenSort.add, GenSort.mul, GenSort.ofTime, TimeLetter.eval, sHat, kLab, refJ,
    cellMeanSem, ← hκm, RealChain.famMetric]
  have hsum : ∑ a : Fin 2, ∑ c : Fin 2,
      ((A.famJac D t)⁻¹ κ a - (if κ = a then 1 else 0) + (if κ = a then 1 else 0)) *
        (ocRefFlux D.α D.q D.Λ D.ζ m (D.kap m) t a c *
          ((A.famJac D t)⁻¹ j c - (if j = c then 1 else 0) + (if j = c then 1 else 0))) =
      ((A.famJac D t)⁻¹ * ocRefFlux D.α D.q D.Λ D.ζ m (D.kap m) t *
        ((A.famJac D t)⁻¹).transpose) κ j := by
    simp only [sub_add_cancel, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hsum]
  simp only [sub_add_cancel]
  ring

/-- **The extension of the label tensor is small**: of size `14(C_d² + 1) κ_{m−1} ownSize(m)`. -/
theorem norm_sHatW_le (hm : ownSize D m ≤ 1 / 100) (hc : 0 < D.cellScaleSq m)
    (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1)) {dd : ChainData} {n : ℕ}
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (κ j : Fin 2) :
    ‖sHatW D b j₀ m k κ j dd n t x‖ ≤ 14 * (Cd ^ 2 + 1) * D.kap (m - 1) * ownSize D m := by
  set s := ownSize D m with hsdef
  have hs0 : 0 ≤ s := ownSize_nonneg' env.hΛ1 m
  have hB0 : 0 < D.kap (m - 1) := hκ (m - 1)
  set M := meanW D b j₀ m k κ j dd n t x
  set Mf := meanFlat D m k κ j t
  set E := metLetW D b j₀ m k κ j dd n t x
  set I : Fin 2 → Fin 2 → ℂ := fun a c => invLetW D b j₀ m k a c dd n t x with hI
  set J : Fin 2 → Fin 2 → ℂ := fun a c => ((ocRefFlux D.α D.q D.Λ D.ζ m (D.kap m) t a c : ℝ) : ℂ)
    with hJ
  have hE : ‖E‖ ≤ metricB s := norm_ownLeafExt_le env m k (metricSub_entryFun κ j) dd n ht _
  have hIb : ∀ a c, ‖I a c‖ ≤ 2 * s := fun a c =>
    (norm_ownLeafExt_le env m k (invSub_entryFun a c) dd n ht _).trans (invB_le_two_mul hs0 hm)
  have hJb : ∀ a c, ‖J a c‖ ≤ D.kap (m - 1) * (Cd ^ 2 / 2 + 1) := fun a c => by
    simp only [hJ, Complex.norm_real, Real.norm_eq_abs]
    rw [hκm]
    exact abs_ocRefFlux_le env.hΛ1 env.hζ hκ hκm hκle hc hk hCd ht a c
  have hMb : ‖M - Mf‖ ≤ Cd ^ 2 * metricB s :=
    norm_meanW_sub_flat_le env hm hκ hk hCd hc hx ht κ j
  have hId := meanFlat_identity env.hΛ1 env.hζ hκ hκm hc hk ht κ j
  rw [← hκm] at hId
  have hdec : sHatW D b j₀ m k κ j dd n t x =
      -(D.kap (m - 1) : ℂ) * (M - Mf) + ((D.kap m : ℝ) : ℂ) * E -
        (∑ a : Fin 2, I κ a * J a j + ∑ c : Fin 2, J κ c * I j c +
          ∑ a : Fin 2, ∑ c : Fin 2, I κ a * (J a c * I j c)) := by
    have hexp : ∑ a : Fin 2, ∑ c : Fin 2,
        (I κ a + ((if κ = a then 1 else 0 : ℝ) : ℂ)) *
          (J a c * (I j c + ((if j = c then 1 else 0 : ℝ) : ℂ))) =
        ∑ a : Fin 2, ∑ c : Fin 2, I κ a * (J a c * I j c) + ∑ a : Fin 2, I κ a * J a j +
          ∑ c : Fin 2, J κ c * I j c + J κ j := by
      simp only [Fin.sum_univ_two]
      fin_cases κ <;> fin_cases j <;> simp <;> ring
    have hJκ : J κ j = -(D.kap (m - 1) : ℂ) *
        (Mf - ((D.kap m / D.kap (m - 1) * (if κ = j then 1 else 0) : ℝ) : ℂ)) := by
      rw [hId]
    unfold sHatW
    rw [show (∑ a : Fin 2, ∑ c : Fin 2,
        (invLetW D b j₀ m k κ a dd n t x + ((if κ = a then 1 else 0 : ℝ) : ℂ)) *
          (((ocRefFlux D.α D.q D.Λ D.ζ m (D.kap m) t a c : ℝ) : ℂ) *
            (invLetW D b j₀ m k j c dd n t x + ((if j = c then 1 else 0 : ℝ) : ℂ)))) =
        ∑ a : Fin 2, ∑ c : Fin 2,
        (I κ a + ((if κ = a then 1 else 0 : ℝ) : ℂ)) *
          (J a c * (I j c + ((if j = c then 1 else 0 : ℝ) : ℂ))) from rfl, hexp, hJκ]
    have hBc : (D.kap (m - 1) : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
    push_cast
    field_simp
    ring
  rw [hdec]
  have hmB := metricB_le_five_mul hs0 hm
  have hBn : ‖(D.kap (m - 1) : ℂ)‖ = D.kap (m - 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
  have hBηn : ‖((D.kap m : ℝ) : ℂ)‖ ≤ D.kap (m - 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hκ m)]
    exact hκle
  have hS1 : ‖∑ a : Fin 2, I κ a * J a j‖ ≤ 2 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Fin.sum_univ_two, norm_mul]
    nlinarith [hIb κ 0, hIb κ 1, hJb 0 j, hJb 1 j, norm_nonneg (I κ 0), norm_nonneg (I κ 1),
      norm_nonneg (J 0 j), norm_nonneg (J 1 j)]
  have hS2 : ‖∑ c : Fin 2, J κ c * I j c‖ ≤ 2 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Fin.sum_univ_two, norm_mul]
    nlinarith [hIb j 0, hIb j 1, hJb κ 0, hJb κ 1, norm_nonneg (I j 0), norm_nonneg (I j 1),
      norm_nonneg (J κ 0), norm_nonneg (J κ 1)]
  have hS3 : ‖∑ a : Fin 2, ∑ c : Fin 2, I κ a * (J a c * I j c)‖ ≤
      4 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1) * (2 * s))) := by
    have hterm : ∀ a c, ‖I κ a * (J a c * I j c)‖ ≤ 2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1) * (2 * s)) :=
      fun a c => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (hIb κ a) (mul_le_mul (hJb a c) (hIb j c) (norm_nonneg _)
          (by positivity)) (by positivity) (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
    simp only [Fin.sum_univ_two]
    linarith [hterm 0 0, hterm 0 1, hterm 1 0, hterm 1 1]
  have hCd2 : 0 ≤ Cd ^ 2 := sq_nonneg Cd
  calc ‖-(D.kap (m - 1) : ℂ) * (M - Mf) + ((D.kap m : ℝ) : ℂ) * E -
        (∑ a : Fin 2, I κ a * J a j + ∑ c : Fin 2, J κ c * I j c +
          ∑ a : Fin 2, ∑ c : Fin 2, I κ a * (J a c * I j c))‖
      ≤ D.kap (m - 1) * (Cd ^ 2 * metricB s) + D.kap (m - 1) * metricB s +
          (2 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1))) + 2 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1))) +
            4 * (2 * s * (D.kap (m - 1) * (Cd ^ 2 / 2 + 1) * (2 * s)))) := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
          ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hS1 hS2))
            hS3)))
        · rw [norm_mul, norm_neg, hBn]
          exact mul_le_mul_of_nonneg_left hMb hB0.le
        · rw [norm_mul]
          exact mul_le_mul hBηn hE (norm_nonneg _) hB0.le
    _ ≤ 14 * (Cd ^ 2 + 1) * D.kap (m - 1) * s := by
        have h1 : D.kap (m - 1) * (Cd ^ 2 * metricB s) ≤ D.kap (m - 1) * (Cd ^ 2 * (5 * s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmB hCd2) hB0.le
        have h2 : D.kap (m - 1) * metricB s ≤ D.kap (m - 1) * (5 * s) :=
          mul_le_mul_of_nonneg_left hmB hB0.le
        have h3 : s * s ≤ s / 100 := by nlinarith
        nlinarith [mul_nonneg hB0.le hs0, mul_nonneg (mul_nonneg hB0.le hs0) hCd2,
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0.le (by positivity : (0 : ℝ) ≤ Cd ^ 2 / 2 + 1))]

include hm hc in
/-- **The family invariant of the label tensor with the small profile.** -/
theorem famInv_sHat (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1)) (κ j : Fin 2) :
    AVRegularity.Providers.ComplexContext.FamInv D b j₀ m k (sHat D m k κ j) (sHatW D b j₀ m k κ j)
      (fun _ h _ => if h = 0 then
        ENNReal.ofReal (14 * (Cd ^ 2 + 1) * D.kap (m - 1) * ownSize D m) else 0) := by
  obtain ⟨B, hF⟩ := famInv_sHatW_struct env hm hκ hk hCd hc hκm κ j
  refine famInv_of_bound hF fun mres _ hm2 t ht dd n _ x hx => ?_
  simp only [↓reduceIte]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_sHatW_le env hκ hk hCd hm hc hκm hκle
    (carrierC_mono env.hb0.le hm2 hx) ht κ j)

end Assemble
end

end AVRegularity.Providers.CascadeInvariants
end

section
open MeasureTheory Set Filter Topology Homogenization
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: sized family functions with carrier-calculus invariants.** `famInvQ` is the
sized algebra (`RepAlgQ`) of the functions of an index `l : Λ` (a time and a family of level `m`
over the finer slot `k`, through `π`) that agree with the semantic function of a carrier-calculus family
invariant (`FamInv`) whose profile is the normalized zero-mode profile `profQ Δ μ₀ r C`: the size
`C` while `r` reserve steps of length `Δ` are available below the budget `μ₀`. Sums add and products
multiply the sizes (`repAlgQ_famInvQ`); a label derivative of a covariant function (its value at the
label `w` is the semantic function at the recentered family) is the slow-label derivative of
the carrier calculus (`FamInv.dSlow`), of cost one reserve step and the factor `σ ≥ C_slow/(ε_{m−1}Δ)`
(`jetRepGQ_covariant_famInvQ`). -/

open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

/-- The normalized zero-mode profile: the size `C` while `r` reserve steps fit in the budget. -/
def profQ (Δ μ₀ : ℝ) (r : ℕ) (C : ℝ≥0) : ℝ → ℤ → ℝ → ℝ≥0∞ :=
  fun mres h _ => if h = 0 then (if mres + r * Δ ≤ μ₀ then (C : ℝ≥0∞) else ⊤) else 0

theorem profQ_ne_zero {Δ μ₀ : ℝ} {r : ℕ} {C : ℝ≥0} {h : ℤ} (hh : h ≠ 0) (mres t : ℝ) :
    profQ Δ μ₀ r C mres h t = 0 := by
  simp [profQ, hh]

theorem profQ_zero_le {Δ μ₀ : ℝ} {r : ℕ} {C : ℝ≥0} (mres t : ℝ) :
    profQ Δ μ₀ r C mres 0 t = if mres + r * Δ ≤ μ₀ then (C : ℝ≥0∞) else ⊤ := by
  simp [profQ]

theorem profQ_mono {Δ μ₀ : ℝ} (hΔ : 0 ≤ Δ) {r r' : ℕ} {C C' : ℝ≥0} (hr : r ≤ r') (hC : C ≤ C')
    (mres t : ℝ) : profQ Δ μ₀ r C mres 0 t ≤ profQ Δ μ₀ r' C' mres 0 t := by
  simp only [profQ_zero_le]
  by_cases h' : mres + r' * Δ ≤ μ₀
  · have hrr : (r : ℝ) * Δ ≤ r' * Δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hΔ
    have h : mres + r * Δ ≤ μ₀ := by linarith
    simp only [h, h', ↓reduceIte]
    exact_mod_cast hC
  · simp [h']

variable (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (Δ μ₀ : ℝ) {Λ : Type*}
  (π : Λ → ℝ × RealChain)

/-- **Sized family functions with the invariants `ComplexContext.FamInv`.** -/
def famInvQ : (Λ → ℝ) → ℕ → ℝ≥0 → Prop :=
  fun F r C => ∃ (f : GenSort.Sem .fam) (G : Ext), (∀ l, F l = f (π l).1 (π l).2) ∧
    ComplexContext.FamInv D b j₀ m k f G (profQ Δ μ₀ r C)

variable {D b j₀ m k Δ μ₀ π}

/-- A family invariant whose zero-mode profile is below `profQ` gives a sized function. -/
theorem famInvQ_of_famInv {f : GenSort.Sem .fam} {G : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞} {r : ℕ}
    {C : ℝ≥0} (hF : ComplexContext.FamInv D b j₀ m k f G B)
    (hB : ∀ mres t, 0 ≤ mres → mres ≤ 2 → t ∈ ocPulseWindow D.α D.q D.Λ m k →
      B mres 0 t ≤ profQ Δ μ₀ r C mres 0 t) :
    famInvQ D b j₀ m k Δ μ₀ π (fun l => f (π l).1 (π l).2) r C :=
  ⟨f, G, fun _ => rfl, hF.mono hB⟩

theorem repAlgQ_famInvQ (hΔ : 0 ≤ Δ) : RepAlgQ (famInvQ D b j₀ m k Δ μ₀ π) where
  mono := fun ⟨f, G, hF, hI⟩ hr hC =>
    ⟨f, G, hF, hI.mono fun mres t _ _ _ => profQ_mono hΔ hr hC mres t⟩
  const c := by
    refine ⟨GenSort.ofTime .fam (TimeLetter.eval D (.const c)), fun _ _ t _ => (c : ℂ),
      fun _ => rfl, (ComplexContext.FamInv.time (L := TimeLetter.const c) continuous_const).mono
        fun mres t _ _ _ => ?_⟩
    simp only [↓reduceIte, profQ_zero_le, TimeLetter.eval]
    split_ifs
    · rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg c)]
      exact le_of_eq (by congr 1; ext; simp)
    · exact le_top
  add := fun ⟨f₁, G₁, hF₁, hI₁⟩ ⟨f₂, G₂, hF₂, hI₂⟩ =>
    ⟨GenSort.add .fam f₁ f₂, _, fun l => by simp [GenSort.add, hF₁ l, hF₂ l],
      (hI₁.add hI₂).mono fun mres t _ _ _ => by
        simp only [profQ_zero_le]
        split_ifs
        · exact le_of_eq (by push_cast; rfl)
        · exact le_top⟩
  mul := fun ⟨f₁, G₁, hF₁, hI₁⟩ ⟨f₂, G₂, hF₂, hI₂⟩ =>
    ⟨GenSort.mul .fam f₁ f₂, _, fun l => by simp [GenSort.mul, hF₁ l, hF₂ l],
      (hI₁.mul hI₂).mono fun mres t _ _ _ => by
        rw [tsum_eq_single 0 fun k hk => by rw [profQ_ne_zero hk, zero_mul]]
        simp only [sub_zero, profQ_zero_le]
        split_ifs
        · exact le_of_eq (by push_cast; rfl)
        · exact le_top⟩

/-- **Covariant functions have sized jets**: the label derivative is the slow-label derivative of
the carrier calculus, of cost one reserve step and the factor `σ`. -/
theorem jetRepGQ_covariant_famInvQ {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hΔ : 0 < Δ)
    (hμ : μ₀ ≤ 2) {σ : ℝ≥0}
    (hσ : ENNReal.ofReal (12 / b) / ENNReal.ofReal (D.eps (m - 1) * Δ) ≤ σ) :
    ∀ (n : ℕ) {f : GenSort.Sem .fam} {G : Ext} {r : ℕ} {C : ℝ≥0},
      ComplexContext.FamInv D b j₀ m k f G (profQ Δ μ₀ r C) →
      JetRepGQ (famInvQ D b j₀ m k Δ μ₀ π) σ n (fun l w => f (π l).1 ((π l).2.recenter D w)) r C := by
  intro n
  induction n with
  | zero =>
    intro f G r C hF
    exact ⟨f, G, fun l => by simp only [recenter_zero D env.hζ], hF⟩
  | succ n ih =>
    intro f G r C hF
    refine ⟨⟨f, G, fun l => by simp only [recenter_zero D env.hζ], hF⟩, fun j => ?_⟩
    have hD := ComplexContext.FamInv.dSlow env hΔ le_rfl j hF
    have hD' : ComplexContext.FamInv D b j₀ m k
        (fun t ch => fderiv ℝ (fun h : Vec 2 => f t (ch.recenter D h)) 0 (basisVec j))
        (dSlowG D j₀ m k j G) (profQ Δ μ₀ (r + 1) (σ * C)) := by
      refine hD.mono fun mres t hm0 _ _ => ?_
      simp only [profQ_zero_le]
      push_cast
      by_cases h1 : mres + ((r : ℝ) + 1) * Δ ≤ μ₀
      · have hr0 : 0 ≤ (r : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg r) hΔ.le
        have h2 : mres + Δ ≤ 2 := by nlinarith
        have h3 : mres + Δ + (r : ℝ) * Δ ≤ μ₀ := by linarith
        simp only [derivCost, h2, h3, h1, ↓reduceIte]
        exact mul_le_mul' hσ le_rfl
      · simp only [h1, ↓reduceIte]
        exact le_top
    have := ih hD'
    refine this.congr_germ fun l => Filter.Eventually.of_forall fun w => ?_
    simp only [dLabelG]
    have e2 : (fun h => f (π l).1 (((π l).2.recenter D w).recenter D h)) =
        fun h => (fun w' => f (π l).1 ((π l).2.recenter D w')) (w + h) := by
      funext h; rw [recenter_recenter D env.hζ]
    show fderiv ℝ (fun h => f (π l).1 (((π l).2.recenter D w).recenter D h)) 0 (basisVec j) =
      fderiv ℝ (fun w' => f (π l).1 ((π l).2.recenter D w')) w (basisVec j)
    rw [e2]
    set F : Vec 2 → ℝ := fun w' => f (π l).1 ((π l).2.recenter D w')
    show fderiv ℝ (fun h => F (w + h)) 0 _ = fderiv ℝ F w _
    rw [fderiv_comp_add_left, add_zero]

end AVRegularity.Providers.CascadeInvariants
end

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the bridge arrays of an appended child are a push-forward tensor at the
recentered family.** For a family `A` of the grade-zero lift setup over the finer slot `k` and a
time of the lift window, the entry `(c, γ)` of order one of the chart arrays `bridgeChild` at the
point `x` is `hSem c (γ 0)` (the push-forward `(F Ŝ₀ Fᵀ)_{cγ}` of the label tensor `sHat`) at the
family recentered at `Ψ⁻¹x` (`bridgeChild_eq_hSem`), and the other orders vanish
(`bridgeChild_ne_one`). The map `y ↦ hSem(A^{[y]})` is as smooth as the lift
(`contDiff_hSem_recenter`). -/

open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

/-- The push-forward `(F Ŝ₀ Fᵀ)_{cg}` of the label tensor at a family. -/
def hSem (D : OCData) (m : ℕ) (k : ℤ) (c g : Fin 2) : GenSort.Sem .fam :=
  fun t A => ∑ a : Fin 2, ∑ e : Fin 2, A.famJac D t c a * sHat D m k a e t A * A.famJac D t g e

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {Dm m : ℕ} {k : ℤ}
  {𝒜 : Set RealChain} {ρ : ℝ} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N : ℕ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The standing facts of the grade-zero lifts over the finer slot `k`. -/
structure ChildLift (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (Dm m : ℕ) (k : ℤ)
    (𝒜 : Set RealChain) (ρ : ℝ) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : Prop where
  hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N (Cc0 k)
  hk : Odd k
  hΛ : 1 ≤ D.Λ
  hζ : IsFastProfile D.ζ
  hκ : ∀ i, 0 < D.kap i
  hN : 1 ≤ N
  hρ : ρ ≠ 0
  hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap (m - 1) * D.cellScaleSq m
  hseq : ∀ A ∈ 𝒜, IsLiftSequence (diagQ D Dm m k A ρ) sX sZ t₀ t₁ N 0 (Cc0 k A)

namespace ChildLift

variable (L : ChildLift D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc0)
include L

/-- The label arrays of order one of the bridge are the label tensor at the recentered family. -/
theorem bridgeLab_one {A : RealChain} (hA : A ∈ 𝒜) {t : ℝ}
    (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (κ : Fin 2) (α : DerivativeWord2 1) (y : Vec 2) :
    bridgeLab D Dm m ρ Cc0 k t A κ 1 α y 0 = sHat D m k κ (α 0) t (A.recenter D y) := by
  have hW : A.WellSlotted := (L.hS.hA A hA).1
  simp only [bridgeLab, Pi.sub_apply]
  rw [pmArr_two_one L.hS L.hk L.hΛ L.hκ L.hN hA L.hρ L.hDst ht κ α y]
  simp only [matGradArr, labJ, jacMatrix_famMap L.hζ A hW t y, sHat]

/-- The label arrays of the bridge of an order other than one vanish. -/
theorem bridgeLab_ne_one {A : RealChain} (hA : A ∈ 𝒜) {t : ℝ}
    (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (κ : Fin 2) {r : ℕ} (hr : r ≠ 1)
    (α : DerivativeWord2 r) (y : Vec 2) : bridgeLab D Dm m ρ Cc0 k t A κ r α y 0 = 0 := by
  simp only [bridgeLab, Pi.sub_apply]
  match r, hr with
  | 0, _ =>
    rw [pmArr_two_zero L.hS L.hN hA ht κ α y]
    simp [matGradArr]
  | r + 2, _ =>
    have h0 := arrSupp_pmArr D m ρ (diagQ D Dm m k A ρ) (Cc0 k A) 2 t κ (r + 2) (by omega) α
    rw [show pmArr D m ρ (diagQ D Dm m k A ρ) (Cc0 k A) 2 t κ (r + 2) α y 0 = 0 from by
      rw [h0]; rfl]
    simp [matGradArr]

/-- **The bridge arrays of an appended child at the point `x`** are the push-forward tensor at
the family recentered at `Ψ⁻¹x`. -/
theorem bridgeChild_eq_hSem {A : RealChain} (hA : A ∈ 𝒜) {t : ℝ}
    (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (c : Fin 2) (γ : DerivativeWord2 1) (x : Vec 2) :
    bridgeChild D Dm m ρ Cc0 k t A c 1 γ x 0 =
      hSem D m k c (γ 0) t (A.recenter D (A.famMapInv D t x)) := by
  have hW : A.WellSlotted := (L.hS.hA A hA).1
  show chartCoef (fun x => jacMatrix (A.famMap D t) (A.famMapInv D t x)) (A.famMapInv D t)
    (A.famMap D t) 2 (bridgeLab D Dm m ρ Cc0 k t A) c 1 γ x = _
  unfold chartCoef
  set y := A.famMapInv D t x with hy
  have hone : ∀ κ, ∑ r ∈ Finset.range (2 + 1), ∑ α : DerivativeWord2 r,
      bridgeLab D Dm m ρ Cc0 k t A κ r α y 0 * fdbArr (A.famMap D t) α 1 γ y 0 =
      ∑ α : DerivativeWord2 1, sHat D m k κ (α 0) t (A.recenter D y) *
        jacMatrix (A.famMap D t) y (γ 0) (α 0) := by
    intro κ
    rw [Finset.sum_eq_single 1]
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [L.bridgeLab_one hA ht κ α y, fdbArr_one_one]
    · intro r _ hr1
      exact Finset.sum_eq_zero fun α _ => by rw [L.bridgeLab_ne_one hA ht κ hr1 α y, zero_mul]
    · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
  simp only [hone]
  unfold hSem
  rw [jacMatrix_famMap L.hζ A hW t y]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  rw [sum_word_one (fun e => (A.recenter D y).famJac D t c a * (sHat D m k a e t (A.recenter D y) *
    (A.recenter D y).famJac D t (γ 0) e))]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **The push-forward tensor along the recentering is smooth**, of the order of the lift. -/
theorem contDiff_hSem_recenter {A : RealChain} (hA : A ∈ 𝒜) {t : ℝ}
    (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) {r : ℕ} (hRX : r + Dm + 2 ≤ sX)
    (hRZ : r + Dm + 2 ≤ sZ) (c g : Fin 2) :
    ContDiff ℝ r (fun y => hSem D m k c g t (A.recenter D y)) := by
  have hW : A.WellSlotted := (L.hS.hA A hA).1
  have hreg := liftRegular_of_isLiftSequence D m k hW ρ (L.hseq A hA) hRX hRZ 0 le_rfl 2 _ ht 0
  have hJ : ∀ a e, ContDiff ℝ r (fun y => (A.recenter D y).famJac D t a e) := by
    intro a e
    have : (fun y => (A.recenter D y).famJac D t a e) = fun y => jacMatrix (A.famMap D t) y a e :=
      funext fun y => by rw [jacMatrix_famMap L.hζ A hW t y]
    rw [this]
    exact (contDiff_jacMatrix_entry (contDiff_famMap A t) a e).of_le (by exact_mod_cast le_top)
  have hJi : ∀ a e, ContDiff ℝ r (fun y => ((A.recenter D y).famJac D t)⁻¹ a e) := fun a e =>
    (contDiff_famJacInv L.hζ A hW t a e).of_le (by exact_mod_cast le_top)
  have hK : ∀ a (α : DerivativeWord2 1), ContDiff ℝ r
      (fun y => kLab D m k a (α 0) t (A.recenter D y)) := by
    intro a α
    have e : (fun y => kLab D m k a (α 0) t (A.recenter D y)) =
        fun y => pmArr D m ρ (diagQ D Dm m k A ρ) (Cc0 k A) 2 t a 1 α y 0 :=
      funext fun y => (pmArr_two_one L.hS L.hk L.hΛ L.hκ L.hN hA L.hρ L.hDst ht a α y).symm
    rw [e]
    exact contDiff_pmArr D m ρ _ _ 2 t a hreg 1 α
  have hS : ∀ a e, ContDiff ℝ r (fun y => sHat D m k a e t (A.recenter D y)) := by
    intro a e
    have hKe := hK a (fun _ => e)
    simp only [sHat]
    refine hKe.sub ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiff.sum fun c _ => (ContDiff.sum fun d _ => (hJi a d).mul contDiff_const).mul
      (hJi e c)
  unfold hSem
  exact ContDiff.sum fun a _ => ContDiff.sum fun e _ => ((hJ c a).mul (hS a e)).mul (hJ g e)

end ChildLift

end AVRegularity.Providers.CascadeInvariants
end
