-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.TailForceSlice
public import AVRegularity.CycleComparison.Reconstruction.ObsEdgesTested
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableBlocks
import AVRegularity.CycleComparison.Reconstruction.ReconChains
public import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Residual.TailJets
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tail slices of the observed pulses on a reconstruction window**. At a time `t` of the
window and of the window of an observed pulse `k`, the weighted word derivatives of the physical
tail flux and force of the pulse, for a coarse field `u` and cleanup chains of its divided tails,
are bounded by the gradient energy density of `u` (`ReconWindowAt.pulse_tail_slice`): this is
`setting_tailPhys_word_slice` and `setting_tailForce_word_slice` with the lift setting and the lift
sequence of the window, the mixed jets of the tail arrays
(`setting_tailFluxCoefficient_mixed_jets`), the jets of the renewal charts at the scale
`E = ε_{m-1}` (`pulseChart_jetBound`) and the slow invariance of the chains
(`setting_tail_cleanupChain_slowShift`). -/

section
/-- In a lift setting the fast scale is below the slow scale: `e = ℓ√ν ≤ ℓ√B = ε_c ρ ≤ ρ`. -/
theorem IsLiftSetting.e_le_ρ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ}
    {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ) :
    e ≤ ρ := by
  have hν := P.ν_pos
  have hB := P.B_pos
  have hρ := P.ρ_pos
  have hνB : ν ≤ B := by
    have h1 := P.η_le
    rw [P.η_eq, div_le_one hB] at h1
    exact h1
  have hℓ : 0 ≤ ℓ := by rw [P.ℓ_eq]; exact div_nonneg P.e_pos.le (Real.sqrt_nonneg _)
  have he : e = ℓ * Real.sqrt ν := by
    rw [P.ℓ_eq, div_mul_cancel₀ _ (Real.sqrt_pos.2 hν).ne']
  have hd : dstar ≤ ρ := by
    have h1 := P.εc_le
    rw [P.εc_eq, div_le_one hρ] at h1
    exact h1
  calc e = ℓ * Real.sqrt ν := he
    _ ≤ ℓ * Real.sqrt B := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hνB) hℓ
    _ = dstar := P.dstar_eq.symm
    _ ≤ ρ := hd

/-- The physical tail flux of a `C^r` label flux, read through a smooth chart with smooth
inverse, is `C^r`. -/
theorem contDiff_tailFluxPhys_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) {r : ℕ}
    (hG : ∀ i₀, ContDiff ℝ (r : ℕ∞) (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀))
    (a₀ : Fin 2) : ContDiff ℝ (r : ℕ∞) (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀) := by
  show ContDiff ℝ (r : ℕ∞) (fun x => ∑ i₀ : Fin 2,
    chartInvJacobian ψ x a₀ i₀ • tailFluxLabel H N Acl ε c ρs es Vc t (ψ x) i₀)
  exact ContDiff.sum fun i₀ _ =>
    ((contDiff_chartInvJacobian_apply hχ hψ hψχ hχψ a₀ i₀).of_le
      (by exact_mod_cast le_top)).smul ((hG i₀).comp (hψ.of_le (by exact_mod_cast le_top)))

/-- The slow bound of the mixed jets of the tail arrays on a reconstruction window. -/
def reconTailS (Klift Llift D H Nc : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ) : ℝ :=
  tailMixedBound Klift Llift Llift D H Nc CGl Cw (fun _ _ => Ca) * (1 + |Sb|) ^ H

theorem reconTailS_nonneg (Klift Llift D H Nc : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ) :
    0 ≤ reconTailS Klift Llift D H Nc CGl Cw Ca Sb :=
  mul_nonneg (tailMixedBound_nonneg _ _ _ _ _ _ _ _ _) (by positivity)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The mixed jets of the tail arrays of an observed pulse** at a cell time of its window. -/
theorem ReconWindowAt.pulse_tail_jets
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r : ℕ} (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift) {k : ℤ}
    (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)) :
    ∀ hh, hh ≤ H → ∀ n ∈ Finset.Icc (Nc + 1) (2 * Nc + D), ∀ bb, bb ≤ r →
      ∀ δ : DerivativeWord2 bb, ∀ i, i ≤ Acl + 2 + r → ∀ m'',
        MixedTail.schurMixedJet π {τ} i δ
          (fun q' : DerivativeWord2 m'' × Fin 2 => tailFluxCoefficient (par k)
            (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B ρ
              (ρ / ocEpsilon q Λ (m - 1)) k
              (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n q'.2 m'' q'.1) ≤
          ENNReal.ofReal (reconTailS Klift Llift D H Nc CGl Cw Ca Sb) := by
  have P := w.hsetting k hk
  have hSle : ∀ hh, hh ≤ H → tailMixedBound Klift Llift Llift D H Nc CGl Cw (fun _ _ => Ca) *
      Sb ^ hh ≤ reconTailS Klift Llift D H Nc CGl Cw Ca Sb := fun hh hhh => by
    unfold reconTailS
    refine mul_le_mul_of_nonneg_left ?_ (tailMixedBound_nonneg _ _ _ _ _ _ _ _ _)
    have h1 : 1 ≤ 1 + |Sb| := by linarith [abs_nonneg Sb]
    calc Sb ^ hh ≤ |Sb ^ hh| := le_abs_self _
      _ = |Sb| ^ hh := abs_pow Sb hh
      _ ≤ (1 + |Sb|) ^ hh := pow_le_pow_left₀ (abs_nonneg _) (by linarith) hh
      _ ≤ (1 + |Sb|) ^ H := pow_le_pow_right₀ h1 hhh
  exact fun hh hhh n hn bb hbb δ i hi m'' =>
    (setting_tailFluxCoefficient_mixed_jets P (Cc k) (w.hseq k hk) hh hhh Acl r hK
      (by unfold TailPresentation.arrayFastOrder; omega) hτ n hn bb hbb δ i hi m'').trans
      (ENNReal.ofReal_le_ofReal (hSle hh hhh))

/-- **The tail slices of one observed pulse at one time of the window.** -/
theorem ReconWindowAt.pulse_tail_slice
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift)
    (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1) (hNχ : m' + 1 ≤ Nχ)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t)) (hup : IsZ2Periodic (u t))
    (hV : ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
        (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ocEll q Λ m ν ^ 2)⁻¹ * t)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => tailFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x' a₀) x) ≤
      ENNReal.ofReal (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ)) *
        ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        ResidualTimeData.gradDensity π ρ m' u t ∧
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => tailForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x') x) ≤
      ENNReal.ofReal (tailForceConst H Nc D Acl r m' (pulseChartD Nχ)) *
        ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        ResidualTimeData.gradDensity π ρ m' u t := by
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ := P.ρ_pos
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  have hrm : r ≤ m' := by omega
  -- the charts
  obtain ⟨hJχ, hJψ⟩ := pulseChart_jetBound α s w.hα₀ w.hα₁ w.hs₀ w.hs₁ q w.hq ζ w.hζ Λ w.hΛ
    Φ w.hΦ m w.hm hφ k hwin Nχ
  have hJ : ∀ {Θ' : Vec 2 → Vec 2} {N₁ : ℕ}, N₁ ≤ Nχ →
      JetBound Θ' Nχ (pulseChartD Nχ) (ocEpsilon q Λ (m - 1)) →
      JetBound Θ' N₁ (pulseChartD Nχ) (ocEpsilon q Λ (m - 1)) :=
    fun hN hJ' p hp1 hpN y => hJ' p hp1 (hpN.trans hN) y
  have hχ := contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hψ := contDiff_ocChartInv hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hC := isChart_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  -- the scales
  have heρ : ocEpsilon q Λ m ≤ ρ := IsLiftSetting.e_le_ρ P
  have hρE := w.hRE
  have hsR : rs ≤ ocEpsilon q Λ (m - 1) := hrse.trans (heρ.trans hρE)
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  -- the mixed jets of the tail arrays
  have hjet := w.pulse_tail_jets hK hrL hk hcell
  -- the chains are invariant under the slow translations
  have hslow : ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t)
          (X + ρ⁻¹ • latticeShift n) =
        Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X := by
    intro hh hhh j' hj' n X
    refine setting_tail_cleanupChain_slowShift P (Klift + D + 2) (max (Llift + 1) (Llift + 2))
      (by omega) (by omega) (Cc k) hseq (ρ⁻¹ • latticeShift n)
      (pulse_G_slow_invariant α q Λ m ζ hφ ν B hρ.ne' _ k _ n)
      (pulse_edge_slow_invariant α q Λ m ζ hφ ν B hρ.ne' k w.htorus (pp k) n)
      hh hhh (by omega : 1 ≤ r + 1) _ _ _ hcell ?_ (hV hh hhh) j' hj' X
    intro X'
    have hct : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
    simp only [hct, smul_add, smul_inv_smul₀ hρ.ne',
      Charts.ocChart_latticeShift hφ α q Λ m (ocPulseChartIndex α q Λ m k) t n]
    exact hup n _
  refine ⟨setting_tailPhys_word_slice P (Klift + D + 2) (max (Llift + 1) (Llift + 2)) (by omega)
    (by omega) (Cc k) hseq Acl r m' hAcl (by omega) (by omega) hord _
    (reconTailS_nonneg Klift Llift D H Nc CGl Cw Ca Sb) u
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) hcell hu hup hC
    (hχ.of_le (by exact_mod_cast le_top)) (hχ.of_le (by exact_mod_cast le_top))
    (hψ.of_le (by exact_mod_cast le_top)) (one_le_pulseChartD Nχ) (hJ (by omega) hJχ)
    (hJ hNχ hJχ) (hJ (by omega) hJψ) hρE hjet Vc hV hslow hrs hrse hsR heρ hM hj β, ?_⟩
  exact setting_tailForce_word_slice P (Klift + D + 2) (max (Llift + 1) (Llift + 2)) (by omega)
    (by omega) (Cc k) hseq Acl r m' hAcl (by omega) (by omega) hord _
    (reconTailS_nonneg Klift Llift D H Nc CGl Cw Ca Sb) u
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) hcell hu hup hC
    (hχ.of_le (by exact_mod_cast le_top)) (hψ.of_le (by exact_mod_cast le_top))
    (one_le_pulseChartD Nχ) (hJ hNχ hJχ) (hJ (by omega) hJψ) hρE hjet Vc hV hslow hrs hrse hsR
    heρ hM hj β

/-- **The tail flux and force of one observed pulse are of class `C^r`** at a time of the window
and of the window of the pulse. -/
theorem ReconWindowAt.pulse_tail_contDiff
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift)
    (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t))
    (hV : ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
        (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ocEll q Λ m ν ^ 2)⁻¹ * t))) :
    (∀ a₀ : Fin 2, ContDiff ℝ (r : ℕ∞) (fun x => tailFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x a₀)) ∧
    ContDiff ℝ (r : ℕ∞) (fun x => tailForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x) := by
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  have hχ := contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hψ := contDiff_ocChartInv hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hTT := fun (hh : ℕ) (hhh : hh ≤ H) => setting_tailTime P (Klift + D + 2)
    (max (Llift + 1) (Llift + 2)) (by omega) (by omega) (Cc k) hseq Acl r m' hAcl (by omega)
    (by omega) hord hh hhh _ u (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    hcell (hu.comp (hχ.of_le (by exact_mod_cast le_top)))
    (w.pulse_tail_jets hK hrL hk hcell hh hhh) (fun j => Vc hh j ((ocEll q Λ m ν ^ 2)⁻¹ * t))
    (hV hh hhh)
  have hbox : ∀ hh, hh ≤ H → ∀ j', j' < Acl → IsBoxSmooth (Acl + 2 + r) (r + 1)
      (Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t)) := fun hh hhh j' hj' =>
    IsCleanupChain.isBoxSmooth (hTT hh hhh).flux_box (hTT hh hhh).chain j' hj'
  have hG : ∀ l, ContDiff ℝ (r : ℕ∞) (fun y => tailFluxLabel H Nc Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
      ρ (ocEpsilon q Λ m) Vc t y l) := fun l =>
    ContDiff.sum fun hh hhm => ((contDiff_cleanupFlux_sample_of_le (sX := Acl + 2 + r)
      (sZ := r + 1) (by omega) (by omega) (ocEll q Λ m ν ^ 2)⁻¹
      ρ (ocEpsilon q Λ m) t
      (hbox hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) l).const_smul _).const_smul _
  refine ⟨fun a₀ => contDiff_tailFluxPhys_of_le hχ hψ
    (Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ t)
    (Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ t) H Nc Acl _ _ _ _ Vc t hG a₀, ?_⟩
  show ContDiff ℝ (r : ℕ∞) (fun x => ∑ hh ∈ Finset.range (H + 1),
    (ocEll q Λ m ν ^ 2)⁻¹ • (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) •
      cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
        (ocEpsilon q Λ m) Acl (Vc hh) t
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x))
  refine ContDiff.sum fun hh hhm => ?_
  have hd := hTT hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))
  have hq : ContDiff ℝ (r : ℕ∞) (fun y => cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹
      ρ (ocEpsilon q Λ m) Acl (Vc hh) t y) :=
    (hd.contDiff_source_sample le_rfl (ocEpsilon q Λ m)).const_smul _
  exact ((hq.comp (hψ.of_le (by exact_mod_cast le_top))).const_smul _).const_smul _
end

/-! **The glued tail slices on a reconstruction window** (the partition weights are nonnegative
with sum one, so the glue costs nothing). At a time
of the window, the weighted word derivatives of the glued tail flux and force (`gluedTailFlux`,
`gluedTailForce`) of a coarse field `u` with cleanup chains on every observed pulse are bounded as
those of one pulse (`ReconWindowAt.glued_tail_slice`): the glued sum is a convex combination of the
weighted pulses (`fluxInt_word_convex_le`, `scalInt_word_convex_le`), each bounded by
`ReconWindowAt.pulse_tail_slice`. -/

section
/-- A weighted sum is the sum over the indices of nonzero weight. -/
theorem sum_smul_eq_sum_filter_weight {E : Type*} [AddCommGroup E] [Module ℝ E] {κ : Type*}
    (S : Finset κ) (w : κ → ℝ) (y : κ → E) [DecidablePred fun k => w k ≠ 0] :
    ∑ k ∈ S, w k • y k = ∑ k ∈ S with w k ≠ 0, w k • y k :=
  (Finset.sum_filter_of_ne (p := fun k => w k ≠ 0) (f := fun k => w k • y k)
    fun k _ hne hw => hne (by rw [show w k = 0 from hw, zero_smul])).symm

/-- The weights of the weighted pulses sum to one. -/
theorem sum_filter_weight_eq_one {κ : Type*} (S : Finset κ) (w : κ → ℝ)
    [DecidablePred fun k => w k ≠ 0] (h1 : ∑ k ∈ S, w k = 1) :
    ∑ k ∈ S with w k ≠ 0, w k = 1 := by
  rw [Finset.sum_filter_ne_zero, h1]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The glued tail slices at one time of the window.** -/
theorem ReconWindowAt.glued_tail_slice
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift)
    (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1) (hNχ : m' + 1 ≤ Nχ)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (r + 1) Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => Vc k hh j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t)) (hup : IsZ2Periodic (u t))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' =>
        gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x' a₀) x) ≤
      ENNReal.ofReal (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ)) *
        ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        ResidualTimeData.gradDensity π ρ m' u t ∧
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' =>
        gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x') x) ≤
      ENNReal.ofReal (tailForceConst H Nc D Acl r m' (pulseChartD Nχ)) *
        ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        ResidualTimeData.gradDensity π ρ m' u t := by
  classical
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  set S' := (ocObsPulses α q Λ m tp (tp + Tobs)).filter (fun k => F.weight (pp k) t ≠ 0)
    with hS'
  have hmem : ∀ k ∈ S', k ∈ ocObsPulses α q Λ m tp (tp + Tobs) ∧ F.weight (pp k) t ≠ 0 :=
    fun k hk => Finset.mem_filter.1 hk
  have hw0 : ∀ k ∈ S', 0 ≤ F.weight (pp k) t := fun k hk => w.hpart.1 k (hmem k hk).1 t
  have hw1 : ∑ k ∈ S', F.weight (pp k) t = 1 :=
    sum_filter_weight_eq_one _ (fun k => F.weight (pp k) t) (w.hpart.2.2.1 t ht)
  -- the facts of the weighted pulses
  have hwin : ∀ k ∈ S', t ∈ ocPulseWindow α q Λ m k := fun k hk =>
    w.hpart.2.2.2.1 k (hmem k hk).1 t (hmem k hk).2
  have hVk : ∀ k ∈ S', ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
        (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (fun j => Vc k hh j ((ocEll q Λ m ν ^ 2)⁻¹ * t)) := fun k hk hh hhh =>
    hV k (hmem k hk).1 hh hhh _
      (AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk) ht)
  have hsl := fun k (hk : k ∈ S') => w.pulse_tail_slice hAcl hK hrL hord hNχ u (Vc k)
    (hmem k hk).1 ht (hwin k hk) hu hup (hVk k hk) hrs hrse hj β
  have hcd := fun k (hk : k ∈ S') => w.pulse_tail_contDiff hAcl hK hrL hord u (Vc k)
    (hmem k hk).1 ht (hwin k hk) hu (hVk k hk)
  -- the glued sums are the sums over the weighted pulses
  have hF : ∀ a₀ : Fin 2, (fun x' =>
      gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x' a₀) = fun x' =>
      ∑ k ∈ S', F.weight (pp k) t • tailFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vc k) t x' a₀ := fun a₀ =>
    funext fun x' => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
  have hf : (fun x' =>
      gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x') = fun x' =>
      ∑ k ∈ S', F.weight (pp k) t • tailForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vc k) t x' :=
    funext fun x' => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
  refine ⟨?_, ?_⟩
  · simp only [hF]
    exact fluxInt_word_convex_le S' (fun k => F.weight (pp k) t) hw0 hw1
      (fun k y l => tailFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vc k) t y l)
      (fun k hk l => ((hcd k hk).1 l).of_le (by exact_mod_cast hj)) rs β π
      (fun k hk _ => (hsl k hk).1)
  · simp only [hf]
    exact scalInt_word_convex_le S' (fun k => F.weight (pp k) t) hw0 hw1
      (fun k y => tailForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vc k) t y)
      (fun k hk => (hcd k hk).2.of_le (by exact_mod_cast hj)) rs β π
      (fun k hk _ => (hsl k hk).2)
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time measurability of the slice norms of the label fields** (the measurability
premise of `partition_term_bound`).

On the clipped lift window `S_k = [max((k - 61/48)τ, t_p), min((k + 61/48)τ, t_p + T_obs)]` of an
observed pulse, the weighted slice norms `t ↦ ∑_v π_v⁻¹ ∫_cell |r_s^j ∂^w labelSrc_hh(a ∘ χ_k)(t)|²`
of the label fields of the Galerkin approximants `a = a_n` are a.e. measurable
(`ReconWindowAt.labelSrc_slice_aemeasurable`).

The time is clamped so that the cell time `ℓ⁻²t` stays in the lift window `[t₀, t₁]` of the
setting: `θ(t) = ℓ² projIcc_{[t₀, t₁]}(ℓ⁻²t)`, with `θ = id` on `S_k`. At the clamped time the
label field is a finite sum of lift actions of the chart-frame field, measurable in time
(`setting_liftApply_joint_measurable`, `chartFrame_clamped_measurable`), and it is `C^J` in space
(`labelSrc_contDiff`); its word derivatives are then jointly measurable (Carathéodory,
`measurable_orderedDerivative_joint`), hence so is its slice norm
(`AVRegularity.ChartTransport.measurable_scalInt`). The abstract statement for a lift setting is
`setting_labelSrc_slice_aemeasurable`. -/

/-- **Carathéodory for word derivatives.** The word derivatives through order `J` of a family of
`C^J` fields that is measurable in the parameter at every point are jointly measurable. -/
theorem measurable_orderedDerivative_joint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : ℝ → Vec 2 → E) (J : ℕ) (hm : ∀ x, Measurable fun t => f t x)
    (hf : ∀ t, ContDiff ℝ (J : ℕ∞) (f t)) {i : ℕ} (hiJ : i ≤ J) (β : DerivativeWord2 i) :
    Measurable fun p : ℝ × Vec 2 => orderedDerivative β (f p.1) p.2 :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec 2) (t : ℝ) => orderedDerivative β (f t) x)
    (fun t => AVRegularity.ChartTransport.continuous_orderedDerivative β
      ((hf t).of_le (natCast_le_natCast_order hiJ)))
    (fun x => Lift.orderedDerivative_parameter_measurable f J hm hf i hiJ β x)).comp
    measurable_swap

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The slice norms of the label fields of a lift setting are a.e. measurable on the clipped
window.** For a lift setting on the cell-time window `[M₁/ℓ², M₂/ℓ²]` with a lift sequence of
orders `(sX, sZ)`, and a coarse field `A` smooth in space whose chart-frame values
`A(ℓ²τ, ρX)` are measurable in the clamped cell time `τ`, the weighted slice norm of every word
derivative of order `i ≤ J ≤ min(sX, sZ)` of the label field `labelSrc_hh(A)` is a.e. measurable
on `[M₁, M₂]`. -/
theorem setting_labelSrc_slice_aemeasurable {D H N K kl L qs qf : ℕ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ}
    {Θ : ℝ} {ℓ M₁ M₂ : ℝ}
    (P : IsLiftSetting Q π (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam par V H N
      K kl L qs qf CG Cw Cj bm Θ)
    {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) N H Cc) (hsZ : 1 ≤ sZ)
    {hh : ℕ} (hhh : hh ≤ H) {J : ℕ} (hJX : J ≤ sX) (hJZ : J ≤ sZ) (hℓ : ℓ ≠ 0)
    (ρ e εc : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) (hA : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hAm : ∀ X, Measurable fun τ =>
      A (ℓ ^ 2 * Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window τ) (ρ • X))
    (π' : ι → ℝ) (rs : ℝ) {i : ℕ} (hiJ : i ≤ J) (β : DerivativeWord2 i) :
    AEMeasurable (fun t => scalInt π' (fun y => rs ^ i • orderedDerivative β
      (labelSrc N hh ℓ ρ e εc Cc A t) y)) (volume.restrict (Set.Icc M₁ M₂)) := by
  have hc : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hc0 : 0 < ℓ ^ 2 := lt_of_le_of_ne (sq_nonneg ℓ) hc.symm
  -- the clamped physical time
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ → ℝ,
      θ = fun t => ℓ ^ 2 * (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t) : ℝ) :=
    ⟨_, rfl⟩
  have hθc : ∀ t, (ℓ ^ 2)⁻¹ * θ t =
      Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t) := fun t => by
    subst hθ
    exact inv_mul_cancel_left₀ hc _
  have hθS : ∀ t ∈ Set.Icc M₁ M₂, θ t = t := fun t ht => by
    have hmem : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) := by
      have e' : (ℓ ^ 2)⁻¹ * t = t / ℓ ^ 2 := by rw [div_eq_inv_mul]
      rw [e']
      exact ⟨div_le_div_of_nonneg_right ht.1 hc0.le, div_le_div_of_nonneg_right ht.2 hc0.le⟩
    have h1 := hθc t
    rw [projIcc_val_of_mem P.window hmem] at h1
    exact mul_left_cancel₀ (inv_ne_zero hc) h1
  -- the lift actions of the chart-frame field are measurable in clamped cell time
  have hg : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun X' => A (ℓ ^ 2 * τ) (ρ • X')) := fun τ =>
    (hA _).comp (contDiff_const_smul ρ)
  have hL : ∀ n' (X z : Vec 2), Measurable fun τ : ℝ => liftApply n' (Cc hh n')
      (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
      (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window τ) X z := by
    intro n' X z
    have hq : Measurable fun τ : ℝ => (τ, X, z) := measurable_id.prodMk measurable_const
    refine Measurable.of_eval fun v => ?_
    have hJ : Measurable fun q : ℝ × Vec 2 × Vec 2 => liftApply n' (Cc hh n')
        (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
        (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window q.1) q.2.1 q.2.2 v :=
      setting_liftApply_joint_measurable P sX sZ hsZ Cc hseq hh hhh n'
        (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
        (fun τ _ => (hg τ).of_le (order_natCast_le_top n')) hAm v
    have h1 := hJ.comp hq
    simp only [Function.comp_def] at h1
    exact h1
  -- the label field at the clamped time: measurable in time, `C^J` in space
  have hm : ∀ y, Measurable fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t) y := by
    intro y
    have he : (fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t) y) = fun t =>
        ∑ n' ∈ Finset.Icc 1 N, εc ^ n' • liftApply n' (Cc hh n')
          (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
          (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t)) (ρ⁻¹ • y)
          (e⁻¹ • y) := by
      funext t
      simp only [labelSrc, diagSample, hθc t]
    rw [he]
    exact Finset.measurable_sum _ fun n' _ =>
      ((hL n' (ρ⁻¹ • y) (e⁻¹ • y)).comp (measurable_const_mul (ℓ ^ 2)⁻¹)).fun_const_smul _
  have hf : ∀ t, ContDiff ℝ (J : ℕ∞) (labelSrc N hh ℓ ρ e εc Cc A (θ t)) := fun t =>
    labelSrc_contDiff hseq hhh hJX hJZ ℓ ρ e εc A hA (by
      rw [hθc t]
      exact (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window _).2)
  -- the slice norm at the clamped time is measurable
  have hM : Measurable fun t => scalInt π' (fun y => rs ^ i • orderedDerivative β
      (labelSrc N hh ℓ ρ e εc Cc A (θ t)) y) :=
    AVRegularity.ChartTransport.measurable_scalInt (r := J)
      (q := fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t)) π' rs
      (fun j' hj' β' v => ((measurable_pi_apply v).comp
        (measurable_orderedDerivative_joint (fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t)) J hm
          hf hj' β')).enorm) hiJ β
  -- the clamp is invisible on the window
  refine hM.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  simp only [hθS t ht]

end Setting

section Window

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The slice norms of the label fields of an approximant are a.e. measurable on the clipped
lift window of each observed pulse** (the measurability premise of `partition_term_bound` for
`a = a_n`), for every grade `hh ≤ H` and every word of order `j ≤ min(K_lift + D + 2, L_lift + 2)`,
when the Galerkin coefficients of `a_n` are measurable in the clamped time. -/
theorem ReconWindowAt.labelSrc_slice_aemeasurable
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (n : ℕ)
    (hcm : ∀ r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {hh : ℕ} (hhh : hh ≤ H) {j : ℕ}
    (hjK : j ≤ Klift + D + 2) (hjL : j ≤ Llift + 2) (w' : DerivativeWord2 j) (rs : ℝ) :
    AEMeasurable (fun t => scalInt π (fun y => rs ^ j • orderedDerivative w'
      (labelSrc Nc hh (ocEll q Λ m ν) ρ (ocEpsilon q Λ m)
        (ocDStar q Λ m ν B / ρ) (Cc k)
        (fun t' y' => coarseTraj n W t'
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t' y')) t) y))
      (volume.restrict (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs)))) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hℓ).symm
  have hcm' : ∀ r', Measurable fun s : Set.Icc tp (tp + Tobs) => coarseCoeff n W r' s :=
    fun r' => by
      have h1 := (hcm r').comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tp (tp + Tobs)))
      simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hA : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (fun y' => coarseTraj n W t
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t y')) := fun t =>
    (coarseTraj_contDiff n W t).comp
      (contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t)
  exact setting_labelSrc_slice_aemeasurable (w.hsetting k hk) (w.hseq k hk)
    (le_max_of_le_left (Nat.le_add_left 1 Llift)) hhh hjK (le_max_of_le_right hjL) hℓ
    ρ (ocEpsilon q Λ m)
    (ocDStar q Λ m ν B / ρ)
    (fun t' y' => coarseTraj n W t'
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t' y')) hA
    (fun X => chartFrame_clamped_measurable (ρ := ρ)
      (f := coarseTraj n W)
      (χ := ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (w.hsetting k hk).window (fun τ hτ => physTime_mem_obs hc0 hτ)
      (jointlyMeas_coarseTraj n W hcm')
      (Charts.contDiff_ocChart_joint hφ α q Λ m (ocPulseChartIndex α q Λ m k)).continuous X)
    π rs le_rfl w'

end Window

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lifted coarse flux slices on a reconstruction window**. At a time of the window and of the
window of an observed pulse `k`, the weighted word derivatives of the physical cleanup flux and
force of the lift of the divergence of a periodic flux field `F` are bounded by the jet density of
`F` (`ReconWindowAt.pulse_lift_slice`; `setting_liftFluxPhys_word_slice`,
`setting_liftForcePhys_word_slice` with the lift setting of the window, the jets of the renewal
charts and the slow invariance of the chains), they are of class `C^r`
(`ReconWindowAt.pulse_lift_contDiff`), and so are their glued sums
(`ReconWindowAt.glued_lift_slice`). The divergence of the flux approximant is the sum of the
partial derivatives of its components (`fluxApproxDiv_eq_sum_fderiv`). -/

/-- The sampled cleanup remainder of a chain of box-smooth members is of class `C^r`. -/
theorem contDiff_cleanupRemainder_sample_of_box {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {sX sZ A r : ℕ} (hA : 1 ≤ A) (hX : r + 1 ≤ sX) (hZ : r ≤ sZ) (c ρ e : ℝ)
    {W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E} (t : ℝ)
    (hW : ∀ j, j < A → IsBoxSmooth sX sZ (W j (c * t))) :
    ContDiff ℝ (r : ℕ∞) (fun y => cleanupRemainder c ρ e A W t y) := by
  have hbox : IsBoxSmooth (r + 1) r (W (A - 1) (c * t)) := (hW (A - 1) (by omega)).mono hX hZ
  show ContDiff ℝ (r : ℕ∞) (fun y => (e / ρ) ^ A •
    cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y) (e⁻¹ • y))
  exact (CoarseFluxDiff.contDiff_sample (CoarseFluxDiff.isBoxSmooth_cleanupSource
    (V := fun j => W j (c * t)) (j := A) hbox) le_rfl le_rfl ρ e).const_smul _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The divergence of the flux approximant** is the sum of the partial derivatives of its
components. -/
theorem fluxApproxDiv_eq_sum_fderiv (n : ℕ) {k : ℕ}
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (t : ℝ) (x : Vec 2) :
    fluxApproxDiv n Fc t x = ∑ k' : Fin 2,
      fderiv ℝ (fun y => fluxApprox n (fun v => Fc v t) y k') x (basisVec k') := by
  funext v
  simp only [fluxApproxDiv, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k' _ => ?_
  exact (tail_fderiv_pi_coord ((fluxApprox_contDiff n (fun v => Fc v t) k').differentiable
    (by simp) x) (basisVec k') v).symm

variable {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- The constant of the lifted coarse flux slices: `θ = 2^{A+2+r} C_g (1 + Θ)^H`. -/
def reconLiftTheta (Acl r H : ℕ) (Cg Sb : ℝ) : ℝ := 2 ^ (Acl + 2 + r) * Cg * (1 + Sb) ^ H

/-- **The lifted coarse flux slices of one observed pulse at one time of the window.** -/
theorem ReconWindowAt.pulse_lift_slice
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ s' k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => G s' x k'))
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} (hk' : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hGp : ∀ k', IsZ2Periodic (fun x => G t x k'))
    (hV : ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      IsCleanupChain (Acl + 2 + r) (max (Llift + 1) (Llift + 2)) Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (fun _ _ _ => 0) (fun j => Vn hh n' j ((ocEll q Λ m ν ^ 2)⁻¹ * t)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => liftFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x' a₀) x) ≤
      ENNReal.ofReal (liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
        ENNReal.ofReal ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
        CoarseFluxDiff.fluxDensity ρ kres π G t ∧
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => liftForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x') x) ≤
      ENNReal.ofReal (liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
        ENNReal.ofReal ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
        CoarseFluxDiff.fluxDensity ρ kres π G t := by
  have P := w.hsetting k hk'
  have hseq := w.hseq k hk'
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ := P.ρ_pos
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  -- the charts
  obtain ⟨hJχ, hJψ⟩ := pulseChart_jetBound α s w.hα₀ w.hα₁ w.hs₀ w.hs₁ q w.hq ζ w.hζ Λ w.hΛ
    Φ w.hΦ m w.hm hφ k hwin Nχ
  have hJ : ∀ {Θ' : Vec 2 → Vec 2} {N₁ : ℕ}, N₁ ≤ Nχ →
      JetBound Θ' Nχ (pulseChartD Nχ) (ocEpsilon q Λ (m - 1)) →
      JetBound Θ' N₁ (pulseChartD Nχ) (ocEpsilon q Λ (m - 1)) :=
    fun hN hJ' p hp1 hpN y => hJ' p hp1 (hpN.trans hN) y
  have hχ : ∀ s', ContDiff ℝ (⊤ : ℕ∞)
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s') := fun s' =>
    contDiff_ocChart hφ α q Λ m _ s'
  have hψ : ∀ s', ContDiff ℝ (⊤ : ℕ∞)
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s') := fun s' =>
    contDiff_ocChartInv hφ α q Λ m _ s'
  have hC := isChart_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  -- the scales
  have heρ : ocEpsilon q Λ m ≤ ρ := IsLiftSetting.e_le_ρ P
  have hρE := w.hRE
  have hsR : rs ≤ ocEpsilon q Λ (m - 1) := hrse.trans (heρ.trans hρE)
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  -- the lift grading and the constants
  have hst : ∀ hh, hh ≤ H → ∀ c0 : ∀ i, h i, ∀ t' ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      ∀ X z, ∀ n, 1 ≤ n → n ≤ Nc → liftApply n (Cc k hh n) (fun _ _ => c0) t' X z = 0 :=
    fun hh hhh c0 t' ht' X z n hn _ => congrFun (congrFun
      (liftSequence_constants_zero P _ _ (Cc k) hseq c0 hh hhh n hn t' ht') X) z
  have hθ : ∀ hh, hh ≤ H → 2 ^ (Acl + 2 + r) * Cg * Sb ^ hh ≤ reconLiftTheta Acl r H Cg Sb :=
    fun hh hhh => by
      unfold reconLiftTheta
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hCg)
      calc Sb ^ hh ≤ (1 + Sb) ^ hh := pow_le_pow_left₀ hSb (by linarith) hh
        _ ≤ (1 + Sb) ^ H := pow_le_pow_right₀ (by linarith) hhh
  have hθ0 : 0 ≤ reconLiftTheta Acl r H Cg Sb := by unfold reconLiftTheta; positivity
  -- the chains are invariant under the slow translations
  have hslow : ∀ hh, hh ≤ H → ∀ n', n' < Nc → ∀ j', j' < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vn hh n' j' ((ocEll q Λ m ν ^ 2)⁻¹ * t)
          (X + ρ⁻¹ • latticeShift n) =
        Vn hh n' j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X := by
    intro hh hhh n' hn' j' hj' n X
    refine isCleanupChain_slow_invariant (by omega : 1 ≤ max (Llift + 1) (Llift + 2))
      (ρ⁻¹ • latticeShift n) (fun X' => ?_) (fun _ => rfl)
      (hV hh hhh n' hn') j' hj' X
    funext z
    refine liftApply_slow_invariant (n' + 1) (Cc k hh (n' + 1)) _ ((ocEll q Λ m ν ^ 2)⁻¹ * t)
      (ρ⁻¹ • latticeShift n)
      (fun m' α' X'' z' v' u' =>
        LiftMeanEntrywise.setting_liftSequence_slowShift_invariant P _ _ (Cc k) hseq
          (ρ⁻¹ • latticeShift n)
          (pulse_G_slow_invariant α q Λ m ζ hφ ν B hρ.ne' _ k _ n)
          (pulse_edge_slow_invariant α q Λ m ζ hφ ν B hρ.ne' k w.htorus (pp k) n) hh hhh
          (n' + 1) m' α' _ hcell X'' z' v' u') (fun X₁ => ?_) X' z
    have hct : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
    simp only [hct, smul_add, smul_inv_smul₀ hρ.ne',
      Charts.ocChart_latticeShift hφ α q Λ m (ocPulseChartIndex α q Λ m k) t n]
    refine Finset.sum_congr rfl fun k' _ => ?_
    have hd : (fun y => G t (y + latticeShift n) k') = fun y => G t y k' :=
      funext fun y => hGp k' n y
    have h2 : fderiv ℝ (fun y => G t (y + latticeShift n) k')
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t
          (ρ • X₁)) =
      fderiv ℝ (fun y => G t y k') (ocChart α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) t (ρ • X₁) +
          latticeShift n) :=
      fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => G t y k') (latticeShift n)
    rw [hd] at h2
    rw [← h2]
  refine ⟨setting_liftFluxPhys_word_slice P (Cc k) hseq Acl r kres hAcl (by omega) hrL
    (by omega) hk Cg hCg hSb (hgr k hk') hst _ hθ0 hθ G
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) hχ
    (fun s' => (hψ s').differentiable (by simp))
    (fun s' => Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ s')
    (fun s' => Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ s')
    (fun s' => Charts.ocChart_det hφ α q Λ m _ s') hG Vn hcell hGp hV hslow hC
    (one_le_pulseChartD Nχ) hNχ (hJ (by omega) hJχ) hJχ (hJ (by omega) hJψ)
    ((hψ t).of_le (by exact_mod_cast le_top)) hρE hrs hrse hsR heρ hM hj β, ?_⟩
  exact setting_liftForcePhys_word_slice P (Cc k) hseq Acl r kres hAcl (by omega) hrL
    (by omega) hk Cg hCg hSb (hgr k hk') hst _ hθ0 hθ G
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) hχ
    (fun s' => (hψ s').differentiable (by simp))
    (fun s' => Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ s')
    (fun s' => Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ s')
    (fun s' => Charts.ocChart_det hφ α q Λ m _ s') hG Vn hcell hGp hV hslow hC
    (one_le_pulseChartD Nχ) hNχ hJχ (hJ (by omega) hJψ)
    ((hψ t).of_le (by exact_mod_cast le_top)) hρE hrs hrse hsR heρ hM hj β

/-- **The lifted coarse flux and force of one observed pulse are of class `C^r`** at a time of
the window and of the window of the pulse. -/
theorem ReconWindowAt.pulse_lift_contDiff
    (_w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r : ℕ} (hAcl : 1 ≤ Acl) (hrL : r ≤ Llift)
    (A : ℝ → Vec 2 → ∀ i, h i) (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} {t : ℝ}
    (hV : ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      IsCleanupChain (Acl + 2 + r) (max (Llift + 1) (Llift + 2)) Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) A ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (fun _ _ _ => 0) (fun j => Vn hh n' j ((ocEll q Λ m ν ^ 2)⁻¹ * t))) :
    (∀ a₀ : Fin 2, ContDiff ℝ (r : ℕ∞) (fun x => liftFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x a₀)) ∧
    ContDiff ℝ (r : ℕ∞) (fun x => liftForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x) := by
  have hχ := contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hψ := contDiff_ocChartInv hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  have hbox : ∀ n, n < Nc → ∀ hh, hh ≤ H → ∀ j, j < Acl →
      IsBoxSmooth (Acl + 2 + r) (max (Llift + 1) (Llift + 2))
        (Vn hh n j ((ocEll q Λ m ν ^ 2)⁻¹ * t)) := fun n hn hh hhh =>
    cleanupChain_zeroFlux_box (hV hh hhh n hn)
  have hG : ∀ n, n < Nc → ∀ l, ContDiff ℝ (r : ℕ∞) (fun y => tailFluxLabel H n Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
      ρ (ocEpsilon q Λ m) (fun hh => Vn hh n) t y l) :=
    fun n hn l => ContDiff.sum fun hh hhm => ((contDiff_cleanupFlux_sample_of_le
      (sX := Acl + 2 + r) (sZ := max (Llift + 1) (Llift + 2)) (by omega) (by omega)
      (ocEll q Λ m ν ^ 2)⁻¹ ρ (ocEpsilon q Λ m) t
      (hbox n hn hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) l).const_smul _).const_smul _
  refine ⟨fun a₀ => ContDiff.sum fun n hn => (contDiff_tailFluxPhys_of_le hχ hψ
    (Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ t)
    (Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ t) H n Acl _ _ _ _
    (fun hh => Vn hh n) t (hG n (Finset.mem_range.1 hn)) a₀).const_smul _, ?_⟩
  refine ContDiff.sum fun n hn => ContDiff.const_smul _ ?_
  show ContDiff ℝ (r : ℕ∞) (fun x => ∑ hh ∈ Finset.range (H + 1),
    (ocEll q Λ m ν ^ 2)⁻¹ • (ocDStar q Λ m ν B / ρ) ^ (n + 1) •
      cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
        (ocEpsilon q Λ m) Acl (Vn hh n) t
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x))
  refine ContDiff.sum fun hh hhm => ?_
  have hq := contDiff_cleanupRemainder_sample_of_box (r := r) hAcl (by omega)
    (by omega : r ≤ max (Llift + 1) (Llift + 2)) (ocEll q Λ m ν ^ 2)⁻¹
    ρ (ocEpsilon q Λ m) t
    (hbox n (Finset.mem_range.1 hn) hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)))
  exact ((hq.comp (hψ.of_le (by exact_mod_cast le_top))).const_smul _).const_smul _

/-- **The glued lifted coarse flux slices at one time of the window.** -/
theorem ReconWindowAt.glued_lift_slice
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ s' k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => G s' x k'))
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (max (Llift + 1) (Llift + 2)) Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hGp : ∀ k', IsZ2Periodic (fun x => G t x k'))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' =>
        gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x' a₀) x) ≤
      ENNReal.ofReal (liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
        ENNReal.ofReal ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
        CoarseFluxDiff.fluxDensity ρ kres π G t ∧
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' =>
        gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x') x) ≤
      ENNReal.ofReal (liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
        ENNReal.ofReal ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
        CoarseFluxDiff.fluxDensity ρ kres π G t := by
  classical
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  set S' := (ocObsPulses α q Λ m tp (tp + Tobs)).filter (fun k => F.weight (pp k) t ≠ 0)
    with hS'
  have hmem : ∀ k ∈ S', k ∈ ocObsPulses α q Λ m tp (tp + Tobs) ∧ F.weight (pp k) t ≠ 0 :=
    fun k hk => Finset.mem_filter.1 hk
  have hw0 : ∀ k ∈ S', 0 ≤ F.weight (pp k) t := fun k hk => w.hpart.1 k (hmem k hk).1 t
  have hw1 : ∑ k ∈ S', F.weight (pp k) t = 1 :=
    sum_filter_weight_eq_one _ (fun k => F.weight (pp k) t) (w.hpart.2.2.1 t ht)
  have hwin : ∀ k ∈ S', t ∈ ocPulseWindow α q Λ m k := fun k hk =>
    w.hpart.2.2.2.1 k (hmem k hk).1 t (hmem k hk).2
  have hcell : ∀ k ∈ S', (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk => AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk) ht
  have hsl := fun k (hkS : k ∈ S') => w.pulse_lift_slice hSb hAcl hK hrL hk hNχ hCg hgr G hG
    (Vn k) (hmem k hkS).1 ht (hwin k hkS) hGp (fun hh hhh n' hn' => hV k (hmem k hkS).1 hh hhh
      n' hn' _ (hcell k hkS)) hrs hrse hj β
  have hcd := fun k (hk : k ∈ S') => w.pulse_lift_contDiff (k := k) hAcl hrL _ (Vn k)
    (fun hh hhh n' hn' => hV k (hmem k hk).1 hh hhh n' hn' _ (hcell k hk))
  have hF : ∀ a₀ : Fin 2, (fun x' =>
      gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x' a₀) = fun x' =>
      ∑ k ∈ S', F.weight (pp k) t • liftFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vn k) t x' a₀ := fun a₀ =>
    funext fun x' => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
  have hf : (fun x' =>
      gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x') = fun x' =>
      ∑ k ∈ S', F.weight (pp k) t • liftForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vn k) t x' :=
    funext fun x' => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
  refine ⟨?_, ?_⟩
  · simp only [hF]
    exact fluxInt_word_convex_le S' (fun k => F.weight (pp k) t) hw0 hw1
      (fun k y l => liftFluxPhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vn k) t y l)
      (fun k hk l => ((hcd k hk).1 l).of_le (by exact_mod_cast hj)) rs β π
      (fun k hk _ => (hsl k hk).1)
  · simp only [hf]
    exact scalInt_word_convex_le S' (fun k => F.weight (pp k) t) hw0 hw1
      (fun k y => liftForcePhys
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (Vn k) t y)
      (fun k hk => (hcd k hk).2.of_le (by exact_mod_cast hj)) rs β π
      (fun k hk _ => (hsl k hk).2)

end AVRegularity.CycleComparison.Reconstruction
end
