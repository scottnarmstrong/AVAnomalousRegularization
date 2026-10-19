-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Seed.SeedLedgerDecayConversion
public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients

/-! **Radius rescaling of the molecular envelopes** (E2 part F). A molecular envelope at radius
`ρ` gives one at any smaller radius `ρ' ≥ ρ/λ` (`λ ≥ 1`) with the constants multiplied by
`λ^{D-2}`, `D` a bound for the maximal orders: the molecular jet is increasing in the radius, and
the order-`d` weight `(νρ^{d-2})⁻¹` grows by at most `λ^{d-2}` (`molecularEnvelope_rescale`,
`pointwiseMolecularEnvelope_rescale`). The pointwise envelope is monotone in its jet count and
constants (`pointwiseMolecularEnvelope_mono`, the analogue of `molecularEnvelope_mono`).

Special cases:
- `λ = 1`, `ρ' = ρ`: the same envelope.
- `D ≤ 2`: only order `2` occurs; the weight `ν⁻¹` does not change and the factor is `1`.
- No identities: both sides are empty sums. -/

/-- The molecular jet is increasing in the radius. -/
theorem molecularJet_radius_mono {κ : Type*} {ρ ρ' e : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' ≤ ρ)
    (he : 0 < e) (k j : ℕ) (dom : κ → Set (ℝ × Vec 2)) (a : κ → ℝ → Vec 2 → Vec 2 → Vec 2) :
    molecularJet ρ' e k j dom a ≤ molecularJet ρ e k j dom a := by
  unfold molecularJet
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ' hρ _) (by positivity)

/-- The pointwise molecular jet is increasing in the radius. -/
theorem pointwiseMolecularJet_radius_mono {κ : Type*} {ρ ρ' e : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' ≤ ρ)
    (he : 0 < e) (k j : ℕ) (dom : κ → Set (ℝ × Vec 2)) (a : κ → ℝ → Vec 2 → Vec 2 → Vec 2) :
    pointwiseMolecularJet ρ' e k j dom a ≤ pointwiseMolecularJet ρ e k j dom a := by
  unfold pointwiseMolecularJet
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ' hρ _) (by positivity)

/-- The order weight `(νρ^n)⁻¹` grows by at most `λ^N` when the radius shrinks by `λ`, `n ≤ N`. -/
theorem inv_radius_weight_le {ν ρ ρ' lam : ℝ} (hν : 0 < ν) (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ)
    (hρlam : ρ ≤ lam * ρ') (hlam : 1 ≤ lam) {n N : ℕ} (hn : n ≤ N) :
    (ENNReal.ofReal (ν * ρ' ^ n))⁻¹ ≤
      ENNReal.ofReal (lam ^ N) * (ENNReal.ofReal (ν * ρ ^ n))⁻¹ := by
  have hρ : 0 < ρ := hρ'.trans_le hρ'ρ
  have h1 : 0 < ν * ρ' ^ n := mul_pos hν (pow_pos hρ' n)
  have h2 : 0 < ν * ρ ^ n := mul_pos hν (pow_pos hρ n)
  rw [← ENNReal.ofReal_inv_of_pos h1, ← ENNReal.ofReal_inv_of_pos h2,
    ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ h2, inv_mul_le_iff₀ h1]
  have hpow : ρ ^ n ≤ lam ^ N * ρ' ^ n :=
    calc ρ ^ n ≤ (lam * ρ') ^ n := pow_le_pow_left₀ hρ.le hρlam n
      _ = lam ^ n * ρ' ^ n := mul_pow _ _ _
      _ ≤ lam ^ N * ρ' ^ n :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlam hn) (pow_nonneg hρ'.le n)
  nlinarith [mul_le_mul_of_nonneg_left hpow hν.le]

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **Radius rescaling of a molecular envelope.** -/
theorem molecularEnvelope_rescale (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ)
    (dom : F.Domain) {ν e E ρ ρ' lam : ℝ} (hν : 0 < ν) (he : 0 < e) (hρ' : 0 < ρ')
    (hρ'ρ : ρ' ≤ ρ) (hρlam : ρ ≤ lam * ρ') (hlam : 1 ≤ lam) {Dmax : ℕ}
    (hmax : ∀ v u (γ : F.Γ v u), (F.identity v u γ).maxOrder ≤ Dmax) {C : ℕ → ℝ} {J : ℕ}
    {b : ι → ι → ℝ} (hM : IsMolecularEnvelope F π K dom ν e E ρ C J b) :
    IsMolecularEnvelope F π K dom ν e E ρ' (fun j => lam ^ (Dmax - 2) * C j) J b := by
  refine ⟨hM.1, fun v u j hj => ?_⟩
  set c := ENNReal.ofReal (lam ^ (Dmax - 2)) with hc
  have hterm : ∀ (γ : F.Γ v u), ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∀ I : DerivativeWord2 (d - 1),
      molecularJet ρ' e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ' ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≤
      c * (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) := by
    intro γ d hd I
    have hdN : d - 2 ≤ Dmax - 2 := Nat.sub_le_sub_right
      ((Finset.mem_Icc.1 hd).2.trans (hmax v u γ)) 2
    calc _ ≤ molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (c * (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹) *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) := by
          gcongr
          · exact molecularJet_radius_mono hρ'.le hρ'ρ he _ _ _ _
          · exact inv_radius_weight_le hν hρ' hρ'ρ hρlam hlam hdN
      _ = _ := by ring
  have h1 : ∀ γ : F.Γ v u,
      (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        molecularJet ρ' e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ' ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      c * ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) := by
    intro γ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun I _ => hterm γ d hd I
  have h2 := hM.2 v u j hj
  calc _ ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) *
        (c * ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
              (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
              ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) := by
        refine mul_le_mul_right ?_ _
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun γ _ => ?_
        rw [mul_left_comm]
        exact mul_le_mul_right (h1 γ) _
    _ = c * (ENNReal.ofReal (Real.sqrt (π u / π v)) *
        ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
              (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
              ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) :=
        mul_left_comm _ _ _
    _ ≤ c * ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u) := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (lam ^ (Dmax - 2) * C j * (E ^ j)⁻¹ * b v u) := by
        rw [hc, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
        congr 1
        ring

/-- **Radius rescaling of a pointwise molecular envelope.** -/
theorem pointwiseMolecularEnvelope_rescale (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (K : ι → ℕ) (dom : F.Domain) {ν e E ρ ρ' lam : ℝ} (hν : 0 < ν) (he : 0 < e) (hρ' : 0 < ρ')
    (hρ'ρ : ρ' ≤ ρ) (hρlam : ρ ≤ lam * ρ') (hlam : 1 ≤ lam) {Dmax : ℕ}
    (hmax : ∀ v u (γ : F.Γ v u), (F.identity v u γ).maxOrder ≤ Dmax) {C : ℕ → ℝ} {J : ℕ}
    {b : ι → ι → ℝ} (hM : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b) :
    IsPointwiseMolecularEnvelope F π K dom ν e E ρ' (fun j => lam ^ (Dmax - 2) * C j) J b := by
  refine ⟨hM.1, fun v u j hj => ?_⟩
  set c := ENNReal.ofReal (lam ^ (Dmax - 2)) with hc
  have hterm : ∀ (γ : F.Γ v u), ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∀ I : DerivativeWord2 (d - 1),
      pointwiseMolecularJet ρ' e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ' ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≤
      c * (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) := by
    intro γ d hd I
    have hdN : d - 2 ≤ Dmax - 2 := Nat.sub_le_sub_right
      ((Finset.mem_Icc.1 hd).2.trans (hmax v u γ)) 2
    calc _ ≤ pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (c * (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹) *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) := by
          gcongr
          · exact pointwiseMolecularJet_radius_mono hρ'.le hρ'ρ he _ _ _ _
          · exact inv_radius_weight_le hν hρ' hρ'ρ hρlam hlam hdN
      _ = _ := by ring
  have h1 : ∀ γ : F.Γ v u,
      (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        pointwiseMolecularJet ρ' e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ' ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      c * ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) := by
    intro γ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun I _ => hterm γ d hd I
  have h2 := hM.2 v u j hj
  calc _ ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) *
        (c * ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
              (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
              ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) := by
        refine mul_le_mul_right ?_ _
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun γ _ => ?_
        rw [mul_left_comm]
        exact mul_le_mul_right (h1 γ) _
    _ = c * (ENNReal.ofReal (Real.sqrt (π u / π v)) *
        ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
              (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
              ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) :=
        mul_left_comm _ _ _
    _ ≤ c * ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u) := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (lam ^ (Dmax - 2) * C j * (E ^ j)⁻¹ * b v u) := by
        rw [hc, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
        congr 1
        ring

/-- **The pointwise molecular envelope is monotone in its jet count and constants.** -/
theorem pointwiseMolecularEnvelope_mono (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (K : ι → ℕ) (dom : F.Domain) (ν e E ρ : ℝ) (hE : 0 ≤ E) {C C' : ℕ → ℝ} {J J' : ℕ}
    (hJ : J ≤ J') (hC : ∀ j, C j ≤ C' j) {b : ι → ι → ℝ} (hb : ∀ v u, 0 ≤ b v u)
    (hM : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J' b) :
    IsPointwiseMolecularEnvelope F π K dom ν e E ρ C' J b := by
  refine ⟨Construction.Preservation.Seed.smoothOn_domain_order_mono F (fun _ _ => le_rfl)
    (fun _ => Nat.add_le_add_left hJ _) hM.1, fun v u j hj => ?_⟩
  exact (hM.2 v u j (hj.trans hJ)).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC j)
      (inv_nonneg.mpr (pow_nonneg hE _))) (hb v u)))

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.EntryTerminal.Ingredients

/-! **Scale and structure facts for the family premises of E2** (part F).
- The Péclet cap `ε_M ≤ √(κ_M/a_M)` for every large `M` (`exists_peclet_cap`; from the weak scale
  ledger `weak_scales_core` at `i = M + 1`, as in the weak kernel widths), so the molecular radius
  `rhoStar D c M = c ε_M`.
- Descending slots from the depth rank: `K_v = D(H − rank v)` with `D` a bound for the maximal
  orders (`isDescending_descSlots`).
- The natural pieces cover every time: the partition `∑_p ϖ_p(t) = 1` and the weights vanish off
  the outputs (`exists_piece_of_natural`).

Special cases:
- An edge-free family: every rank is `0` and `K = D H` is constant.
- `D = 0`: the slots vanish; only identities of order `0` can be descending, and there are none of
  order `≥ 2`.
- `M` below the threshold: no claim. -/

open AVRegularity.EntryTerminal.Route

/-- **The Péclet cap** `ε_M ≤ √(κ_M / a_M)` at every large level. -/
theorem exists_peclet_cap (X : TermConstruction) {Λ : ℕ} (hΛ : 128 ≤ Λ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain X.α X.q Λ X.ζ M κ →
      ocEpsilon X.q Λ M ≤ Real.sqrt (κ M / ocA X.α X.q Λ M) := by
  obtain ⟨Cw, hCw, hweak⟩ := EntryScales.weak_scales_core X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
  have hγ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).1
  have hCwp : 0 < Cw := zero_lt_one.trans_le hCw
  have hevent := (EntryScales.epsilon_rpow_tendsto_zero X.hq.1 hΛ hγ).eventually
    (gt_mem_nhds (inv_pos.mpr hCwp))
  obtain ⟨Mf, hMf⟩ := eventually_atTop.mp hevent
  refine ⟨Mf, fun M hM κ hκ => ?_⟩
  have hx := Scales.epsilon_basic (m := M) X.hq.1 hΛ
  have hν : 0 < κ M := CycleReference.bandChain_pos (by omega) X.hζ hκ le_rfl
  have hA : 0 < ocA X.α X.q Λ M := by
    change 0 < ocEpsilon X.q Λ M ^ ((1 + X.α) - 2)
    exact Real.rpow_pos_of_pos hx.1 _
  have hsmall : Cw * ocEpsilon X.q Λ M ^ ocGamma X.α X.q ≤ 1 := by
    have hs := (hMf M hM).le
    have hh := mul_le_mul_of_nonneg_left hs hCwp.le
    rwa [mul_inv_cancel₀ hCwp.ne'] at hh
  have hweakM := (hweak Λ hΛ M (κ M) hκ.1 (M + 1) (by omega)).2.1
  simp only [Nat.add_sub_cancel] at hweakM
  apply Real.le_sqrt_of_sq_le
  have hh := (div_le_one hν).mp (hweakM.trans hsmall)
  exact (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)

section Slots

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The descending slots `K_v = D(H − rank v)`. -/
def descSlots (F : ChartedFamily ι h D P Ctx) (H Dmax : ℕ) (v : ι) : ℕ :=
  Dmax * (H - CycleWords.familyDepthRank F H v)

theorem descSlots_le (F : ChartedFamily ι h D P Ctx) (H Dmax : ℕ) (v : ι) :
    descSlots F H Dmax v ≤ Dmax * H :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- **The depth rank gives descending slots.** -/
theorem isDescending_descSlots (F : ChartedFamily ι h D P Ctx) {H Dmax : ℕ}
    (hdepth : F.HasDepthAtMost H)
    (hmax : ∀ v u (γ : F.Γ v u), (F.identity v u γ).maxOrder ≤ Dmax) :
    F.IsDescending (descSlots F H Dmax) := by
  intro v u γ
  have hr := CycleWords.familyDepthRank_strict F H hdepth ⟨γ⟩
  have hv := CycleWords.familyDepthRank_le F H v
  have hsub : H - CycleWords.familyDepthRank F H v + 1 ≤
      H - CycleWords.familyDepthRank F H u := by omega
  have hm := Nat.mul_le_mul_left Dmax hsub
  rw [Nat.mul_add, Nat.mul_one] at hm
  have hγ := hmax v u γ
  unfold descSlots
  linarith

end Slots

/-- **The natural pieces cover every time.** -/
theorem exists_piece_of_natural {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm b j₀) {M : ℕ} (hnat : G.IsNatural M) (hΛ : 1 ≤ D.Λ) (t : ℝ) :
    ∃ p, t ∈ (G.fam.piece p).output := by
  by_contra hno
  push Not at hno
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have h1 := WeakEntryProofs.ocCutoff_finsum_one D.α D.q D.Λ G.level hτ t
  have h0 : (fun p : OddSlot => ocCutoff D.α D.q D.Λ G.level p.1 t) = fun _ => 0 := by
    funext p
    rw [← hnat.2.1 p t]
    exact G.fam.weight_zero p t (hno p)
  rw [h0, finsum_zero] at h1
  exact zero_ne_one h1

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The family premises of the capped preparation on the actual-context family** (`PrepFamilyPart`).
Every premise of `PrepFamilyPremises` on `F⋆ = Gw.actualFamily` comes from `IsWeakStage`, through
the actual-family adapter (`Families/ActualFamily/*`):
- masses: positive birth masses; slots: `K = D_W(d_W − rank)` (`isDescending_descSlots`, the depth
  `d_W` and the maximal orders `≤ D_W` of `IsWeakStage`), so `K_max = D_W d_W`;
- weights: the partition `ϖ_p = ocCutoff` (natural pieces); the cover: the partition sums to one
  (`exists_piece_of_natural`); time measurability: `isTimeMeasurable_actualFamily_of_certified`
  from the context certificate and the natural outputs;
- depth, torus compatibility, transversality on the enlarged pulses (cut to the window), fast
  independence on the trimmed quiet times and the atlas (`actualAtlas`): the stage invariant;
- the envelope: the stage invariant's envelope clause at the strength `S = C_χ x^{χ_w} = C_θ Θ` with
  `Θ = x^{χ_w} ≤ 1`; the pointwise envelope: `IsSeedPointwiseMolecular`. Both are at the radius
  `rhoStar D c_K M = c_K x` (Péclet cap, `exists_peclet_cap`), lowered to `ϱ = min{c_K, c_cov} x`
  at the factor `(c_K / min{c_K, c_cov})^{D_W − 2}` (`molecularEnvelope_rescale`), with the orders
  reduced to `K_s, L_s, J_m ≤ K_need`.
The window `[a_M, a_M + 2h]` lies in the weak window `[a_M, a + T₀]` for large `M`
(`exists_entry_wait`).

For an empty weak family every clause is about empty sums. If `c_cov ≥ c_K`, then `ϱ = c_K x` and
the factor is `1`. For an edge-free weak family `K = D_W d_W` is constant. -/

open AVRegularity.EntryTerminal.Route

/-- **The family premises of the capped preparation.** -/
theorem prepFamilyPart : PrepFamilyPart := by
  intro X
  refine ⟨128, le_rfl, fun PA hΛ hPA => ?_⟩
  refine ⟨PA.DW * PA.dW, fun Ks Ls Jm =>
    ⟨max (PA.DW * PA.dW) (max Ks (max Ls Jm)), le_max_left _ _, ?_⟩⟩
  intro nW cK CL Cχ kW hcK hc₀ hKs hKan hLan hJm ccov hccov
  set lam := cK / min cK ccov with hlam
  refine ⟨kW.Ca, Cχ, fun j => lam ^ (PA.DW - 2) * kW.Cm j, fun j₀ => ?_⟩
  obtain ⟨-, -, -, ⟨-, hτ, hτT, -, -, -, hχw, -, -⟩, -, -⟩ := hPA
  obtain ⟨Mw, hMw⟩ := exists_entry_wait X.hα₀ X.hα₁ X.hq (by omega : 2 ≤ PA.Λ) 1 PA.Jw PA.T₀
    (hτ.trans hτT)
  obtain ⟨Mp, hMp⟩ := exists_peclet_cap X hΛ
  refine ⟨max (max 1 j₀) (max Mw Mp), fun M hM => ?_⟩
  simp only [max_le_iff] at hM
  obtain ⟨⟨hM1, hMj⟩, hMMw, hMMp⟩ := hM
  intro D hD a lawW PW Gw aM hW
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := hD
  have hwait := hMw M hMMw
  have hcap := hMp M hMMp D.κ hband
  have hν : 0 < D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  rw [← hDα, ← hDq, ← hDΛ] at hwait hcap
  rw [← hDα, ← hDq, ← hDΛ, ← hDζ]
  have hΛ128 : 128 ≤ D.Λ := hDΛ ▸ hΛ
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hq1 : 1 < D.q := hDq ▸ X.hq.1
  have hε := Scales.epsilon_basic (m := M) hq1 hΛ128
  have hε' := Scales.epsilon_basic (m := M - 1) hq1 hΛ128
  -- the weak stage
  have hlev : Gw.level = M := hW.2.2.1
  have hdepthW : Gw.fam.HasDepthAtMost PA.dW := hW.2.2.2.1
  have hmax : ∀ v u (γ : Gw.fam.Γ v u), (Gw.fam.identity v u γ).maxOrder ≤ PA.DW :=
    fun v u γ => (hW.2.2.2.2.2.2.1 v u γ).1
  have haM : aM ≤ a + 6 * PA.Jw * ocTauPP D.α D.q D.Λ (M + 1) := hW.2.1
  have hpw : IsSeedPointwiseMolecular lawW kW Gw aM (a + PA.T₀) := hW.2.2.2.2.2.1.2.2
  obtain ⟨hnat, -, -, -, -, hcert, henvI, -, -, -, ⟨T, hTc, hTv, hTq, -, -⟩, htr, hfi, -⟩ :=
    hW.2.2.2.2.2.2.2.2.2
  have hact : ∀ p, (Gw.actual p).1 = nativeChain Gw.level p.1 := hnat.2.2.1
  have hi : 1 ≤ Gw.level := by omega
  have hjl : j₀ ≤ Gw.level := by omega
  -- the window and the radius
  have hWsub : Set.Icc aM (aM + 2 * ocTauPP D.α D.q D.Λ M) ⊆ Set.Icc aM (a + PA.T₀) := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rw [abs_one] at hwait
    have := ht.2
    linarith
  have hkap : D.kap Gw.level = D.κ M := by
    rw [hlev]
    unfold OCData.kap
    rw [hterm, min_self]
  have hrho : rhoStar D kW.c₀ Gw.level = cK * D.eps M := by
    rw [hlev, hc₀]
    have hcap' : D.eps M ≤ Real.sqrt (D.κ M / ocA D.α D.q D.Λ M) := hcap
    unfold rhoStar
    rw [min_eq_left hcap']
  set x := ocEpsilon D.q D.Λ M with hx
  have hmin0 : 0 < min cK ccov := lt_min hcK hccov
  have hρ' : 0 < min cK ccov * x := mul_pos hmin0 hε.1
  have hρ'ρ : min cK ccov * x ≤ cK * x := mul_le_mul_of_nonneg_right (min_le_left _ _) hε.1.le
  have hρlam : cK * x ≤ lam * (min cK ccov * x) := by
    rw [hlam, ← mul_assoc, div_mul_cancel₀ _ hmin0.ne']
  have hlam1 : 1 ≤ lam := by
    rw [hlam, le_div_iff₀ hmin0, one_mul]
    exact min_le_left _ _
  have hE0 : 0 ≤ D.eps (M - 1) := hε'.1.le
  -- slots
  set K : CompIn Gw.comps → ℕ := descSlots Gw.fam PA.dW PA.DW with hK
  have hKs' : ∀ v, K v ≤ kW.Ks :=
    fun v => (descSlots_le _ _ _ v).trans ((le_max_left _ _).trans hKs)
  have hKsKan : Ks ≤ kW.Kan := (le_max_left _ _).trans ((le_max_right _ _).trans hKan)
  have hLsLan : Ls ≤ kW.Lan :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLan))
  have hJmJm : Jm ≤ kW.Jm :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJm))
  -- the envelopes
  have hE := (henvI K hKs').1
  rw [hkap, hrho] at hE
  simp only [hlev] at hE
  have hE' := Gw.isEnvelope_actualFamily hWsub kW.mEnv hact hi hjl hE
  have hP := hpw K hKs'
  rw [hkap, hrho] at hP
  simp only [hlev] at hP
  have hP' := Gw.isPointwiseMolecularEnvelope_actualFamily hWsub kW.mEnv hact hi hjl hP
  have hmaxF : ∀ v u (γ : Gw.actualFamily.Γ v u),
      (Gw.actualFamily.identity v u γ).maxOrder ≤ PA.DW := hmax
  -- transversality, fast independence, atlas
  simp only [hlev] at htr hfi hTv
  rw [hkap] at hTq
  simp only [hlev] at hTq
  have htr' : Gw.fam.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau D.α D.q D.Λ M)
        (((k.1 : ℝ) + 3 / 4) * ocTau D.α D.q D.Λ M) ∩
          Set.Icc aM (aM + 2 * ocTauPP D.α D.q D.Λ M))
      (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1) :=
    fun k p c v u γ d I t ht => htr k p c v u γ d I t ⟨⟨ht.1.1, hWsub ht.1.2⟩, ht.2⟩
  refine ⟨K, fun v u => ∑ γ : Gw.fam.Γ v u,
      ‖(Gw.fam.identity v u γ).map‖ * (Gw.fam.identity v u γ).record.size,
    x ^ PA.χw, Gw.actualAtlas T, ?_⟩
  exact
    { hπ := fun v => Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛ128 lawW v.1
      hK := fun v => descSlots_le _ _ _ v
      hwmeas := fun p => by
        have hw : Gw.actualFamily.weight p = ocCutoff D.α D.q D.Λ Gw.level p.1 :=
          funext (hnat.2.1 p)
        rw [hw]
        exact (CycleReference.ocCutoff_contDiff hΛ1 p.1).continuous.measurable
      hdepth := Gw.hasDepthAtMost_actualFamily hdepthW
      hdesc := Gw.isDescending_actualFamily (isDescending_descSlots Gw.fam hdepthW hmax)
      htorus := Gw.isTorusCompatible_actualFamily (IsWeakStage.isTorusCompatible hW)
      hcover := fun t _ => Set.mem_iUnion.2 (exists_piece_of_natural Gw hnat hΛ1 t)
      hmeas := Gw.isTimeMeasurable_actualFamily_of_certified hcert fun p => (hnat.1 p).2.1
      hΘ₀ := Real.rpow_nonneg hε.1.le _
      hΘ₁ := Real.rpow_le_one hε.1.le hε.2.1 hχw.le
      henv := ⟨hE'.nonneg, hE'.row_sum, hE'.col_sum,
        Construction.Preservation.Seed.analyticEnvelope_mono _ _ (fun _ _ => le_rfl) _ _ _
          hKsKan hLsLan _ hE'.nonneg le_rfl hE'.analytic,
        molecularEnvelope_rescale _ _ _ _ hν hε.1 hρ' hρ'ρ hρlam hlam1 hmaxF
          (Construction.Preservation.Seed.molecularEnvelope_mono _ _ _ (fun _ _ => le_rfl)
            _ _ _ _ hE0 _ _ hJmJm (fun _ => le_rfl) _ hE'.nonneg hE'.molecular)⟩
      hpointwise := pointwiseMolecularEnvelope_rescale _ _ _ _ hν hε.1 hρ' hρ'ρ hρlam hlam1
        hmaxF (pointwiseMolecularEnvelope_mono _ _ _ _ _ _ _ _ hE0 hJmJm (fun _ => le_rfl)
          hE'.nonneg hP')
      htrans := Gw.isTransverseOnPulses_actualFamily htr'
      hquiet := Gw.isFastIndependentOn_actualFamily
        (CycleComparison.isFastIndependentOn_mono Gw.fam (Set.inter_subset_inter_right _ hWsub)
          hfi)
      hTcons := Gw.actualAtlas_isConsecutiveClosed fun p q hpq hlab hne =>
        hTc p q hpq hlab (hne.mono (Set.inter_subset_inter_right _ hWsub))
      hTcov := Gw.actualAtlas_coversQuiet fun p q hpq t ht Y =>
        hTv p q hpq t ⟨⟨⟨ht.1.1.1, hWsub ht.1.1.2⟩, ht.1.2⟩, ht.2⟩ Y
      hTq := Gw.actualAtlas_isQuiet hTq }

end AVRegularity.EntryTerminal.Ingredients
end
