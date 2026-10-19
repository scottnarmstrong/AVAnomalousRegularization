-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.RowMaster
import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
public import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.StageForced
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Assembly
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.ComponentStrong
import AVRegularity.Construction.EntryScales.TerminalCore

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The rows of the root flux defects are `C^{k_c+2p_T}`**.

`FilterRowSmoothStatement`, proved: `rootFluxDefect_smooth` with the coefficient smoothness
`termCtx_physCoeff` at the order `n = k_c + 2p_T`, the proof of `termReconReadoutSmooth_proof`
with `n` in place of `2p_T` (the order floor is taken after `k_c`).

Special case: `k_c = 0` is the smoothness clause of the mean flux split. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The rows are `C^{k_c+2p_T}`, from the certificate and the floors.** -/
theorem filterRowSmoothAt_of_certificate
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc : ℕ) (hA : A.Valid) (hΛ : 128 ≤ A.Λ)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hK : kc + 2 * A.pT + A.Dt + 2 ≤ A.Khat Kout) :
    FilterRowSmoothAt c x kc := by
  intro v t ht
  have hST := termCtx_slotTransverse c x hA hΛ hCH hΥ hcar hX hZ
  have hSH := termCtx_shiftInvariant c hΛ
  have hφ := hA.2.1
  have hcoef := fun v u γ d => termCtx_physCoeff c x x.cert hST hSH hA hΛ hj hM2
    (kc + 2 * A.pT) v u γ d t
  exact rootFluxDefect_smooth (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.φ₀ hφ.1 hφ.2.2.2 c.Gw c.Gt' x.aZ t (kc + 2 * A.pT) hcoef
      (fun u => by
        obtain ⟨-, h1, h2, -⟩ := x.repZ u t ht
        exact ⟨h1.of_le (WithTop.coe_le_coe.2 (Nat.cast_le.2 (by omega))), h2⟩) v

/-- **`FilterRowSmoothStatement`.** -/
theorem filterRowSmooth_proof : FilterRowSmoothStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ?_⟩⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, kc + 2 * A.pT + A.Dt + 2, fun sXT sZT hX hZ Kout hKout => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ hcr0 hcr1 hcr _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ hcar => ⟨j₀ + 2, fun M hM c x => ?_⟩⟩
  exact filterRowSmoothAt_of_certificate c x kc hV hΛ le_rfl le_rfl hcar hX hZ (by omega)
    (by omega) (le_trans hKout (le_max_left _ _))

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **The mass of the root flux defect rows at a terminal context, from named inputs.**

`filterRowMassAt_of_inputs` proves `FilterRowMassAt c x kc C` from

* `CoeffReg`: the coefficients of all identities of `Gt'` are measurable, `C^{k_c+2p_T}`, periodic
  and of finite seminorm on the window;
* `FilterSchurWAt`: the Schur bound `(C/K_c) x^{χ_w}` of the coefficients of the identities from
  `Gw` with a seed kernel, weighted by `κ_{M-1}`, the radius `ρ`, the masses of `Gt'` and the
  widths `r_w` (the weak price);
* `FilterSchurFAt`: the Schur bound `(C/K_c) E^{b_T}` of the identities from `Gw` with a fresh
  kernel at the widths `r_new` (the fresh price);
* `FilterEnergyAt`: a zero extension to the rows of `Gt'` of a truncation of the readout of the
  retained solution, with the energy bound `√(|W|+1) √2 max(C_P,0) ‖f‖₂`;
* the scale facts `r_w ≤ ρ`, `r_new ≤ ρ`.

The two kernels are constant, `r_new = ρ E^{t_T}`, so the fresh ratio is `E^{t_T}` and the price
`E^{b_T} (E^{t_T})^{L_c} = E^{b_T + t_T L_c}`. The constant `K_c` absorbs the two defect
constants `Mc` and the energy constant.

Special cases: `C = 0` forces `θ = 0`, the bound is `0 ≤ 0`; an empty window. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Arith

/-- The arithmetic of the two prices. -/
theorem filter_arith {qw qf X Y Mw Mf Eb N C Kc : ℝ} {Lw Lf : ℕ} (hqw : 0 ≤ qw) (hqf : 0 ≤ qf)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hMw : 0 ≤ Mw) (hMf : 0 ≤ Mf) (hEb : 0 ≤ Eb) (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hKc : Kc = (Mw + Mf + 1) * (Eb + 1)) :
    qw ^ Lw * Mw * (C / Kc * X) * (Eb * N) + qf ^ Lf * Mf * (C / Kc * Y) * (Eb * N) ≤
      C * (Y * qf ^ Lf + X * qw ^ Lw) * N := by
  have hKpos : 0 < Kc := by rw [hKc]; positivity
  have h1 : Eb * Mw ≤ Kc := by rw [hKc]; nlinarith [mul_nonneg hMw hEb, mul_nonneg hMf hEb]
  have h2 : Eb * Mf ≤ Kc := by rw [hKc]; nlinarith [mul_nonneg hMw hEb, mul_nonneg hMf hEb]
  have hw : 0 ≤ qw ^ Lw * X * N := by positivity
  have hf : 0 ≤ qf ^ Lf * Y * N := by positivity
  have e1 : qw ^ Lw * Mw * (C / Kc * X) * (Eb * N) = C * (Eb * Mw / Kc) * (qw ^ Lw * X * N) := by
    field_simp
  have e2 : qf ^ Lf * Mf * (C / Kc * Y) * (Eb * N) = C * (Eb * Mf / Kc) * (qf ^ Lf * Y * N) := by
    field_simp
  have h3 : Eb * Mw / Kc ≤ 1 := (div_le_one hKpos).2 h1
  have h4 : Eb * Mf / Kc ≤ 1 := (div_le_one hKpos).2 h2
  have h5 : C * (Eb * Mw / Kc) * (qw ^ Lw * X * N) ≤ C * 1 * (qw ^ Lw * X * N) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC) hw
  have h6 : C * (Eb * Mf / Kc) * (qf ^ Lf * Y * N) ≤ C * 1 * (qf ^ Lf * Y * N) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hC) hf
  rw [e1, e2]
  nlinarith [h5, h6]

end Arith

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The energy constant `√(|W_{R_T+1}|+1) √2 max(C_P,0)` (without `‖f‖₂`). -/
def filterEb (A : TermArgs X) (CP : ℝ) : ℝ :=
  Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * (Real.sqrt 2 * max CP 0)

/-- The constant absorbing the two defect constants and the energy constant. -/
def filterKc (A : TermArgs X) (CP : ℝ) (kc : ℕ) : ℝ :=
  (Mc A.φ₀ A.LoT (kc + 2 * A.pT) A.Dt + Mc A.φ₀ A.LcT (kc + 2 * A.pT) A.Dt + 1) *
    (filterEb A CP + 1)

/-- The order of the truncation of the readout. -/
def filterK (A : TermArgs X) (kc : ℕ) : ℕ :=
  kc + 2 * A.pT + (A.Dt - 2) + max A.LoT A.LcT

/-- The edges from `Gw` with a seed (weak) kernel. -/
def filterEdgeW : ∀ v u : CompIn c.Gt'.comps, c.Gt'.fam.Γ v u → Prop :=
  fun v u γ => u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ

/-- The edges from `Gw` with a fresh kernel. -/
def filterEdgeF : ∀ v u : CompIn c.Gt'.comps, c.Gt'.fam.Γ v u → Prop :=
  fun v u γ => u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ

/-- **(SW), the weak price.** -/
def FilterSchurWAt (kc : ℕ) (C : ℝ) : Prop :=
  SchurBound (C / filterKc A CP kc * c.D.eps M ^ A.χw)
    (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root) (c.D.κ (M - 1))
      (c.D.termRho cr M) (c.Gt'.mass c.lawT) (kc + 2 * A.pT) A.Dt c.tp (c.a + A.T₀)
      (fun _ => 1) (fun _ _ _ => c.D.termRW A.σw M)
      (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
      (filtCoeff c.Gt' (filterEdgeW c)))

/-- **(SF), the fresh price.** -/
def FilterSchurFAt (kc : ℕ) (C : ℝ) : Prop :=
  SchurBound (C / filterKc A CP kc * c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ -
      A.η₀ / 4 - A.tT * (termExcess A.NT A.pT A.alph : ℝ)))
    (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root) (c.D.κ (M - 1))
      (c.D.termRho cr M) (c.Gt'.mass c.lawT) (kc + 2 * A.pT) A.Dt c.tp (c.a + A.T₀)
      (fun _ => 1) (fun _ _ _ => c.D.termRNew cr A.tT M)
      (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
      (filtCoeff c.Gt' (filterEdgeF c)))

/-- **(EN), the energy of the zero extension of the readout.** -/
def FilterEnergyAt (x : TermResAux c) (kc : ℕ) : Prop :=
  ∃ V : ∀ j : CompIn c.Gt'.comps, ℝ → TorusHk (filterK A kc + 1) (ScalarH j.1.root),
    (∀ j, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (V j t) (extAZ c.Gw c.Gt' x.aZ j t) (filterK A kc + 1)) ∧
    (∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    Integrable (fun t => massGradNormSq (E := fun j : CompIn c.Gt'.comps => ScalarH j.1.root)
      (K := fun _ => filterK A kc) (c.D.termRho cr M) (c.Gt'.mass c.lawT)
      (fun j => (V j t).val)) (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) ∧
    Real.sqrt (c.D.κ (M - 1) * ∫ s in Set.Icc c.tp (c.a + A.T₀),
      massGradNormSq (E := fun j : CompIn c.Gt'.comps => ScalarH j.1.root)
        (K := fun _ => filterK A kc) (c.D.termRho cr M) (c.Gt'.mass c.lawT)
        (fun j => (V j s).val)) ≤ filterEb A CP * c.normF

/-- **(SC), the scale facts**: both kernel widths are at most the radius. -/
def FilterScaleAt : Prop :=
  c.D.termRW A.σw M ≤ c.D.termRho cr M ∧ c.D.termRNew cr A.tT M ≤ c.D.termRho cr M

/-- **(R)**, the regularity of the coefficients on the window. -/
def FilterRegAt (kc : ℕ) : Prop :=
  CoeffReg c.Gt' c.tp (c.a + A.T₀) (c.D.termRho cr M) (kc + 2 * A.pT)

theorem filterPrice_nonneg (hε : 0 < c.D.eps M) (hε1 : 0 < c.D.eps (M - 1))
    (hρ : 0 < c.D.termRho cr M) (hrw : 0 ≤ c.D.termRW A.σw M) : 0 ≤ c.filterPrice := by
  unfold TermResCtx.filterPrice
  positivity

theorem Mc_nonneg (φ₀ : Vec 2 → ℝ) (L k D : ℕ) : 0 ≤ Mc φ₀ L k D :=
  Finset.sum_nonneg fun m _ => mul_nonneg
    (Construction.KernelDefect.kdUniformMomentConst_nonneg φ₀ L (by norm_num))
    (by positivity)

theorem filterKc_pos (A : TermArgs X) (CP : ℝ) (kc : ℕ) : 0 < filterKc A CP kc := by
  have h1 := Mc_nonneg A.φ₀ A.LoT (kc + 2 * A.pT) A.Dt
  have h2 := Mc_nonneg A.φ₀ A.LcT (kc + 2 * A.pT) A.Dt
  have h3 : 0 ≤ filterEb A CP := by unfold filterEb; positivity
  unfold filterKc
  positivity

/-- **The mass of the root flux defect rows from the named inputs.** -/
theorem filterRowMassAt_of_inputs (x : TermResAux c) (kc : ℕ) (C : ℝ) (hV : A.Valid)
    (hKO : IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf)
    (hε : 0 < c.D.eps M) (hε1 : 0 < c.D.eps (M - 1)) (hν : 0 < c.D.κ (M - 1))
    (hρ : 0 < c.D.termRho cr M) (hπ : ∀ i, 0 < c.Gt'.mass c.lawT i) (hD : 2 ≤ A.Dt)
    (hC : 0 ≤ C) (hreg : CoeffReg c.Gt' c.tp (c.a + A.T₀) (c.D.termRho cr M) (kc + 2 * A.pT))
    (hSW : FilterSchurWAt c kc C) (hSF : FilterSchurFAt c kc C) (hEn : FilterEnergyAt c x kc)
    (hSC : FilterScaleAt c) : FilterRowMassAt c x kc C := by
  have hrw : 0 < c.D.termRW A.σw M := by unfold OCData.termRW; positivity
  have hrn : 0 < c.D.termRNew cr A.tT M := by unfold OCData.termRNew; positivity
  have hfp : 0 ≤ c.filterPrice := filterPrice_nonneg c hε hε1 hρ hrw.le
  have hN : 0 ≤ c.normF := Real.sqrt_nonneg _
  unfold FilterRowMassAt
  by_cases htime : c.tp ≤ c.a + A.T₀
  swap
  · refine hasFluxBound_of_zero _ _ _ _ _ _ (fun v t ht => ?_) (by positivity)
    exact absurd ht (by rw [Set.Icc_eq_empty htime]; exact Set.notMem_empty t)
  obtain ⟨V, hcl, hmeas, hint, hE⟩ := hEn
  obtain ⟨hd, hnn, hm, hs⟩ := hV.2.1
  have haw := WeakEntryProofs.isoPairedKernel_isAdmissible (c.D.termRW A.σw M) nW A.LoT (by have := hKO.1; omega)
  have haf := WeakEntryProofs.isoPairedKernel_isAdmissible (c.D.termRNew cr A.tT M) A.nT A.LcT
    hV.2.2.2.2.2.2.2.1.1
  have hKc := filterKc_pos A CP kc
  have hθw : 0 ≤ C / filterKc A CP kc * c.D.eps M ^ A.χw := by positivity
  have hθf : 0 ≤ C / filterKc A CP kc * c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ -
      A.η₀ / 4 - A.tT * (termExcess A.NT A.pT A.alph : ℝ)) := by positivity
  have key := rootFlux_hasFluxBound (A.Pt c.D Cw cr M) A.φ₀ A.hφ₀ hd hnn hm hs
    (isoPairedKernel (c.D.termRW A.σw M) nW) (isoPairedKernel (c.D.termRNew cr A.tT M) A.nT)
    A.LoT A.LcT haw haf hrw hrn c.Gw c.Gt' x.aZ c.tp (c.a + A.T₀) (c.D.termRho cr M)
    (c.D.κ (M - 1)) hρ hSC.1 hSC.2 hν htime (kc + 2 * A.pT) hD (c.Gt'.mass c.lawT) hπ hreg
    _ _ hθw hθf hSW hSF (K := filterK A kc) (by unfold filterK; omega) (by unfold filterK; omega)
    V hcl hmeas hint hE
  refine hasFluxBound_mono_Y key ?_
  have hq : c.D.termRNew cr A.tT M / c.D.termRho cr M = c.D.eps (M - 1) ^ A.tT := by
    unfold OCData.termRNew
    field_simp
  have hY : c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ)) * (c.D.eps (M - 1) ^ A.tT) ^ A.LcT =
      c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
        A.tT * (termExcess A.NT A.pT A.alph : ℝ) + A.tT * (A.LcT : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε1.le, ← Real.rpow_add hε1]
  have hEb : 0 ≤ filterEb A CP := by unfold filterEb; positivity
  change (c.D.termRW A.σw M / c.D.termRho cr M) ^ A.LoT * Mc A.φ₀ A.LoT (kc + 2 * A.pT) A.Dt *
      (C / filterKc A CP kc * c.D.eps M ^ A.χw) * (filterEb A CP * c.normF) +
    (c.D.termRNew cr A.tT M / c.D.termRho cr M) ^ A.LcT *
      Mc A.φ₀ A.LcT (kc + 2 * A.pT) A.Dt * (C / filterKc A CP kc * c.D.eps (M - 1) ^
        (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 - A.tT * (termExcess A.NT A.pT A.alph : ℝ))) *
      (filterEb A CP * c.normF) ≤ _
  rw [hq]
  refine (filter_arith (Lw := A.LoT) (Lf := A.LcT) (by positivity) (by positivity) (by positivity)
    (by positivity) (Mc_nonneg _ _ _ _) (Mc_nonneg _ _ _ _) hEb hN hC rfl).trans (le_of_eq ?_)
  unfold TermResCtx.filterPrice
  rw [← hY]

end Terminal

/-! ### The prefix statements and the join -/

/-- **(R)** The regularity of the coefficients of all identities of `Gt'` on the window. -/
def FilterRegStatement : Prop :=
  TermResPrefix fun c _ kc _ _ _ _ => FilterRegAt c kc

/-- **(SW)** The weak price of the Schur bound. -/
def FilterSchurWStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => FilterSchurWAt c kc C

/-- **(SF)** The fresh price of the Schur bound. -/
def FilterSchurFStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => FilterSchurFAt c kc C

/-- **(EN)** The energy of the zero extension of the readout. -/
def FilterEnergyStatement : Prop :=
  TermResPrefix fun c x kc _ _ _ _ => FilterEnergyAt c x kc

/-- **(SC)** The scale facts. -/
def FilterScaleStatement : Prop :=
  TermResPrefix fun c _ _ _ _ _ _ => FilterScaleAt c

/-- A statement at a fixed constant gives the statement at all larger constants, using the
terminal kernel orders and `A.Valid` (the prefix of `termFluxPrefix_map` with these two extra
hypotheses passed to the context-level implication). -/
theorem prefix_map {P R : TermFluxPred}
    (hmap : ∀ (X : TermConstruction) (A : TermArgs X) (kc : ℕ) (C₁ : ℝ), 128 ≤ A.Λ → A.Valid →
      0 ≤ C₁ → ∃ C₂ : ℝ,
      ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
        {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ}
        {j₀ M : ℕ},
        IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
          Cw Ce cker j₀ M) (x : TermResAux c), P c x kc C₁ → ∀ C' : ℝ, C₂ ≤ C' → R c x kc C')
    (h : TermResPrefix fun c x kc _ C _ _ => P c x kc C) :
    TermResPrefix fun c x kc _ C _ _ => R c x kc C := by
  intro X
  obtain ⟨Λ₁, hΛ₁, H₁⟩ := h X
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV => ?_⟩
  obtain ⟨kc₁, K₁⟩ := H₁ A hΛ hV
  refine ⟨kc₁, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, S⟩ := K₁ kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hsX hsZ Kout hK => ?_⟩
  obtain ⟨Kn, N⟩ := S sXT sZT hsX hsZ Kout hK
  refine ⟨Kn, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₁, cg, Cg, hcg, CH, Υ, hCH, hΥ, T⟩ := N Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO
    hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce
    cker hcP Cfl
  obtain ⟨C₂, hC₂⟩ := hmap X A kc (max C₁ 0) (le_trans hΛ₁ hΛ) hV (le_max_right _ _)
  refine ⟨C₂, cg, Cg, hcg, CH, Υ, hCH, hΥ, ?_⟩
  intro C hC j₀ hj₀
  obtain ⟨M₁, U⟩ := T (max C₁ 0) (le_max_left _ _) j₀ hj₀
  exact ⟨M₁, fun M hM c x => hC₂ hKO c x (U M hM c x) C hC⟩

end AVRegularity.Construction.Residual.Presentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.ForcedEnergy AVRegularity.Construction.Preservation.Buffer
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The defect step at a context, from the generic defect flux bound

`fineDefectAt_of`: `FineDefectAt c x C` from the generic `FDData.timeBound`, with the level facts
(`ρ_⋆ = r_*`, `L_f + 1 ≤ 2 n_W`, `r_w ≤ r_*`, the small `θ_K`, the order `k₀ ≤ K_s`) and the two
named premises `0 ≤ C_χ`, `0 < kW.cker j` (j + 2 ≤ D_t) as hypotheses. The coefficient part is the
stage invariant through `reserveKernelOperator` restricted to `[t_p, a + T₀]`; the kernel part is
`kernelDefect` through `FDData`. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The price constant of the defect step: `∑_{m ≤ D_t - 2} C₀ ((k₀+L_f+m)!/k₀!)/c_m`. -/
def fineMconst (A : TermArgs X) (_nW : ℕ+) (kW : InvConsts) : ℝ :=
  ∑ m ∈ Finset.range (A.Dt - 1),
    Construction.KernelDefect.kdUniformMomentConst A.φ₀ A.LfT (max kW.Γk 0) *
      (((A.k₀ + (A.LfT + m)).factorial : ℝ) / A.k₀.factorial) / kW.cker m

theorem kernelOf_weak (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (v u : CompIn c.Gw.comps) (γ : c.Gw.fam.Γ v u) :
    c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ =
      isoPairedKernel (c.D.termRW A.σw M) nW := by
  unfold GenStage.kernelOf
  split <;> rfl

/-- The coefficient operator of the weak stage on `[t_p, a + T₀]` at the radius `r_*`. -/
def fineOp (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)
    (hI : IsStageInvariant c.lawW c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (M + A.Jw) kW
      c.aM (c.a + A.T₀) (Cχ * c.D.eps M ^ A.χw) (Cχ * c.D.eps M ^ A.χw) c.Gw)
    (hres0 : ∀ v : CompIn c.Gw.comps, 0 ≤ compReserve kW v.1)
    (hq : 1 < c.D.q) (hΛ : 128 ≤ c.D.Λ) (hi : 1 ≤ c.Gw.level) (hj : j₀ ≤ c.Gw.level)
    (hbw : 0 < A.bw) (hε1 : 0 < c.D.eps (c.Gw.level - 1)) (hκ : 0 < c.D.kap c.Gw.level)
    (hRpos : 0 < c.D.termRStar cK M) (hRε : c.D.termRStar cK M ≤ c.D.eps (c.Gw.level - 1))
    (hD2 : 2 ≤ A.Dt) (hθ : Cχ * c.D.eps M ^ A.χw ≤ 1 / 8) (hKs : A.k₀ ≤ kW.Ks)
    (hsch : SchurBound (Cχ * c.D.eps M ^ A.χw)
      (kernelSchurMatrix (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
        (Γ := c.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (c.D.kap c.Gw.level)
        (c.D.termRStar cK M) (fun v => c.Gw.mass c.lawW v / (fun _ => (1 : ℝ)) v ^ 2) A.k₀ A.Dt
        c.aM (c.a + A.T₀) kW.cker
        (fun v u γ => (c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun v u γ d => c.Gw.physCoeff v u γ d.1)))
    (haMtp : c.aM ≤ c.tp) (htp : c.tp ≤ c.a + A.T₀) :
    KernelEnergy.TorusKernelOperator c.tp (c.a + A.T₀) (c.D.termRStar cK M) (c.D.kap c.Gw.level)
      A.k₀ A.Dt (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (Γ := c.Gw.fam.Γ)
      (G := fun _ u _ => ScalarH u.1.root) :=
  kernelOperator_time_restrict
    (reserveKernelOperator c.lawW c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (M + A.Jw) kW
      c.aM (c.a + A.T₀) (Cχ * c.D.eps M ^ A.χw) (Cχ * c.D.eps M ^ A.χw) c.Gw hI hres0 hq hΛ hi hj
      hbw hε1 (haMtp.trans htp) hκ (c.D.termRStar cK M) hRpos hRε hD2 hθ A.k₀ hKs hsch)
    (Set.Icc_subset_Icc haMtp le_rfl) htp

/-- The defect data of the weak stage. -/
def fineFD (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M) (hValid : A.Valid) (heps : 0 < c.D.eps M) (hRpos : 0 < c.D.termRStar cK M)
    (hD2 : 2 ≤ A.Dt) (hLf : A.LfT + 1 ≤ 2 * (nW : ℕ))
    (hq1 : c.D.termRW A.σw M ≤ c.D.termRStar cK M)
    (hker : ∀ v u (γ : c.Gw.fam.Γ v u),
      (c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ).IsAdmissible kW.Γk kW.Lker)
    (R2 : KernelEnergy.TorusKernelOperator c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (c.D.kap c.Gw.level) A.k₀ A.Dt (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      (Γ := c.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root)) :
    FDData (CompIn c.Gw.comps) (fun v => ScalarH v.1.root) c.Gw.fam.Γ :=
  have hd := hValid.2.1.1
  have hnn := hValid.2.1.2.1
  have hm := hValid.2.1.2.2.1
  have hs := hValid.2.1.2.2.2
  have hrW : 0 < c.D.termRW A.σw M := by unfold OCData.termRW; positivity
  { φ₀ := A.φ₀, hφ := A.hφ₀, hd := hd, hnonneg := hnn, hmass := hm, hsupp := hs,
    t₀ := c.tp, t₁ := c.a + A.T₀, ρ := c.D.termRStar cK M, hρ := hRpos, k := A.k₀, D := A.Dt,
    hD := hD2, L := A.LfT, Γk := max kW.Γk 0, hΓk := le_max_right _ _,
    q := c.D.termRW A.σw M / c.D.termRStar cK M, hq0 := by positivity,
    hq1 := (div_le_one hRpos).2 hq1,
    B := R2.B, hB_meas := R2.hB_meas, hB_smooth := R2.hB_smooth, hB_per := R2.hB_per,
    hB_fin := R2.hB_fin,
    Kern := fun v u γ => c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ,
    hadm := fun v u γ => by
      have h0 := hker v u γ
      rw [kernelOf_weak] at h0
      show (c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ).IsAdmissible _ _
      rw [kernelOf_weak]
      obtain ⟨h1, h2, h3, -⟩ := h0
      exact ⟨h1, h2, fun t => ⟨(h3 t).1.trans (le_max_left _ _),
        (h3 t).2.1.trans (le_max_left _ _), (h3 t).2.2.1,
        (h3 t).2.2.2.trans (le_max_left _ _)⟩, hLf⟩,
    hwpos := fun v u γ => by rw [kernelOf_weak]; exact hrW,
    hwq := fun v u γ => by
      rw [kernelOf_weak]
      exact le_of_eq (div_mul_cancel₀ _ hRpos.ne').symm }

theorem fine_classicalRep (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW
    cP CP cHP Cw Ce cker j₀ M)
    (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (hreal : FineLiftRealization c Û) (v : CompIn c.Gw.comps) (t : ℝ)
    (ht : t ∈ Set.Icc c.tp (c.a + A.T₀)) :
    IsClassicalRep (Û v t)
      (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
      (fineOrder (A := A) + 1) := by
  obtain ⟨-, hjet, hreg⟩ := hreal
  obtain ⟨hC, hp⟩ := hreg v t ht
  exact Construction.Preservation.FullLift.classicalRep_of_value_ae (Û v t) _ _
    (CycleComparison.Reconstruction.periodicHk_isClassicalRep _ hC hp le_rfl) (hjet v t ht)

/-- **The defect step at a context** (named premises as hypotheses). -/
theorem fineDefectAt_of (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW
    cP CP cHP Cw Ce cker j₀ M) (x : TermResAux c) (C : ℝ) (hValid : A.Valid)
    (hq : 1 < c.D.q) (hΛ : 128 ≤ c.D.Λ) (hM1 : 1 ≤ M) (hMj : j₀ ≤ M) (hbw : 0 < A.bw)
    (hε1 : 0 < c.D.eps (M - 1)) (hκ : 0 < c.D.κ M) (hkap : c.D.kap c.Gw.level = c.D.κ M)
    (heps : 0 < c.D.eps M) (hRε : c.D.termRStar cK M ≤ c.D.eps (M - 1))
    (hrho : c.D.termRStar cK M = rhoStar c.D kW.c₀ c.Gw.level)
    (hθ : Cχ * c.D.eps M ^ A.χw ≤ 1 / 8) (hKs : A.k₀ ≤ kW.Ks)
    (hLf : A.LfT + 1 ≤ 2 * (nW : ℕ)) (hq1 : c.D.termRW A.σw M ≤ c.D.termRStar cK M)
    (hRpos : 0 < c.D.termRStar cK M)
    (hcpos : ∀ m, m + 2 ≤ A.Dt → 0 < kW.cker m)
    (hres0 : ∀ v : CompIn c.Gw.comps, 0 ≤ compReserve kW v.1)
    (haMtp : c.aM ≤ c.tp) (htp : c.tp ≤ c.a + A.T₀) (hC : fineMconst A nW kW ≤ C) :
    FineDefectAt c x C := by
  intro Û E hreal hen
  obtain ⟨-, haMb, hlev, -, hbirth, -, -, -, -, hI⟩ := c.weak
  have hD2 : 2 ≤ A.Dt := le_max_left _ _
  have hI' := hI
  rcases hI' with ⟨_, _, _, _, _, _, _, _, hkernel, hschur, _⟩
  have hker : ∀ v u (γ : c.Gw.fam.Γ v u),
      (c.Gw.kernelOf c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) v u γ).IsAdmissible kW.Γk kW.Lker :=
    fun v u γ => (hkernel v u γ).1
  have hschR := hschur A.k₀ hKs (fun _ => 1) (Or.inl rfl)
  rw [← hrho] at hschR
  set R2 := fineOp c hI hres0 hq hΛ (by rw [hlev]; exact hM1) (by rw [hlev]; exact hMj) hbw
    (by rw [hlev]; exact hε1) (by rw [hkap]; exact hκ) hRpos (by rw [hlev]; exact hRε) hD2 hθ hKs
    hschR haMtp htp with hR2
  have hπ : R2.π = c.Gw.mass c.lawW := by
    funext v
    show c.Gw.mass c.lawW v / (fun _ => (1 : ℝ)) v ^ 2 = _
    simp
  set P := fineFD c hValid heps hRpos hD2 hLf hq1 hker R2 with hP
  have hK : P.OrderOK (fineOrder (A := A)) := by
    show A.k₀ + (A.Dt - 2) + A.LfT ≤ fineOrder (A := A)
    unfold fineOrder; omega
  set θ' := |Cχ| * c.D.eps M ^ A.χw with hθ'
  have hθ'0 : 0 ≤ θ' := by positivity
  have hschur : SchurBound θ' (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root)
      (c.D.kap c.Gw.level) P.ρ (c.Gw.mass c.lawW) P.k P.D P.t₀ P.t₁ kW.cker
      (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root)) P.B) := by
    have h0 : SchurBound (Cχ * c.D.eps M ^ A.χw) (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root)
      (c.D.kap c.Gw.level) P.ρ R2.π P.k P.D P.t₀ P.t₁ kW.cker
      (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root)) P.B) := R2.hschur
    rw [hπ] at h0
    have hle : Cχ * c.D.eps M ^ A.χw ≤ θ' := by
      rw [hθ']
      exact mul_le_mul_of_nonneg_right (le_abs_self Cχ) (by positivity)
    exact ⟨fun i => (h0.1 i).trans hle, fun j => (h0.2 j).trans hle⟩
  have hmassPos : ∀ v : CompIn c.Gw.comps, 0 < c.Gw.mass c.lawW v := fun v =>
    birth_compMass_pos hq hΛ c.lawW v.1
  obtain ⟨Fk, hFr, hFm, hFb⟩ := P.timeBound htp (c.Gw.mass c.lawW) hmassPos (c.D.kap c.Gw.level)
    (by rw [hkap]; exact hκ) kW.cker hcpos θ' hθ'0 hschur hK Û
    (fun j t x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x j)
    (fun j t ht => fine_classicalRep c Û hreal j t ht)
    (fun j => (hreal.1 j).aestronglyMeasurable) hen.1
  refine ⟨Fk, ?_, hFm, ?_⟩
  · intro v t ht
    exact (hFr v t ht).trans (Filter.Eventually.of_forall fun x => rfl)
  · rw [hkap] at hFb
    have hE := hen.2
    have hMc : 0 ≤ P.Mconst kW.cker := P.Mconst_nonneg hcpos
    have hqL : 0 ≤ P.q ^ P.L := pow_nonneg P.hq0 _
    have hC0 : 0 ≤ C := hMc.trans hC
    refine hFb.trans ?_
    have hs0 : Real.sqrt (c.D.κ M * ∫ s in Set.Icc c.tp (c.a + A.T₀),
        massGradNormSq (E := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
          (K := fun _ => fineOrder (A := A)) (c.D.termRStar cK M) (c.Gw.mass c.lawW)
          (fun v => (Û v s).val)) ≤ E := hE
    have hC' : P.Mconst kW.cker ≤ C := hC
    calc P.q ^ P.L * P.Mconst kW.cker * θ' * _ ≤ P.q ^ P.L * C * θ' * E :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC' hqL |> fun h => mul_le_mul h le_rfl hθ'0
            (mul_nonneg hqL hC0)) hs0 (Real.sqrt_nonneg _)
            (mul_nonneg (mul_nonneg hqL hC0) hθ'0)
      _ = _ := by
          change (c.D.termRW A.σw M / c.D.termRStar cK M) ^ A.LfT * C * θ' * E = _
          ring

/-- An empty window: the defect step is trivial. -/
theorem fineDefectAt_empty (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid
    kW cP CP cHP Cw Ce cker j₀ M) (x : TermResAux c) (C : ℝ) (hC0 : 0 ≤ C)
    (heps : 0 < c.D.eps M) (hcK : 0 < cK)
    (htp : ¬ c.tp ≤ c.a + A.T₀) : FineDefectAt c x C := by
  intro Û E hreal hen
  have hE : 0 ≤ E := (Real.sqrt_nonneg _).trans hen.2
  have hemp : Set.Icc c.tp (c.a + A.T₀) = ∅ := Set.Icc_eq_empty htp
  refine ⟨fun v t => 0, fun v t ht => ?_, fun v => ?_, ?_⟩
  · rw [hemp] at ht; exact absurd ht (Set.notMem_empty t)
  · rw [hemp]; simp [Measure.restrict_empty]
  · rw [hemp]
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, Real.sqrt_zero]
    have hr : 0 ≤ c.D.termRW A.σw M / c.D.termRStar cK M := by
      unfold OCData.termRW OCData.termRStar; positivity
    positivity

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
@[expose] public noncomputable section

section
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The scale facts of the filter defect (`FilterScaleStatement`).**

At late terminal levels `M`, the weak kernel width `r_w = ε_M^{1+σ_w}` and the fresh width
`r_new = ρ ε_{M-1}^{t_T}` are at most the radius `ρ`.

* `r_new ≤ ρ` since `ε_{M-1} ≤ 1` and `t_T ≥ 0`;
* `r_w ≤ ε_M ≤ 2 ε_{M-1}^q ≤ C⁻¹ ε_{M-1}^{1+c} ≤ ρ`, where `terminal_scales_core` gives
  `C⁻¹ ε_{M-1}^{c} ≤ ρ/ε_{M-1}` and `c = ocC < q - 1`.

Special cases: `σ_w = 0`, `t_T = 0`: the widths are `ε_M` and `ρ`. -/

/-- The exponent `ocC` is below `q - 1` in the admissible range. -/
theorem ocC_lt {α q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hq : 1 < q) :
    ocC α q < q - 1 := by
  have hq1 : 0 < q + 1 := by linarith
  have hg : ocGamma α q ≤ 2 / 3 * (q - 1) := by
    unfold ocGamma
    rw [div_le_iff₀ hq1]
    nlinarith
  have hd : ocDelta α q ≤ (q - 1) / 4 := by
    unfold ocDelta
    have h0 : 0 ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
    nlinarith
  unfold ocC
  linarith

/-- The abstract comparison: `2 E^q ≤ C⁻¹ E^c E` from `E^{q-1-c} ≤ (2C)⁻¹`. -/
theorem scale_alg {E C c q : ℝ} (hE : 0 < E)
    (hs : E ^ (q - 1 - c) ≤ (2 * C)⁻¹) : 2 * E ^ q ≤ C⁻¹ * E ^ c * E := by
  have h1 : E ^ (q - 1 - c) * E ^ c = E ^ (q - 1) := by
    rw [← Real.rpow_add hE]; ring_nf
  have h2 : E ^ q = E ^ (q - 1) * E := by
    rw [Real.rpow_sub_one hE.ne', div_mul_cancel₀ _ hE.ne']
  have h3 : 0 ≤ E ^ c * E := by positivity
  have h4 : E ^ (q - 1 - c) * (E ^ c * E) ≤ (2 * C)⁻¹ * (E ^ c * E) :=
    mul_le_mul_of_nonneg_right hs h3
  have h5 : (2 * C)⁻¹ = C⁻¹ / 2 := by rw [mul_inv]; ring
  calc 2 * E ^ q = 2 * (E ^ (q - 1 - c) * (E ^ c * E)) := by rw [h2, ← h1]; ring
    _ ≤ 2 * ((2 * C)⁻¹ * (E ^ c * E)) := by linarith
    _ = C⁻¹ * E ^ c * E := by rw [h5]; ring

/-- **The scale facts at late levels.** -/
theorem scale_core (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (cr σw tT : ℝ), 0 < cr → 0 ≤ σw → 0 ≤ tT →
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, D.α = X.α → D.q = X.q → D.Λ = Λ →
      IsOCBandChain X.α X.q Λ X.ζ M D.κ →
      D.termRW σw M ≤ D.termRho cr M ∧ D.termRNew cr tT M ≤ D.termRho cr M := by
  obtain ⟨ΛT, hΛT, hT⟩ := EntryScales.terminal_scales_core X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨ΛT, hΛT, fun Λ hΛ cr σw tT hcr hσ htT => ?_⟩
  have h128 : 128 ≤ Λ := hΛT.trans hΛ
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨C, M₁, hC1, hsc⟩ := hT Λ hΛ cr hcr
  have hC : 0 < C := by linarith
  have hp : 0 < X.q - 1 - ocC X.α X.q := sub_pos.2 (ocC_lt X.hα₀ X.hα₁ hq1)
  obtain ⟨Ma, hMa⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp
    (c := (2 * C)⁻¹) (by positivity)
  refine ⟨max (max 2 M₁) (Ma + 1), le_trans (le_max_left _ _) (le_max_left _ _),
    fun M hM D hDα hDq hDΛ hband => ?_⟩
  have hM2 : 2 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM₁ : M₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMa' : Ma ≤ M - 1 := by
    have := le_trans (le_max_right _ _) hM
    omega
  obtain ⟨-, -, -, hlow, -⟩ := hsc M hM₁ D.κ hband
  simp only [OCData.termRW, OCData.termRho, OCData.termRNew, OCData.termB, OCData.termH,
    OCData.eps, hDα, hDq, hDΛ]
  obtain ⟨hε, hε1, -⟩ := Scales.epsilon_basic (m := M) hq1 h128
  obtain ⟨hE, hE1, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 h128
  have hρ0 : 0 ≤ cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) :=
    mul_nonneg hcr.le (Real.sqrt_nonneg _)
  refine ⟨?_, ?_⟩
  · have h1 : ocEpsilon X.q Λ M ^ (1 + σw) ≤ ocEpsilon X.q Λ M := by
      calc ocEpsilon X.q Λ M ^ (1 + σw) ≤ ocEpsilon X.q Λ M ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
        _ = _ := Real.rpow_one _
    have h2 := Scales.epsilon_q_step hq1 X.hq.2.1 h128 (by omega : 1 ≤ M)
    have h3 := scale_alg hE (hMa (M - 1) hMa')
    have h4 : C⁻¹ * ocEpsilon X.q Λ (M - 1) ^ ocC X.α X.q * ocEpsilon X.q Λ (M - 1) ≤
        cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) := by
      have := (le_div_iff₀ hE).1 hlow
      exact this
    linarith
  · calc cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) * ocEpsilon X.q Λ (M - 1) ^ tT
        ≤ cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hE.le hE1 htT) hρ0
      _ = _ := mul_one _

/-- **(SC), `FilterScaleStatement`.** -/
theorem filterScale : FilterScaleStatement := by
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := scale_core X
  refine ⟨Λc, hΛc, fun A hΛ hV => ?_⟩
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, -, -, -⟩, -, hsch, -⟩ := hV
  have htT : 0 ≤ A.tT := hsch.2.2.2.2.2.2.2.2.1.le
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _
    _ _ _ hko hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩⟩
  obtain ⟨M₀, -, hM₀⟩ := hcore A.Λ hΛ cr A.σw A.tT hcr0 hσw.le htT
  refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨M₀, fun M hM c x => ?_⟩⟩
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  exact hM₀ M hM c.D hDα hDq hDΛ hband

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The defect step of the fine matrix tail with the prefix of `entry_terminal_residual`**.

`termFineDefect_of_cker`: `TermFineDefectStatement` from `TermCkerStatement`, the positivity of the
weak kernel constants `0 < kW.cker m` (`m + 2 ≤ D_t`, `M` large) for a weak stage **with an edge**
(`TermCkerStatement`). At a context it splits three ways:
- `t_p > a + T₀`: the empty window (`fineDefectAt_empty`);
- no edge in the weak family: the defect flux is an empty sum, realized by `0`
  (`fineDefectAt_noEdge`). Here `kW.cker` is unconstrained (the stage invariant's regularizer clause
  is about edges), so positivity is not available and not needed;
- otherwise `fineDefectAt_of`, with the level facts of `terminalForcedEnergy_of_reserve`
  (`term_level_floor`, `term_scale_facts` at `c_d = 0`), `ε^{σ_w} ≤ c_K` for `r_w ≤ r_*`, `K_need = k₀`,
  `a_M ≤ t_p` from the preparation (`0 < c_P`) and the reserve (`x.reserve`).
The constant is `C₀ = max 0 (fineMconst A n_W kW)`.

Special cases:
- An empty weak family: no edge; the bound is `0 ≤ Y`.
- `t_p = a + T₀`: a one-point window, the third case.
- `D_t = 2`: `fineMconst` is a sum over `range 1`. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **Positivity of the weak kernel constants**: for a weak stage with an edge, the weak kernel constants are positive at the
orders of the defect, for `M` large. -/
def TermCkerStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (nW : ℕ+) (CL Cχ : ℝ) (kW : InvConsts) (j₀ : ℕ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
    (∃ v u, Nonempty (Gw.fam.Γ v u)) → ∀ m, m + 2 ≤ A.Dt → 0 < kW.cker m

/-- **No edge**: the defect flux is an empty sum, realized by `0`. -/
theorem fineDefectAt_noEdge (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread
    Cid kW cP CP cHP Cw Ce cker j₀ M) (x : TermResAux c) (C : ℝ) (hC0 : 0 ≤ C)
    (hnone : ∀ v u, IsEmpty (c.Gw.fam.Γ v u)) (heps : 0 < c.D.eps M) (hcK : 0 < cK) :
    FineDefectAt c x C := by
  intro Û E _ hen
  have hE : 0 ≤ E := (Real.sqrt_nonneg _).trans hen.2
  have hr : 0 ≤ c.D.termRW A.σw M / c.D.termRStar cK M := by
    unfold OCData.termRW OCData.termRStar; positivity
  refine hasFluxBound_of_zero _ _ _ _ _ _ (fun v t _ => ?_) (by positivity)
  funext y
  simp only [Pi.zero_apply, fineFluxF, coeffFluxOn]
  refine Finset.sum_eq_zero fun u _ => ?_
  have := hnone v u
  simp

/-- **The defect step with the prefix of `entry_terminal_residual`**, from the positivity of the weak kernel constants. -/
theorem termFineDefect_of_cker (hck : TermCkerStatement) : TermFineDefectStatement := by
  intro X
  obtain ⟨Λc, -, hck⟩ := hck X
  refine ⟨max 128 Λc, le_max_left _ _, fun A hΛ hV => ?_⟩
  have h128 : 128 ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hq1 : 1 < X.q := X.hq.1
  have hV' := hV
  obtain ⟨-, -, ⟨hbw, -⟩, ⟨-, -, -, -, hσw, -, hχw, -, -⟩, -⟩ := hV'
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨A.k₀, fun Kw Lt nW hk₀w _ cr kS _
    _ _ _ hko _ _ _ _ _ hKs _ _ _ cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP
    Cfl => ?_⟩⟩⟩
  refine ⟨max 0 (fineMconst A nW kW), 1, 0, one_pos, 1, 1, le_rfl, one_pos,
    fun C hC j₀ _ => ?_⟩
  have hC0 : 0 ≤ C := le_trans (le_max_left _ _) hC
  have hCm : fineMconst A nW kW ≤ C := le_trans (le_max_right _ _) hC
  have hKs' : A.k₀ ≤ kW.Ks := le_trans hKs hall.1
  have hLf : A.LfT + 1 ≤ 2 * (nW : ℕ) := by
    have h1 := hko.1
    have h2 : A.LfT ≤ max A.LpT (max A.LoT A.LfT) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  obtain ⟨M₁, hM₁2, hfl⟩ := ForcedEnergy.term_level_floor X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq h128 cK Cχ
    A.χw 0 hcK hχw le_rfl
  obtain ⟨M₂, h2⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hσw hcK
  obtain ⟨M₃, h3⟩ := hck A (le_trans (le_max_right _ _) hΛ) hV nW CL Cχ kW j₀
  refine ⟨max (max M₁ M₂) (max M₃ j₀), fun M hM c x => ?_⟩
  have hM1 : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM2 : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM3 : M₃ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMj : j₀ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hM2' : 2 ≤ M := le_trans hM₁2 hM1
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, hterm⟩ := c.data
  obtain ⟨hθle, hcKε, hγ2, hγCd⟩ := hfl M hM1
  have hεD : c.D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hεD1 : c.D.eps (M - 1) = ocEpsilon X.q A.Λ (M - 1) := by
    simp only [OCData.eps, hDq, hDΛ]
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hkap : c.D.kap c.Gw.level = c.D.κ M := by simp [OCData.kap, hlev, hterm]
  obtain ⟨hεpos, hκpos, hεa, -⟩ := ForcedEnergy.term_scale_facts M hq1 h128 hband.1 0 0 le_rfl
    le_rfl (by norm_num) hγ2 hγCd
  have hapos : 0 < ocA X.α X.q A.Λ M := Real.rpow_pos_of_pos hεpos _
  have hmin : min (c.D.eps M) (Real.sqrt (c.D.κ M / ocA c.D.α c.D.q c.D.Λ M)) =
      ocEpsilon X.q A.Λ M := by
    rw [hεD, hDα, hDq, hDΛ]
    refine min_eq_left ((Real.le_sqrt' hεpos).2 ?_)
    rw [le_div_iff₀ hapos]
    exact hεa
  have hRdef : c.D.termRStar cK M = cK * ocEpsilon X.q A.Λ M := by
    rw [OCData.termRStar, hεD]
  have hrho : c.D.termRStar cK M = rhoStar c.D kW.c₀ c.Gw.level := by
    rw [hRdef, hlev, hkW]
    unfold rhoStar
    rw [hmin]
  have hE1 : 0 < ocEpsilon X.q A.Λ (M - 1) := (Scales.epsilon_basic (m := M - 1) hq1 h128).1
  have hε1 : 0 < c.D.eps (M - 1) := by rw [hεD1]; exact hE1
  have heps : 0 < c.D.eps M := by rw [hεD]; exact hεpos
  have hRε : c.D.termRStar cK M ≤ c.D.eps (M - 1) := by rw [hRdef, hεD1]; exact hcKε
  have hθ : Cχ * c.D.eps M ^ A.χw ≤ 1 / 8 := by rw [hεD]; exact hθle
  have hRpos : 0 < c.D.termRStar cK M := by rw [hRdef]; exact mul_pos hcK hεpos
  have hrw : c.D.termRW A.σw M ≤ c.D.termRStar cK M := by
    have hs := h2 M hM2
    unfold OCData.termRW
    rw [hRdef, hεD, Real.rpow_add hεpos, Real.rpow_one, mul_comm cK]
    exact mul_le_mul_of_nonneg_left hs hεpos.le
  have hres0 : ∀ v : CompIn c.Gw.comps, 0 ≤ compReserve kW v.1 := by
    intro v
    unfold compReserve compGrade
    rw [c.weak.2.2.2.2.1 v]
    simp only [List.length_nil, add_zero]
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast x.reserve
  have haMtp : c.aM ≤ c.tp := by
    have h1 := c.prep.2.1
    have hH : 0 < c.D.termH M :=
      Construction.Stream.ocTauPP_pos (le_trans (by norm_num) (hDΛ ▸ h128))
    nlinarith [mul_pos hcP hH]
  by_cases htp : c.tp ≤ c.a + A.T₀
  · by_cases hedge : ∃ v u, Nonempty (c.Gw.fam.Γ v u)
    · exact fineDefectAt_of c x C hV (hDq ▸ hq1) (hDΛ ▸ h128) (by omega) hMj hbw hε1 hκpos hkap
        heps hRε hrho hθ hKs' hLf hrw hRpos
        (h3 M hM3 c.D c.data c.a c.lawW c.PW c.Gw c.aM c.weak hedge) hres0 haMtp htp hCm
    · exact fineDefectAt_noEdge c x C hC0
        (fun v u => not_nonempty_iff.1 fun h => hedge ⟨v, u, h⟩) heps hcK
  · exact fineDefectAt_empty c x C hC0 heps hcK htp

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Residual.Presentation

/-! Exact mean-flux coefficient action for finite regularity inputs. At each slow point,
replace the coarse input by its smooth Taylor jet, invoke the smooth flux identity, and
transfer back using the finite-jet locality of liftFluxX. No global smoothing or
limiting argument changes the supplied lift sequence or its actual flux.

Special cases: a polynomial input may serve as its own replacement; constants give zero
positive tested-order action; both the diagonal degree-two metric and the inherited source
convolution are retained. The required field order is D+N, independent of the cell degree. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
private theorem covTruncCellMean_apply_input_jet (c : LiftCoeff ι h) (n R : ℕ) (hnR : n ≤ R)
    (f g : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (hj : SameJetAt R X f g) :
    liftApply n c (fun _ => f) t X z = liftApply n c (fun _ => g) t X z := by
  ext v
  unfold liftApply
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have hmR : m ≤ R := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)).trans hnR
  rw [congrFun (hj m α hmR) u]

include P in
omit [DecidableEq ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- The actual cell mean depends only on the finite slow jet of the input. -/
theorem covTruncCellMean_input_jet (sX sZ : ℕ) (hsX : D ≤ sX) (hsZ : D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (f g : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ ((D + N : ℕ) : ℕ∞) f) (hg : ContDiff ℝ ((D + N : ℕ) : ℕ∞) g)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (j : Fin 2)
    (hj : SameJetAt (D + N) X f g) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => g) hh n t X z j) := by
  have hv : Continuous (Q.v t) := by
    have he : Q.v t = fun z => V t (z par.rev) • basisVec par := funext (P.v_shear t)
    rw [he]
    exact ((P.V_smooth t ht).continuous.comp (continuous_apply _)).smul continuous_const
  have hl := liftFlux_sameJet (ι := ι) (h := h) Q Cc (fun _ => f) (fun _ => g)
    hh n t j 0 N H X (by have := P.D_ge; omega) hhh hseq.2.2.1
    (fun r hr n' m α v u => (hseq.2.2.2.2.2.1 r hr n' m α v u t ht).1.mono
      (by simpa using hsX) (by simpa using hsZ))
    (fun l => (P.G_smooth t ht j l).of_le (by simp))
    (contDiff_zero.mpr ((continuous_apply j).comp hv))
    (fun _ v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono
      (Nat.zero_le _) (Nat.zero_le _))
    (by simpa only [zero_add] using hf) (by simpa only [zero_add] using hg)
    (by simpa only [zero_add] using hj)
  have he : (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) =
      fun z => liftFluxX Q Cc (fun _ => g) hh n t X z j := by
    funext z
    simpa only [orderedDerivative_zero] using hl z 0 (fun i => Fin.elim0 i) le_rfl
  rw [he]

include P in
/-- Both actual mean coefficient actions at finite input regularity. -/
theorem covTruncCellMean_finite (sX sZ : ℕ) (hsX : max 2 D ≤ sX) (hsZ : max 2 D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hh n : ℕ) (hhh : hh ≤ H)
    (hn : 2 ≤ n) (hnR : n ≤ N + D) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ ((D + N : ℕ) : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X : Vec 2) (j : Fin 2) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) =
      liftApply (n - 1)
        (if hh = 0 then diagonalMeanFluxCoefficient Q Cc n j else
          positiveMeanFluxCoefficient Q Cc hh n j) (fun _ => f) t X 0 := by
  obtain ⟨T, hT, hj⟩ := smoothJetRealization (D + N) f hf X
  have hfT : SameJetAt (D + N) X f T := fun r α hr => (hj r α hr).symm
  have hmean := covTruncCellMean_input_jet P sX sZ
    ((le_max_right _ _).trans hsX) ((le_max_right _ _).trans hsZ) Cc hseq hh n hhh f T hf
    (hT.of_le (by simp)) t ht X j hfT
  rw [hmean]
  have hact : fieldCellMean (fun z => liftFluxX Q Cc (fun _ => T) hh n t X z j) =
      liftApply (n - 1)
        (if hh = 0 then diagonalMeanFluxCoefficient Q Cc n j else
          positiveMeanFluxCoefficient Q Cc hh n j) (fun _ => T) t X 0 := by
    by_cases hh0 : hh = 0
    · subst hh
      rw [ite_eq_left rfl]
      exact covTruncCellMean_diagonal P sX sZ ((le_max_left _ _).trans hsX)
        ((le_max_left _ _).trans hsZ) Cc hseq n hn T hT t ht X j
    · rw [ite_eq_right hh0]
      exact covTruncCellMean_positive P sX sZ ((le_max_left _ _).trans hsX)
        ((le_max_left _ _).trans hsZ) Cc hseq P₀ hreserve hh n (by omega) hhh hn hnR T hT
        t ht X j
  rw [hact]
  exact covTruncCellMean_apply_input_jet _ (n - 1) (D + N) (by omega) T f t X 0 hj

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse AVRegularity.EntryTerminal.CovOp
namespace AVRegularity.Construction.Residual.Presentation

/-! The existing covariance adjoint calculus supplies the polynomial factor of the exact
terminal mean-flux operator. The normalized bound depends on the orders and a bound on
H/rho^2, and is independent of the components and datum. No coefficient polynomial is
expanded anew. Special cases: p=0 gives the identity; H=0 gives the identity; empty windows
are extended by zero. The polynomial is applied before the physical mean coefficients. -/

local instance covGradTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance covGradTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance covGradTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

section Family
variable {Kin K : ℕ} {I : Set ℝ}
  (L : ∀ v : ι, I → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)) →L[ℝ]
    TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)))

def covTruncCovFamilyOp : ℝ →
    ((∀ v, TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v))) →L[ℝ]
      (∀ v, TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)))) := fun t =>
  open Classical in
  if ht : t ∈ I then ContinuousLinearMap.pi fun v =>
    (L v ⟨t, ht⟩).comp (ContinuousLinearMap.proj v) else 0

omit [Fintype ι] in
theorem covTruncCovFamilyOp_apply (t : ℝ) (ht : t ∈ I) U v :
    covTruncCovFamilyOp L t U v = L v ⟨t, ht⟩ (U v) := by
  simp only [covTruncCovFamilyOp, dite_eq_left ht, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem covTruncCovFamilyOp_norm (Cn : ℝ) (hCn : 0 ≤ Cn)
    (hn : ∀ v s, ‖L v s‖ ≤ Cn) (t : ℝ) (ht : t ∈ I) :
    ‖covTruncCovFamilyOp L t‖ ≤ Cn := by
  refine ContinuousLinearMap.opNorm_le_bound _ hCn fun U => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCn (norm_nonneg U))).mpr fun v => ?_
  rw [covTruncCovFamilyOp_apply L t ht U v]
  exact ((L v ⟨t, ht⟩).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hn v ⟨t, ht⟩) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm U v) hCn))

omit [Fintype ι] in
theorem covTruncCovFamilyOp_meas (hI : MeasurableSet I) (hL : ∀ v, Continuous (L v))
    (U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)))
    (hU : ∀ v, AEStronglyMeasurable (U v) (volume.restrict I)) (v : ι) :
    AEStronglyMeasurable (fun t => covTruncCovFamilyOp L t (fun u => U u t) v)
      (volume.restrict I) := by
  classical
  have hm := covOp_aesm_apply (I := I) hI (L v) (hL v) (hU v)
  have he : (fun t => if ht : t ∈ I then L v ⟨t, ht⟩ (U v t) else 0) =
      fun t => covTruncCovFamilyOp L t (fun u => U u t) v := by
    funext t
    by_cases ht : t ∈ I
    · rw [dite_eq_left ht, covTruncCovFamilyOp_apply L t ht]
    · simp only [covTruncCovFamilyOp, dite_eq_right ht, zero_apply, Pi.zero_apply]
  rw [he] at hm
  exact hm

theorem covTruncCovFamilyOp_mass (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (Cb : ℝ)
    (hb : ∀ v s W, factorialNormSq ρ (L v s W).val ≤ Cb ^ 2 * factorialNormSq ρ W.val)
    (t : ℝ) (ht : t ∈ I) U :
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => K) ρ π
        (fun v => (covTruncCovFamilyOp L t U v).val) ≤ Cb ^ 2 *
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => Kin) ρ π
        (fun v => (U v).val) := by
  apply covOp_mass_pointwise ρ π hπ Cb _ U
  intro v
  rw [covTruncCovFamilyOp_apply L t ht U v]
  exact hb v ⟨t, ht⟩ (U v)
end Family

/-- Covariance polynomials have a measurable exact flux action with a normalized price. -/
def covTruncCovGradient_operator (K p : ℕ) (a b ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ContinuousOn Hc (Set.Icc a b))
    (hsize : ∀ t ∈ Set.Icc a b, covBound (Hc t) ≤ 4 * ρ ^ 2)
    (input : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hsmooth : ∀ v, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (input v t))
    (hper : ∀ v, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (input v t))
    (hcont : ∀ v, ∀ t ∈ Set.Icc a b, Continuous (covPolyP (Hc t) p (input v t))) :
    CovTruncFluxOperator (h := h) (K + 2 * p) K (Set.Icc a b) ρ π
      (covPolyConst (4 * ((K + 2 * p : ℕ) : ℝ) ^ 2) p) input
      (fun v t => covPolyP (Hc t) p (input v t)) := by
  classical
  let I := Set.Icc a b
  let A (v : ι) (s : I) := TorusAdj.covPolyP
    (E := PiLp 2 (fun _ : Fin 2 => h v)) (Hc s) (hsize s s.2) p K (K + 2 * p)
  let L (v : ι) (s : I) := (A v s).adj K le_rfl
  have hAc : ∀ v, AdjCont (A v) := fun v =>
    covOp_adjCont_covPolyP (E := PiLp 2 (fun _ : Fin 2 => h v))
      hH.domRestrict (fun s : I => hsize s s.2) p K (K + 2 * p)
  have hCn : 0 ≤ covPolyConst (4 * ρ ^ 2) p := by
    unfold covPolyConst
    exact Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l)
      (Nat.cast_nonneg _)
  have hFB : ∀ v s, (A v s).FBound ρ
      (covPolyConst (4 * ((K + 2 * p : ℕ) : ℝ) ^ 2) p) := by
    intro v s
    refine (TorusAdj.FBound.covPolyP hρ (Hc s) (hsize s s.2) p K (K + 2 * p)).mono_const ?_
    exact gfbCovPoly_mono (fbCovConst_nonneg hρ _ _)
      (gfbCovConst_le hρ _ _ (hsize s s.2)) p
  refine {
    op := covTruncCovFamilyOp L
    norm_bound := ⟨covPolyConst (4 * ρ ^ 2) p,
      covTruncCovFamilyOp_norm L _ hCn (fun v s => (A v s).bound K le_rfl)⟩
    measurable_apply := covTruncCovFamilyOp_meas L measurableSet_Icc (fun v => hAc v K le_rfl)
    weighted_bound := covTruncCovFamilyOp_mass L ρ π hπ _ ?_
    realizes := fun U hU v t ht => ?_ }
  · intro v s W
    exact covOp_sq_le_of_sqrt_le (factorialNormSq_nonneg _ _) (factorialNormSq_nonneg _ _)
      (hFB v s K le_rfl W)
  · change tval (covTruncCovFamilyOp L t (fun u => U u t) v) =ᵐ[_] _
    rw [covTruncCovFamilyOp_apply L t ht (fun u => U u t) v]
    refine covOp_adj_value (A v ⟨t, ht⟩) le_rfl (U v t) (hU v t ht) (hcont v t ht) ?_
    intro φ hφ hpφ
    exact (covOp_P_adjoint (Hc t) p (input v t) φ (hsmooth v t ht)
      (hφ.of_le (by exact_mod_cast (le_top : (2 * p : ℕ∞) ≤ ⊤))) (hper v t ht) hpφ).symm

section Context
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Input order of the physical mean operator after the covariance polynomial is applied. -/
def covTruncCovGradientOrder {X : TermConstruction} (A : TermArgs X) (kc : ℕ) : ℕ :=
  kc + 4 * A.pT + A.NT + A.Dt

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The actual gradient of P_p applied to the readout, before the physical mean operator. -/
def covTruncCovGradientInput (x : TermResAux c) (v : CompIn c.Gw.comps)
    (t : ℝ) (y : Vec 2) : PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root) :=
  toFluxL (gradE (fun z => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t z v) y)

/-- The covariance factor of the exact mean-flux operator, retaining the original gradient
as its input. This is a proved operator, not an additional analytic assumption. -/
def CovTruncCovGradientAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  Nonempty (CovTruncFluxOperator (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (covTruncMeanInputOrder A kc) (covTruncCovGradientOrder A kc)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.termRho cr M) (c.Gw.mass c.lawW) C
    (fun v t y => toFluxL (gradE (fun z => x.aZ t z v) y)) (covTruncCovGradientInput c x))

private def CovTruncCovFieldOrderAt (_x : TermResAux c) (kc : ℕ) : Prop :=
  covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout

/-- At a context, the size of the covariance primitive and the existing field floor supply the covariance factor. -/
theorem covTruncCovGradient_of_size (x : TermResAux c) (kc : ℕ) (C : ℝ)
    (hΛ : 128 ≤ A.Λ) (hs : CovTruncSizeAt c x kc C)
    (ho : covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout) :
    CovTruncCovGradientAt c x kc
      (covPolyConst (4 * ((covTruncMeanInputOrder A kc : ℕ) : ℝ) ^ 2) A.pT) := by
  have hΛD : 128 ≤ c.D.Λ := c.data.2.2.1 ▸ hΛ
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hH : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ c.D.Λ)
  have hcr : 0 < cr := lt_of_lt_of_eq one_pos x.one.symm
  have hρ : 0 < c.D.termRho cr M := mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hν hH))
  have hq : 1 < c.D.q := c.data.2.1 ▸ X.hq.1
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq hΛD c.lawW v.1
  have he : covTruncCovGradientOrder A kc + 2 * A.pT = covTruncMeanInputOrder A kc := by
    dsimp [covTruncCovGradientOrder, covTruncMeanInputOrder]; omega
  have hf : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((2 * A.pT + 1 : ℕ) : ℕ∞) (fun z => x.aZ t z v) := by
    intro v t ht
    have hfK : ContDiff ℝ ((A.Khat Kout - 2 : ℕ) : ℕ∞) (fun z => x.aZ t z v) := by
      exact_mod_cast (x.repZ v t ht).2.1
    have hbound : 2 * A.pT + 1 ≤ A.Khat Kout - 2 := by
      dsimp [covTruncMeanInputOrder] at ho
      omega
    exact hfK.of_le (by exact_mod_cast hbound)
  have hg : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((2 * A.pT : ℕ) : ℕ∞)
        (fun y => toFluxL (gradE (fun z => x.aZ t z v) y)) := by
    intro v t ht
    exact_mod_cast contDiff_gradField_nat (hf v t ht)
  let T := covTruncCovGradient_operator (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (covTruncCovGradientOrder A kc) A.pT c.tp (c.a + A.T₀) (c.D.termRho cr M) hρ
    (c.Gw.mass c.lawW) hπ (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    hs.2.2 (fun t ht => (hs.1 t ht).trans (by
      calc
        _ ≤ c.D.termRho cr M ^ 2 := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hs.2.1 (sq_nonneg (c.D.termRho cr M)))
        _ ≤ 4 * c.D.termRho cr M ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (by norm_num)))
    (fun v t y => toFluxL (gradE (fun z => x.aZ t z v) y)) hg
    (fun v t ht z y => by
      apply PiLp.ext
      intro j
      exact covTruncReg_gradE_periodic ((hf v t ht).differentiable (by simp))
        (x.repZ v t ht).2.2.1 j z y)
    (fun v t ht => (covOp_contDiff_P _ A.pT 0 (by simpa only [zero_add] using hg v t ht)).continuous)
  have htarget : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      covPolyP (menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) A.pT
        (fun y => toFluxL (gradE (fun z => x.aZ t z v) y)) = covTruncCovGradientInput c x v t := by
    intro v t ht
    funext y
    exact (covTruncGradient_covPolyP_finite _ A.pT (fun z => x.aZ t z v) (hf v t ht) y).symm
  rw [he] at T
  refine ⟨{ T with realizes := fun U hU v t ht => ?_ }⟩
  rw [← htarget v t ht]
  exact T.realizes U hU v t ht
end Context

private theorem covTruncCovGradient_field_order :
    TermResPrefix fun c x kc _ _ _ _ => CovTruncCovFieldOrderAt c x kc := by
  intro X
  refine ⟨128, le_rfl, fun A _ _ => ⟨0, fun kc _ => ⟨0, 0, covTruncMeanInputOrder A kc + 3,
    fun sXT sZT _ _ Kout hK => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨0, fun M _ c x => ?_⟩⟩
  exact hK.trans (le_max_left _ _)

/-- The covariance factor is available with the exact uniform residual prefix. -/
theorem covTruncCovGradient :
    TermResPrefix fun c x kc _ C _ _ => CovTruncCovGradientAt c x kc C := by
  have hj := termFluxPrefix_and (P₁ := fun c x kc C => CovTruncSizeAt c x kc C)
    (P₂ := fun c x kc _ => CovTruncCovFieldOrderAt c x kc)
    covTruncSize covTruncCovGradient_field_order
  refine termFluxPrefix_map (P := fun c x kc C => CovTruncSizeAt c x kc C ∧
    CovTruncCovFieldOrderAt c x kc) (R := fun c x kc C => CovTruncCovGradientAt c x kc C) ?_ hj
  intro X A kc C₁ hΛ _
  let Cp := covPolyConst (4 * ((covTruncMeanInputOrder A kc : ℕ) : ℝ) ^ 2) A.pT
  have hCp : 0 ≤ Cp := by
    unfold Cp covPolyConst
    exact Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l) (Nat.cast_nonneg _)
  refine ⟨Cp, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hp C' hC'
  obtain ⟨T⟩ := covTruncCovGradient_of_size c x kc C₁ hΛ hp.1 hp.2
  refine ⟨{ T with weighted_bound := fun t ht U => (T.weighted_bound t ht U).trans ?_ }⟩
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCp hC' 2) ?_
  exact Finset.sum_nonneg fun v _ => mul_nonneg
    (inv_nonneg.mpr (Construction.Preservation.Buffer.birth_compMass_pos
      (c.data.2.1 ▸ X.hq.1) (c.data.2.2.1 ▸ hΛ) c.lawW v.1).le) (factorialNormSq_nonneg _ _)

end AVRegularity.Construction.Residual.Presentation
end
end
end
