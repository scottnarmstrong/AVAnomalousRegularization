-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.EntryTerminal.Ingredients.Recon.PartitionGate
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonDescending
public import AVRegularity.Proofs.WeakGen.Residual.Recon.PartitionStatement
public import AVRegularity.Construction.Residual.Presentation.FluxAe
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableBlocks
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
public section
namespace AVRegularity.Providers.WeakGen.Window

/-! **The closing inequality of the price of the weak window** (abstract reals).

The physical lift of the weak window bounds the forcing cost by
`L^K (C_b · bill · M) + L^K (C_b · bill · M)`, with `C_b` the constant of the bill of the
reconstruction. The price of the bill gives `bill ≤ δ e` for every `δ > 0` above a level floor,
with `e = ε_M^{P_w + 2q^{J_w} + 1}`. `weakPrice_close`: at `δ = c_f / (2 L^K |C_b| + 1)` the cost is
below `c_f e M`. No sign of `C_b`, of `c_f` or of `e` is used.

The degenerate cases are included: `C_b = 0` gives `0 ≤ c_f e M` from `0 ≤ bill ≤ c_f e`; `M = 0`
gives `0 ≤ 0`; `K = 0` has `L^K = 1`. -/

/-- **The cost of the weak window at the price of the bill.** -/
theorem weakPrice_close {L Cb bill M fc e : ℝ} (K : ℕ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hbill0 : 0 ≤ bill) (hbill : bill ≤ fc / (2 * (L ^ K * |Cb|) + 1) * e) :
    L ^ K * (Cb * bill * M) + L ^ K * (Cb * bill * M) ≤ fc * e * M := by
  have hc : 0 ≤ L ^ K * |Cb| := mul_nonneg (pow_nonneg hL K) (abs_nonneg Cb)
  have hpos : 0 < 2 * (L ^ K * |Cb|) + 1 := by linarith
  have h1 : (2 * (L ^ K * |Cb|) + 1) * bill ≤ fc * e :=
    calc (2 * (L ^ K * |Cb|) + 1) * bill
        ≤ (2 * (L ^ K * |Cb|) + 1) * (fc / (2 * (L ^ K * |Cb|) + 1) * e) :=
          mul_le_mul_of_nonneg_left hbill hpos.le
      _ = fc * e := by field_simp
  have h2 : L ^ K * (Cb * bill * M) ≤ L ^ K * |Cb| * bill * M :=
    calc L ^ K * (Cb * bill * M) ≤ L ^ K * (|Cb| * bill * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cb) hbill0) hM) (pow_nonneg hL K)
      _ = L ^ K * |Cb| * bill * M := by ring
  have h3 : 2 * (L ^ K * |Cb|) * bill ≤ fc * e :=
    calc 2 * (L ^ K * |Cb|) * bill ≤ (2 * (L ^ K * |Cb|) + 1) * bill :=
          mul_le_mul_of_nonneg_right (by linarith) hbill0
      _ ≤ fc * e := h1
  calc L ^ K * (Cb * bill * M) + L ^ K * (Cb * bill * M)
      ≤ L ^ K * |Cb| * bill * M + L ^ K * |Cb| * bill * M := add_le_add h2 h2
    _ = 2 * (L ^ K * |Cb|) * bill * M := by ring
    _ ≤ fc * e * M := mul_le_mul_of_nonneg_right h3 hM

/-- The same, between the extended nonnegative reals. -/
theorem weakPrice_close_ofReal {L Cb bill M fc e : ℝ} (K : ℕ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hbill0 : 0 ≤ bill) (hbill : bill ≤ fc / (2 * (L ^ K * |Cb|) + 1) * e) :
    ENNReal.ofReal (L ^ K * (Cb * bill * M) + L ^ K * (Cb * bill * M)) ≤
      ENNReal.ofReal (fc * e * M) :=
  ENNReal.ofReal_le_ofReal (weakPrice_close K hL hM hbill0 hbill)

end AVRegularity.Providers.WeakGen.Window
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Change of cap for `IsLiftSetting`.** A lift setting of `Q` at the cap `D₁` is
a lift setting at every cap `D₂ ≥ D₁` of the data with the same `η, G, v` and the edges extended by
`[]` above `D₁` (`extendEdges`), at every orders `(K', k', L')` whose reserves at `D₂` are at most
the given `qs, qf`. -/

section ChangeOfCap

variable {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D₁ D₂ : ℕ}

/-- The edges at the cap `D₂`: those of the cap `D₁` for degrees `≤ D₁`, empty above. -/
def extendEdges (_hD : D₁ ≤ D₂) (edge : ConstituentEdges D₁ h) : ConstituentEdges D₂ h :=
  fun v u d =>
    if hd : d.1 ≤ D₁ then edge v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ else []

/-- The data at the cap `D₂`: the same `η, G, v`, the extended edges. -/
def extendData (hD : D₁ ≤ D₂) (Q : LiftOperatorData ι h D₁) : LiftOperatorData ι h D₂ :=
  ⟨Q.η, Q.G, Q.v, extendEdges hD Q.edge⟩

theorem extendEdges_eq_nil (hD : D₁ ≤ D₂) (edge : ConstituentEdges D₁ h) (v u : ι)
    (d : Finset.Icc 2 D₂) (hd : D₁ < d.1) : extendEdges hD edge v u d = [] := by
  simp [extendEdges, not_le.2 hd]

theorem extendEdges_of_le (hD : D₁ ≤ D₂) (edge : ConstituentEdges D₁ h) (v u : ι)
    (d : Finset.Icc 2 D₂) (hd : d.1 ≤ D₁) :
    extendEdges hD edge v u d = edge v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ := by
  simp [extendEdges, hd]

theorem mem_extendEdges {hD : D₁ ≤ D₂} {edge : ConstituentEdges D₁ h} {v u : ι}
    {d : Finset.Icc 2 D₂} {γ : Constituent d.1 (h u) (h v)}
    (hγ : γ ∈ extendEdges hD edge v u d) :
    ∃ hd : d.1 ≤ D₁, γ ∈ edge v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ := by
  by_cases hd : d.1 ≤ D₁
  · refine ⟨hd, ?_⟩
    rwa [extendEdges_of_le hD edge v u d hd] at hγ
  · rw [extendEdges_eq_nil hD edge v u d (not_le.1 hd)] at hγ
    simp at hγ

/-- The jet envelope sum is unchanged by the extension by empty edges. -/
theorem sum_extendEdges (hD : D₁ ≤ D₂) (edge : ConstituentEdges D₁ h) (v u : ι)
    (I : Set ℝ) (r q : ℕ) :
    ∑ d : Finset.Icc 2 D₂, ((extendEdges hD edge v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r q (γ.coeff α)).sum =
      ∑ d : Finset.Icc 2 D₁, ((edge v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r q (γ.coeff α)).sum := by
  symm
  refine Fintype.sum_of_injective
    (fun d : Finset.Icc 2 D₁ => (⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1,
      (Finset.mem_Icc.1 d.2).2.trans hD⟩⟩ : Finset.Icc 2 D₂)) ?_ _ _ ?_ ?_
  · intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  · intro d hd
    have : D₁ < d.1 := by
      by_contra hle
      exact hd ⟨⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, not_lt.1 hle⟩⟩, rfl⟩
    rw [extendEdges_eq_nil hD edge v u d this]
    simp
  · intro d
    rw [extendEdges_of_le hD edge v u _ (Finset.mem_Icc.1 d.2).2]

variable [Fintype ι] {Q : LiftOperatorData ι h D₁} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {H N K k L K' k' L' qs qf qs' qf' : ℕ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}

/-- **Change of cap.** A lift setting at the cap `D₁` is a lift setting at the cap `D₂ ≥ D₁` of the
data with the same `η, G, v` and the edges extended by `[]`, at orders `(K', k', L')` whose
reserves at `D₂` are at most `qs, qf`. (`weakIsLiftSetting_mono` is the case `D₂ = D₁`.) -/
theorem isLiftSetting_changeCap (hD : D₁ ≤ D₂)
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hqs' : qs' = K' + 4 * (H + 1) * (N + D₂) ^ 2)
    (hqf' : qf' = max k' (L' + 2) + H * D₂ + 2 * N + 2 * D₂)
    (h1 : qs' ≤ qs) (h2 : qf' ≤ qf) :
    IsLiftSetting (extendData hD Q) π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K' k' L' qs' qf'
      CG Cw Cj b Θ := by
  refine
    { window := hS.window, e_pos := hS.e_pos, ν_pos := hS.ν_pos, B_pos := hS.B_pos
      ρ_pos := hS.ρ_pos, E_pos := hS.E_pos, ℓ_eq := hS.ℓ_eq, η_eq := hS.η_eq, η_le := hS.η_le
      dstar_eq := hS.dstar_eq, εc_eq := hS.εc_eq, εc_le := hS.εc_le, lam_eq := hS.lam_eq
      lam_le := hS.lam_le, N_ge := hS.N_ge, D_ge := hS.D_ge.trans hD, qs_eq := hqs',
      qf_eq := hqf', mass_pos := hS.mass_pos, G_symm := hS.G_symm, G_meas := hS.G_meas
      G_smooth := fun t ht i j => (hS.G_smooth t ht i j).of_le (by exact_mod_cast h1)
      G_ellip := hS.G_ellip
      G_jets := fun r hr => hS.G_jets r (hr.trans h1)
      v_shear := hS.v_shear
      V_smooth := fun t ht => (hS.V_smooth t ht).of_le (by exact_mod_cast h2)
      V_per := hS.V_per, V_mean := hS.V_mean, v_meas := hS.v_meas
      w_jets := fun q hq => hS.w_jets q (hq.trans h2)
      depth := ?_, transverse := ?_, coeff_meas := ?_, coeff_smooth := ?_, envelope := ?_ }
  · intro p
    obtain ⟨k, hk⟩ := hS.depth p
    refine ⟨k, fun d => ?_⟩
    by_cases hd : d.1 ≤ D₁
    · exact (extendEdges_of_le hD Q.edge _ _ d hd).trans (hk _)
    · exact extendEdges_eq_nil hD Q.edge _ _ d (not_le.1 hd)
  · intro v u d γ hγ α
    obtain ⟨hd, hγ'⟩ := mem_extendEdges (hD := hD) hγ
    exact hS.transverse v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ γ hγ' α
  · intro v u d γ hγ α X z
    obtain ⟨hd, hγ'⟩ := mem_extendEdges (hD := hD) hγ
    exact hS.coeff_meas v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ γ hγ' α X z
  · intro v u d γ hγ α t ht
    obtain ⟨hd, hγ'⟩ := mem_extendEdges (hD := hD) hγ
    exact CycleComparison.Reconstruction.isBoxSmooth_mono (hS.coeff_smooth v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩ γ hγ' α t ht) h1 h2
  · refine ⟨hS.envelope.nonneg, hS.envelope.row_sum, hS.envelope.col_sum, ?_⟩
    intro v u r hr q hq
    show ENNReal.ofReal (Real.sqrt (π u / π v)) * ∑ d : Finset.Icc 2 D₂,
      ((extendEdges hD Q.edge v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ.coeff α)).sum ≤ _
    rw [sum_extendEdges]
    exact hS.envelope.jets v u r (hr.trans h1) q (hq.trans h2)

end ChangeOfCap

end AVRegularity.Providers.WeakGen.Residual
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.EntryTerminal.Ingredients.Recon
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **A measurable version of the coarse flux with its equation and its bound**
(the adapter for `hcd`, `hFm`, `hFcm`, `hY`).

The inputs give a class `Fc` of the coarse flux, the coarse defect equation with
it and its bound in the mass form `FluxMassLe`. The physical lift asks more of
the flux: Borel measurability of its Galerkin coefficients at the clamped time, and the bound in
the lower-integral form. `coarseFlux_version`: there is a strongly measurable version `Fc'`,
equal to `Fc` almost everywhere on the window, with the same equation, measurable Galerkin
coefficients, and the bound `hY`. It packages the generic lemmas
(`exists_fluxVersion`, `isCoarseDefect_congr_ae`, `measurable_coarseModeCoeff_comp`,
`fluxBound_le_of_ae`) with `fluxMassLe_lintegral`.

The degenerate cases are included: `Fc` strongly measurable may be its own version; `Y = 0` forces
the flux to vanish almost everywhere; an empty window `t₁ < t₀` is excluded by `t₀ ≤ t₁` (the clamp
needs it). -/

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The lower-integral form of a flux bound in the mass form.** -/
theorem fluxMassLe_lintegral {k : ℕ} {ν ρ : ℝ} {π : ι → ℝ} (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    {t₀ t₁ Y : ℝ} {G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hG : FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν ρ π (Set.Icc t₀ t₁) G Y) :
    ENNReal.ofReal (Real.sqrt ν)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
      (massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (G v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
  have hint := CycleComparison.Error.integrable_massNormSq
    (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) ρ π (K := fun _ => k) G hG.1
  have hnn : ∀ s, 0 ≤ massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (G v s).val) := fun s => by
    unfold massNormSq
    exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hnn) (by norm_num),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg ν))]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hG.2)
  rw [Real.sqrt_mul (inv_nonneg.2 hν.le), Real.sqrt_inv]
  simp only [Real.sqrt_eq_rpow]

/-- **A measurable version of the coarse flux**, with the coarse defect equation, the measurable
Galerkin coefficients and the flux bound of the physical lift. -/
theorem coarseFlux_version [DecidableEq ι] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))} {ν ρ : ℝ} {π : ι → ℝ} {Y : ℝ}
    (ht : t₀ ≤ t₁) (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    (hcd : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc)
    (hF : FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν ρ π (Set.Icc t₀ t₁) Fc Y) :
    ∃ Fc' : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)),
      IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc' ∧
      (∀ n r', Measurable fun s =>
        coarseModeCoeff n (fun v => Fc' v (Set.projIcc t₀ t₁ ht s)) r') ∧
      (∀ v, AEStronglyMeasurable (Fc' v) (volume.restrict (Set.Icc t₀ t₁))) ∧
      ENNReal.ofReal (Real.sqrt ν)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
        (massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
          (fun v => (Fc' v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
  obtain ⟨Fc', hae, hsm⟩ := exists_fluxVersion fun v => (hF.1 v).aestronglyMeasurable
  exact ⟨Fc', isCoarseDefect_congr_ae hcd hae,
    fun n r' => measurable_coarseModeCoeff_comp hsm
      (continuous_subtype_val.comp continuous_projIcc).measurable n r',
    fun v => (hsm v).aestronglyMeasurable,
    fluxBound_le_of_ae hae (fluxMassLe_lintegral hν hπ hF)⟩

end AVRegularity.Providers.WeakGen.Window
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.Providers.QuietAtlas
namespace AVRegularity.Providers.WeakGen.Window

/-! **The stage predicates transfer to the re-capped stage.** `IsNatural`,
`IsShiftInvariant`, and (for an all-transfer presentation) a `QuietPresentation` with
`FinerHistoryInvariant` of `G` give those of `G.recap N hN 𝒮`: none of them reads the order cap
`Dm` of the stage (the `.first` sources read it, the `.transfer` sources do not). -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm b j₀} {N : ℕ}
  {hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N} {𝒮 : SeedExports}

theorem recap_isNatural {M : ℕ} (h : G.IsNatural M) : (G.recap N hN 𝒮).IsNatural M := h

theorem recap_isShiftInvariant (h : G.IsShiftInvariant) : (G.recap N hN 𝒮).IsShiftInvariant := h

/-- The presentation of the re-capped stage: the same sources. -/
def recapPresentation (N : ℕ) (hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N)
    (𝒮 : SeedExports) (Q : QuietPresentation G) (hall : Q.AllTransfer) :
    QuietPresentation (G.recap N hN 𝒮) where
  source := Q.source
  represents := by
    intro p c v u γ d I t Y z hd
    obtain ⟨lam, order, fop, hs⟩ := hall v u γ
    have h1 := Q.represents p c v u γ d I t Y z hd
    rw [hs] at h1
    rw [hs]
    exact h1

theorem recapPresentation_allTransfer (Q : QuietPresentation G) (hall : Q.AllTransfer) :
    (recapPresentation N hN 𝒮 Q hall).AllTransfer := hall

theorem recapPresentation_finerHistory (Q : QuietPresentation G) (hall : Q.AllTransfer)
    {Mtop : ℕ} (hF : FinerHistoryInvariant G Q Mtop) :
    FinerHistoryInvariant (G.recap N hN 𝒮) (recapPresentation N hN 𝒮 Q hall) Mtop := by
  intro v u γ n hn k ch ch' hs t ht f
  obtain ⟨lam, order, fop, hs'⟩ := hall v u γ
  have h1 := hF v u γ n hn k ch ch' hs t ht f
  have e : (recapPresentation N hN 𝒮 Q hall).source v u γ = Q.source v u γ := rfl
  rw [e, hs'] at *
  exact h1

end AVRegularity.Providers.WeakGen.Window
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.WeakGen.Window

/-! **The family of the reconstruction window of a weak passage** (the shared definitions).

The stage `c.stage i` of a passage instance has the ambient order cap `c.Dm`, arbitrary above
`1 + J_wN_w`. The reconstruction window (`ReconWindowAt`) carries its family's cap in its orders,
so the window of a weak passage takes the same stage at the cap `1 + J_wN_w`:

* `weakStage_maxOrder_le`: every identity of a passage stage has order at most `1 + J_wN_w`;
* `weakWindowStage`: the stage re-capped at `1 + J_wN_w` (`GenStage.recap`), with its own
  registry of exports;
* `weakWindowFamily`: its actual family, over the components of `c.stage i`;
* `weakWindowSlots`: the slots `K v = k₀ + (J_wR_w - rank v)(J_wN_w - 1)`, the descending
  reserves of the comparison shifted by `k₀`;
* `weakWindow_edgeCoefficient`: the edge coefficient of the window's family at `(κ_M, ε_i,
  ε_{i-1})` is the sum of the stage's physical coefficients, so the coupled system that the
  physical lift of the window returns is the stage's system;
* `weakWindow_physCoeff_nonadmissible`: the stage's coefficients vanish at the orders that are
  not admissible for the slots.

The degenerate cases are included: at the root `i = M + J_w` the stage has no identity and every sum
is empty; `k₀ = 0` gives the reserves of the comparison; `c.Dm` enters none of the statements. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The identities of a passage stage have order at most `1 + J_wN_w`.** -/
theorem weakStage_maxOrder_le (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u) :
    ((c.stage i).fam.identity v u γ).maxOrder ≤ 1 + A.Jw * A.Nw := by
  by_cases heq : i = c.M + A.Jw
  · subst i
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  · exact weakConstruction_output_maxOrder_bound c.P _ c.M A.Jw _ 0 c.stage c.construction i
      (by omega) (by omega) v u γ

/-- **The stage of the window**: the passage stage at the cap `1 + J_wN_w`. -/
def weakWindowStage (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) : GenStage c.D ScalarH (1 + A.Jw * A.Nw) A.bw c.j₀ :=
  (c.stage i).recap (1 + A.Jw * A.Nw) (weakStage_maxOrder_le c i hi hit) (c.stage i).exports

/-- **The family of the window**: the actual family of the re-capped stage. -/
def weakWindowFamily (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) :
    ChartedFamily (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root) (1 + A.Jw * A.Nw)
      OddSlot (fun _ => Unit) :=
  (weakWindowStage c i hi hit).actualFamily

/-- **The slots of the window**: the descending reserves of the comparison, shifted by `k₀`. -/
def weakWindowSlots (c : WeakPassageInstance plan R) (i k₀ : ℕ) :
    CompIn (c.stage i).comps → ℕ :=
  fun v => k₀ + weakComparisonReserve R v.1

theorem weakWindowSlots_ge (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (v : CompIn (c.stage i).comps) : k₀ ≤ weakWindowSlots c i k₀ v :=
  Nat.le_add_right _ _

theorem weakWindowSlots_le (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (v : CompIn (c.stage i).comps) :
    weakWindowSlots c i k₀ v ≤ k₀ + A.Jw * A.Rw * (A.Jw * A.Nw - 1) :=
  Nat.add_le_add_left (weak_comparison_reserve_le R v.1) _

/-- **The slots descend along the family of the window.** -/
theorem weakWindowFamily_isDescending (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (k₀ : ℕ) :
    (weakWindowFamily c i hi hit).IsDescending (weakWindowSlots c i k₀) := by
  intro v u γ
  have hmax := weakStage_maxOrder_le c i hi hit v u γ
  have h := weak_comparison_edge_admissible c i hi hit v u γ
    ((c.stage i).fam.identity v u γ).maxOrder ((c.stage i).fam.identity v u γ).two_le hmax
  have h2 : weakComparisonReserve R v.1 + ((c.stage i).fam.identity v u γ).maxOrder ≤
      weakComparisonReserve R u.1 + 2 := (Finset.mem_filter.1 h).2
  change k₀ + weakComparisonReserve R v.1 + ((c.stage i).fam.identity v u γ).maxOrder ≤
    k₀ + weakComparisonReserve R u.1 + 2
  omega

/-- **The stage's coefficients vanish at the orders not admissible for the slots.** -/
theorem weakWindow_physCoeff_nonadmissible (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (k₀ : ℕ) (v u : CompIn (c.stage i).comps)
    (γ : (c.stage i).fam.Γ v u) (n : ℕ) (hn : n ∈ Finset.Icc 2 (1 + A.Jw * A.Nw))
    (hna : n ∉ admissibleOrders (weakWindowSlots c i k₀) (1 + A.Jw * A.Nw) v u) (s : ℝ)
    (x : Vec 2) : (c.stage i).physCoeff v u γ n s x = 0 := by
  exfalso
  apply hna
  have h := weak_comparison_edge_admissible c i hi hit v u γ n (Finset.mem_Icc.1 hn).1
    (Finset.mem_Icc.1 hn).2
  have h2 : weakComparisonReserve R v.1 + n ≤ weakComparisonReserve R u.1 + 2 :=
    (Finset.mem_filter.1 h).2
  refine Finset.mem_filter.2 ⟨hn, ?_⟩
  change k₀ + weakComparisonReserve R v.1 + n ≤ k₀ + weakComparisonReserve R u.1 + 2
  omega

/-- **The edge coefficient of the window's family is the stage's**, at the diffusivity `κ_M` and
the scales `(ε_i, ε_{i-1})`. -/
theorem weakWindow_edgeCoefficient (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (K : CompIn (c.stage i).comps → ℕ) (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders K (1 + A.Jw * A.Nw) v u) (s : ℝ) (x : Vec 2) :
    edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) K v u d s x =
      ∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 s x := by
  have hlev : (c.stage i).level = i :=
    weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
  have h := congrFun (congrFun (congrFun (congrFun (congrFun
    (GenStage.edgeCoefficient_actualFamily (weakWindowStage c i hi hit) (c.D.κ c.M)
      (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) K) v) u) d) s) x
  refine h.trans ?_
  simp only [edgeCoefficient, physicalCoefficient, GenStage.physCoeff, hlev, hkap]
  rfl

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Window

/-! **Three facts on the stages of a weak passage** (inputs of the top assembly).

* `weakConstruction_comps_nonempty`, `weakStage_nonempty`: every stage `M ≤ i ≤ M + J_w` has a
  component. The root stage has the single component `⟨r, []⟩`, and each passage extends the
  component set of its incoming stage (`weakExtComps` contains it). So the letters `cdAD` of the
  window can be taken at a reference component `v₀`.
* `weakStage_isNatural_of_le`: every such stage is natural at the top level `M + J_w` (the root by
  `IsWeakRoot`, the others as outputs of a passage).
* `weakStage_weight`: its weights are the cutoffs of its level, the hypothesis `hw` of
  `weakLifted_of_window` and of the partition adapter.

The degenerate cases are included: `J_w = 0` is the root alone; `R_w = 0` adds no component and
keeps the root's. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- **Every stage of a weak construction has a component.** -/
theorem weakConstruction_comps_nonempty {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {P : ProvParams} {Mn : WeakMenu} {M J : ℕ} {rW : ℝ} {r : ℕ}
    {stage : ℕ → GenStage D ScalarH Dm b j₀}
    (hc : IsWeakConstruction D P Mn M J rW r stage) :
    ∀ n, n ≤ J → (stage (M + J - n)).comps.Nonempty
  | 0, _ => by
    simp only [Nat.sub_zero]
    rw [hc.2.1.2.1]
    exact Finset.singleton_nonempty _
  | n + 1, hn => by
    have ih := weakConstruction_comps_nonempty hc n (by omega)
    have hpass := (hc.2.2 (M + J - n) (by omega) (by omega)).1
    rw [show M + J - (n + 1) = M + J - n - 1 by omega, hpass.2.2.2.1]
    exact ih.mono Finset.subset_union_left

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Every stage of a passage instance has a component.** -/
theorem weakStage_nonempty (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i)
    (hit : i ≤ c.M + A.Jw) : Nonempty (CompIn (c.stage i).comps) := by
  have h := weakConstruction_comps_nonempty c.construction (c.M + A.Jw - i) (by omega)
  rw [show c.M + A.Jw - (c.M + A.Jw - i) = i by omega] at h
  obtain ⟨x, hx⟩ := h
  exact ⟨⟨x, hx⟩⟩

/-- **Every stage of a passage instance is natural** at the top level `M + J_w`. -/
theorem weakStage_isNatural_of_le (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i)
    (hit : i ≤ c.M + A.Jw) : (c.stage i).IsNatural (c.M + A.Jw) := by
  by_cases heq : i = c.M + A.Jw
  · subst heq
    exact c.construction.2.1.2.2.2
  · have h := (c.construction.2.2 (i + 1) (by omega) (by omega)).1.2.2.2.2.1
    simpa only [Nat.add_sub_cancel] using h

/-- **The weights of a passage stage are the cutoffs of its level.** -/
theorem weakStage_weight (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i)
    (hit : i ≤ c.M + A.Jw) (p : OddSlot) (s : ℝ) :
    (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s := by
  have hlev : (c.stage i).level = i :=
    EntryWeakProofs.weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi hit
  exact ((weakStage_isNatural_of_le c i hi hit).2.1 p s).trans
    (congrArg (fun m => ocCutoff c.D.α c.D.q c.D.Λ m p.1 s) hlev)

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.WeakGen.Window

/-! **The coefficient bounds of the weak window from the edge bounds of the actual family**.

The edge bounds (`WeakReconBoundsAt`) bound the edge coefficients of the actual family of the stage
at its ambient cap `c.Dm`. The window's family is the actual family of the stage re-capped at
`1 + J_wN_w` (`weakWindowFamily`). Both coefficients are the same sums of the stage's physical
coefficients (`weakStage_edgeCoefficient`, `weakWindow_edgeCoefficient`), so the bounds pass to
the window: `weakWindow_edge_bounds` gives the hypotheses `hAb`, `hAm` of the physical lift.

The degenerate cases are included: a stage without identity has zero coefficients on both sides; an
order `d ≤ 1 + J_wN_w` admissible for the slots is admissible at the cap `c.Dm`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The edge coefficient of the actual family of the stage, at the ambient cap, is the sum of
the stage's physical coefficients.** -/
theorem weakStage_edgeCoefficient (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (K : CompIn (c.stage i).comps → ℕ) (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders K c.Dm v u) (s : ℝ) (x : Vec 2) :
    edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M) (c.D.eps i) (c.D.eps (i - 1))
        (fun _ => ()) K v u d s x =
      ∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 s x := by
  have hlev : (c.stage i).level = i :=
    weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
  have h := congrFun (congrFun (congrFun (congrFun (congrFun
    (GenStage.edgeCoefficient_actualFamily (c.stage i) (c.D.κ c.M) (c.D.eps i)
      (c.D.eps (i - 1)) K) v) u) d) s) x
  refine h.trans ?_
  simp only [edgeCoefficient, physicalCoefficient, GenStage.physCoeff, hlev, hkap]

/-- An order admissible at the cap `1 + J_wN_w` is admissible at the ambient cap. -/
def weakWindowOrderUp (c : WeakPassageInstance plan R) (i : ℕ)
    (K : CompIn (c.stage i).comps → ℕ) (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders K (1 + A.Jw * A.Nw) v u) : admissibleOrders K c.Dm v u :=
  ⟨d.1, Finset.mem_filter.2 ⟨Finset.mem_Icc.2
    ⟨(Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1,
      (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).2.trans c.order_ge⟩,
    (Finset.mem_filter.1 d.2).2⟩⟩

/-- The window's coefficient is the stage's coefficient at the same order. -/
theorem weakWindow_edgeCoefficient_eq_stage (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (K : CompIn (c.stage i).comps → ℕ)
    (v u : CompIn (c.stage i).comps) (d : admissibleOrders K (1 + A.Jw * A.Nw) v u) (s : ℝ) :
    edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) K v u d s =
      edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M) (c.D.eps i) (c.D.eps (i - 1))
        (fun _ => ()) K v u (weakWindowOrderUp c i K v u d) s := by
  funext x
  rw [weakWindow_edgeCoefficient c i hi hit K v u d s x,
    weakStage_edgeCoefficient c i hi hit K v u (weakWindowOrderUp c i K v u d) s x]
  rfl

/-- **The coefficient bounds of the weak window** (`hAb`, `hAm`) from the coefficient bounds. -/
theorem weakWindow_edge_bounds (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (K : CompIn (c.stage i).comps → ℕ) {Vb CA : ℝ}
    (hb : WeakReconBoundsAt c r i K Vb CA) :
    (∀ s ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v u
        (d : admissibleOrders K (1 + A.Jw * A.Nw) v u) x,
      ‖edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) K v u d s x‖ ≤ CA) ∧
    ∀ s ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v u (d : admissibleOrders K (1 + A.Jw * A.Nw) v u),
      AEStronglyMeasurable (edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M)
        (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) K v u d s)
        (volume.restrict unitCube) := by
  obtain ⟨-, -, -, hAb, hAm⟩ := hb
  refine ⟨fun s hs v u d x => ?_, fun s hs v u d => ?_⟩
  · rw [weakWindow_edgeCoefficient_eq_stage c i hi hit K v u d s]
    exact hAb s hs v u (weakWindowOrderUp c i K v u d) x
  · rw [weakWindow_edgeCoefficient_eq_stage c i hi hit K v u d s]
    exact hAm s hs v u (weakWindowOrderUp c i K v u d)

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Providers.WeakGen.Window

/-! **The glued lift of the weak window is the glued weak lift**.

The physical lift of the reconstruction window of a weak passage returns the glued lift in the
window's form: the observed pulses of the whole window, the weights of the window's family, the
cell time `ℓ_i²`, the lift length `ε_{i-1}`, the contrast `d_*/ρ`, the renewal charts. The
`weakGluedLift` uses the pulses observed at the time, the
cutoffs, `D.cellScaleSq i`, `ε_i/ε_{i-1}` and the flows from the slot anchors, and takes the field
at the time. `weakWindow_gluedLift_eq`: at a time of the window they agree, for a stage whose
weights are the cutoffs. It is the weak form of `stage_gluedLift_eq_menuLiftedRep`; the new points
are `ν = B = κ_M` (so `d_* = ε_i`) and the freezing of the field at the time
(`gluedLift_congr_time`).

The degenerate cases are included: a time in no pulse window has no observed pulse and both sides
are zero; `tp = tf = t` is the identity of the pulse sets. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- At a weak level the cell time of the window is the cell scale of the level. -/
theorem weakWindow_cellTime (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hκ : 0 < c.D.κ c.M) : ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 = c.D.cellScaleSq i := by
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
  unfold ocEll OCData.cellScaleSq OCData.eps
  rw [hkap, div_pow, Real.sq_sqrt hκ.le]

/-- At equal diffusivities the length `d_*` is `ε_i`. -/
theorem weakWindow_dStar (c : WeakPassageInstance plan R) (i : ℕ) (hκ : 0 < c.D.κ c.M) :
    ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) = ocEpsilon c.D.q c.D.Λ i := by
  unfold ocDStar
  rw [div_self hκ.ne', Real.sqrt_one, mul_one]

/-- **The glued lift of the weak window is the glued weak lift**, at a time of the window. -/
theorem weakWindow_gluedLift_eq (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root))
    (g : ℝ → CompIn (c.stage i).comps → Vec 2 → ℝ) {tp tf t : ℝ} (x : Vec 2)
    (hΛ : 1 ≤ c.D.Λ) (hκ : 0 < c.D.κ c.M)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    (ht : t ∈ Set.Icc tp tf) (v : CompIn (c.stage i).comps) :
    gluedLift (ocObsPulses c.D.α c.D.q c.D.Λ i tp tf)
        (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
        (ocEpsilon c.D.q c.D.Λ i)
        (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
        A.Nw (A.Jw * A.Rw) Cc
        (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (fun s y w => g s w y) t x v =
      weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) Cc t (g t) v x := by
  classical
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTau_pos hΛ
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTauPP_pos hΛ
  have hc := weakWindow_cellTime c i hi hκ
  have hds := weakWindow_dStar c i hκ
  have hc0 : ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 ≠ 0 := by
    unfold ocEll
    exact pow_ne_zero 2 (div_ne_zero (Construction.Stream.ocEpsilon_pos hΛ).ne'
      (Real.sqrt_pos.2 hκ).ne')
  have hchart : ∀ k : ℤ, ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
        fun s' y => c.D.flowOf (i - 1) s' y (c.D.slotAnchor i k) := by
    intro k
    funext s' y
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ'']
  have hinv : ∀ k : ℤ, ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
        fun s' y => c.D.flowOf (i - 1) (c.D.slotAnchor i k) y s' := by
    intro k
    funext s' y
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ'']
  have hweight : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i tp tf,
      (weakWindowFamily c i hi hit).weight (oddSlotOf k) t = ocCutoff c.D.α c.D.q c.D.Λ i k t := by
    intro k hk
    have hodd : Odd k := by
      unfold ocObsPulses at hk
      exact (Finset.mem_filter.1 hk).2.1
    rw [oddSlotOf_of_odd hodd]
    exact hw ⟨k, hodd⟩ t
  rw [gluedLift_congr_time _ _ hc0 _ _ _ _ _ _ _ _
    (a := fun s y w => g s w y) (b := fun _ y w => g t w y) rfl x]
  unfold weakGluedLift gluedLift
  simp only [hc, hds, hchart, hinv, OCData.eps]
  rw [Finset.sum_congr rfl fun k hk => by rw [hweight k hk]]
  symm
  refine congrFun (Finset.sum_subset (obsPulses_time_subset c.D.α c.D.q c.D.Λ i hτ ht)
    fun k hk hnk => ?_) v
  have hodd : Odd k := by
    unfold ocObsPulses at hk
    exact (Finset.mem_filter.1 hk).2.1
  have hout : t ∉ ocPulseWindow c.D.α c.D.q c.D.Λ i k := fun hin =>
    hnk (mem_obsPulses_time c.D.α c.D.q c.D.Λ i hτ hodd hin)
  rw [AVRegularity.WeakEntryProofs.ocCutoff_zero_off_output c.D.α c.D.q c.D.Λ i hτ k t hout,
    zero_smul]

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **The data of the reconstruction window of a weak passage**.
For a passage `M < i ≤ M + J_w` of an instance `c`, a run `r` and a comparison input `h`,
the window `ReconWindowAt … ρ ρc Jm …` has

* the family `weakWindowFamily c i` (the stage `i` re-capped at `D_w = 1 + J_wN_w`), the pieces
  `oddSlotOf`, the trivial actual context, the slots `weakWindowSlots c i k₀`;
* the scales `ν = B = κ_M`, `ρs = ε_i`, the lift length `ρ = ε_{i-1}`, the radius of the coarse
  setting `ρc = plan.radius R · ε_{i-1}`, `Jm = κ_M · 1`;
* the window `[t_i, a + T₀]`, `tp = r.tq i`, `T_obs = a + T₀ - t_i`;
* the masses `weakMass`, the count `H = J_wR_w`, `N_c = N_w`, the lift coefficients `h.CcR i`, the
  parallel direction `pulseParallel` and the shear profile `pulseShearProfile … κ_M`;
* the lift orders `weakKlift`, `weakLlift`, functions of the request and of `k₀`.

The coarse data (`AD, CE, Aedge, W, f0, Fc, aRep` and the constants of the coarse setting) are
parameters (supplied by the coarse defect statements). Constants are named functions of the plan and the request.
`D_m` (`c.Dm`) enters nowhere. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-! ### Constants and orders -/

/-- The cap of the window, `D_w = 1 + J_wN_w`. -/
abbrev weakDw {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ := 1 + A.Jw * A.Nw

/-- The count of the graph, `H = J_wR_w`. -/
abbrev weakH {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ := A.Jw * A.Rw

/-- The cleanup order of the window, `A_cl = 1`. -/
abbrev weakAcl : ℕ := 1

/-- `K_max = k₀ + J_wR_w(J_wN_w - 1)`. -/
abbrev weakKmax {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  k₀ + A.Jw * A.Rw * (A.Jw * A.Nw - 1)

/-- `K_lift` (the terminal shape, with `D_t = D_w`, `d_w = H`, `N_T = N_w`). -/
abbrev weakKlift {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  2 * weakAcl + 2 + weakKmax A k₀ + weakDw A * (weakH A + 1) * A.Nw + 2

/-- `L_lift`. -/
abbrev weakLlift {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakKmax A k₀ + weakDw A * (weakH A + 1) * A.Nw + 2

/-- The uniform derivative constant of the pulse cutoffs: the partition constant of the window. -/
noncomputable def weakCpart : ℝ := Classical.choose CycleReference.cutoff_derivative_uniform_bound

/-! ### The data of the window -/

section Data

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- The length of the window `T_obs = a + T₀ - t_i`. -/
abbrev wTobs : ℝ := r.a + A.T₀ - r.tq i

/-- The radius of the coarse setting, `ρc = plan.radius R · ε_{i-1}`. -/
abbrev wRhoC : ℝ := plan.radius R * ocEpsilon c.D.q c.D.Λ (i - 1)

/-- The constant flux matrix of the window, `κ_M · 1`. -/
abbrev wJm : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun _ => c.D.κ c.M • 1

/-- The lift data of the observed pulse `k`. -/
abbrev wLiftData (k : ℤ) :
    LiftOperatorData (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root) (weakDw A) :=
  pulseLiftData c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.Φ (i - 1)) (c.D.hΦ (i - 1)) (c.D.κ c.M)
    (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ (i - 1) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) k
    ((weakWindowFamily c i hi hit).fiber (oddSlotOf k) ())

/-- The window `ReconWindowAt` of a weak passage, at the data above and the free data: the atlas
`T`, the slot shift `k₀`, the orders and constants of the lift settings, the coarse data. -/
abbrev WeakWindow (h : WeakComparisonInput r i) (k₀ : ℕ)
    (T : (weakWindowFamily c i hi hit).Atlas) (Cpart : ℝ) (qs qf : ℕ)
    (CGl Cw : ℕ → ℝ) (Ca : ℝ) (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ)
    (Sb : ℝ) (aC B₀C lamC : ℝ) (pc Jc kc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4)) (ScalarH v.1.root))
    (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root))
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn (c.stage i).comps, ScalarH v.1.root) (r₀ : ℕ) : Prop :=
  ReconWindowAt c.D.α B.s c.D.q c.D.Λ c.D.ζ c.D.Φ i (c.D.hΦ (i - 1)) (c.D.κ c.M) (c.D.κ c.M)
    (r.tq i) (wTobs c r i) (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1))
    (wRhoC c i) (wJm c) (weakWindowFamily c i hi hit) (fun _ => ()) (weakWindowSlots c i k₀) T
    oddSlotOf (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Cpart (weakH A) A.Nw (weakKlift A k₀)
    (weakLlift A k₀) qs qf (h.CcR i) pulseParallel
    (fun k => pulseShearProfile c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.κ c.M) k) CGl Cw Ca bM Sb aC B₀C
    lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀

end Data

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Window

/-! **The bill of the reconstruction window of a weak passage** (the
definition and the five dominations).

`ReconPhysicalLiftStatement` takes a real `bill` with the lower bounds `hb1`–`hb5` and
`hPM : Xp ≤ Cpx * bill`, and returns the residual at `reconBillConst(…) · bill · M`. At a weak
passage (`ν = B = κ_M`, lift length `ε_{i-1}`, `N_c = N_w`, `A_cl = weakAcl`) the bill is the
SUM of the five left sides and of a partition term `Xp`:

* `weakReconContrast c i = d_*/ε_{i-1}` (`d_* = ε_i` at equal diffusivities);
* `weakReconZ c r i = √T_obs/ℓ_i · (ε_i/ε_{i-1})^{A_cl}`, the cleanup factor;
* `weakReconBill c r i tt Xp`, with `tt` the flux price and `Xp` the partition term
  (`weakReconPartitionBillTerm`).

Each of `hb1`–`hb5` and `Xp ≤ bill` is then one of `weakReconBill_ge₁ … _ge₅`,
`weakReconBill_ge_partition`, for nonnegative `tt`, `Xp`. The smallness of the bill against
`ε_M^{P}` is the price step.

The degenerate cases are included: `tt = 0`, `Xp = 0` leave `contrast^{N_w}(1 + Z)`;
`T_obs = 0` gives `Z = 0`. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The contrast `d_*/ρ` of the weak window. -/
def weakReconContrast (c : WeakPassageInstance plan R) (i : ℕ) : ℝ :=
  ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1)

/-- The cleanup factor `√T_obs/ℓ_i · (ε_i/ρ)^{A_cl}` of the weak window. -/
def weakReconZ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : ℝ :=
  Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
    (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ weakAcl

/-- **The bill of the weak window**, at a flux price `tt` and a partition term `Xp`. -/
def weakReconBill (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (tt Xp : ℝ) : ℝ :=
  weakReconContrast c i ^ A.Nw + Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt +
    weakReconContrast c i ^ 2 * tt + weakReconContrast c i ^ A.Nw * weakReconZ c r i +
    weakReconContrast c i ^ 2 * weakReconZ c r i * tt + Xp

theorem weakReconContrast_nonneg (c : WeakPassageInstance plan R) (i : ℕ) (hΛ : 1 ≤ c.D.Λ) :
    0 ≤ weakReconContrast c i := by
  unfold weakReconContrast ocDStar
  exact div_nonneg (mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _))
    (Construction.Stream.ocEpsilon_pos hΛ).le

theorem weakReconZ_nonneg (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hΛ : 1 ≤ c.D.Λ) : 0 ≤ weakReconZ c r i := by
  unfold weakReconZ ocEll
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _)))
    (pow_nonneg (div_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le
      (Construction.Stream.ocEpsilon_pos hΛ).le) _)

section Dominations

variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) {tt Xp : ℝ}
  (hΛ : 1 ≤ c.D.Λ) (htt : 0 ≤ tt) (hXp : 0 ≤ Xp)

include hΛ htt hXp

/-- `hb1`. -/
theorem weakReconBill_ge₁ : weakReconContrast c i ^ A.Nw ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h2 : 0 ≤ Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt := mul_nonneg (Real.sqrt_nonneg _) htt
  have h3 : 0 ≤ weakReconContrast c i ^ 2 * tt := mul_nonneg (pow_nonneg h0 _) htt
  have h4 : 0 ≤ weakReconContrast c i ^ A.Nw * weakReconZ c r i :=
    mul_nonneg (pow_nonneg h0 _) hZ
  have h5 : 0 ≤ weakReconContrast c i ^ 2 * weakReconZ c r i * tt :=
    mul_nonneg (mul_nonneg (pow_nonneg h0 _) hZ) htt
  linarith

/-- `hb2`. -/
theorem weakReconBill_ge₂ :
    Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h1 : 0 ≤ weakReconContrast c i ^ A.Nw := pow_nonneg h0 _
  have h3 : 0 ≤ weakReconContrast c i ^ 2 * tt := mul_nonneg (pow_nonneg h0 _) htt
  have h4 : 0 ≤ weakReconContrast c i ^ A.Nw * weakReconZ c r i :=
    mul_nonneg (pow_nonneg h0 _) hZ
  have h5 : 0 ≤ weakReconContrast c i ^ 2 * weakReconZ c r i * tt :=
    mul_nonneg (mul_nonneg (pow_nonneg h0 _) hZ) htt
  linarith

/-- `hb3`. -/
theorem weakReconBill_ge₃ : weakReconContrast c i ^ 2 * tt ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h1 : 0 ≤ weakReconContrast c i ^ A.Nw := pow_nonneg h0 _
  have h2 : 0 ≤ Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt := mul_nonneg (Real.sqrt_nonneg _) htt
  have h4 : 0 ≤ weakReconContrast c i ^ A.Nw * weakReconZ c r i :=
    mul_nonneg (pow_nonneg h0 _) hZ
  have h5 : 0 ≤ weakReconContrast c i ^ 2 * weakReconZ c r i * tt :=
    mul_nonneg (mul_nonneg (pow_nonneg h0 _) hZ) htt
  linarith

/-- `hb4`. -/
theorem weakReconBill_ge₄ :
    weakReconContrast c i ^ A.Nw * weakReconZ c r i ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h1 : 0 ≤ weakReconContrast c i ^ A.Nw := pow_nonneg h0 _
  have h2 : 0 ≤ Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt := mul_nonneg (Real.sqrt_nonneg _) htt
  have h3 : 0 ≤ weakReconContrast c i ^ 2 * tt := mul_nonneg (pow_nonneg h0 _) htt
  have h5 : 0 ≤ weakReconContrast c i ^ 2 * weakReconZ c r i * tt :=
    mul_nonneg (mul_nonneg (pow_nonneg h0 _) hZ) htt
  linarith

/-- `hb5`. -/
theorem weakReconBill_ge₅ :
    weakReconContrast c i ^ 2 * weakReconZ c r i * tt ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h1 : 0 ≤ weakReconContrast c i ^ A.Nw := pow_nonneg h0 _
  have h2 : 0 ≤ Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt := mul_nonneg (Real.sqrt_nonneg _) htt
  have h3 : 0 ≤ weakReconContrast c i ^ 2 * tt := mul_nonneg (pow_nonneg h0 _) htt
  have h4 : 0 ≤ weakReconContrast c i ^ A.Nw * weakReconZ c r i :=
    mul_nonneg (pow_nonneg h0 _) hZ
  linarith

omit hXp in
/-- The partition term is below the bill (`hPM` with the constant of the term). -/
theorem weakReconBill_ge_partition : Xp ≤ weakReconBill c r i tt Xp := by
  have h0 := weakReconContrast_nonneg c i hΛ
  have hZ := weakReconZ_nonneg c r i hΛ
  unfold weakReconBill
  have h1 : 0 ≤ weakReconContrast c i ^ A.Nw := pow_nonneg h0 _
  have h2 : 0 ≤ Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt := mul_nonneg (Real.sqrt_nonneg _) htt
  have h3 : 0 ≤ weakReconContrast c i ^ 2 * tt := mul_nonneg (pow_nonneg h0 _) htt
  have h4 : 0 ≤ weakReconContrast c i ^ A.Nw * weakReconZ c r i :=
    mul_nonneg (pow_nonneg h0 _) hZ
  have h5 : 0 ≤ weakReconContrast c i ^ 2 * weakReconZ c r i * tt :=
    mul_nonneg (mul_nonneg (pow_nonneg h0 _) hZ) htt
  linarith

end Dominations

end AVRegularity.Providers.WeakGen.Window
end
end
end
