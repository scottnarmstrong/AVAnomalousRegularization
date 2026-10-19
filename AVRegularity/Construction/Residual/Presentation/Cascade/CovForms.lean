-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.FluxForms
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.EntryTerminal.Ingredients.Recon.Energy.Chain
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelopeStatement
public import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.StageForced
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovCommCont
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic

section
section
/-! **The size form of the covariance primitive at a cascade frame.**

`CovSizeForm F.Mn D m tp tf (rhoEnh D cr m) (frameOmega F cr)` for the levels `m ≥ m_*` of a band
chain, where `ω = frameOmega F cr = ‖𝖧‖_∞/ρ²` is the quantity of `succBill`.

* `covSizeForm_of_bound`: the form holds with `ω` the supremum over the window as soon as the
  matrix `𝖧(t)` has `covBound ≤ ρ²` and is continuous (generic over the stage and the menu;
  the menu has the anchor `0`, so that its primitive is `covPrimitive D m`).
* `covBound_le_of_bandChain`: the fourth estimate of `bandChain_covariance_estimates` gives
  `covBound 𝖧(t) ≤ 4 C ε_{m-1}^δ ρ² / c_r²`.
* `covSizeForm_at_frame`: the frame statement; the constants (`Λ₀`, then `m_*` after `c_r`)
  are chosen before the frame.

The degenerate cases are included:
- `t_p = t_f` (or `t_f < t_p`): the window is a point (or empty), the form holds with `ω` the value
  at the point (or `0`).
- `H ≡ 0`: `ω = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter Topology
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! ### The supremum -/

/-- A uniform bound on the matrices bounds their supremum over a window. -/
theorem iSup_covBound_le {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {tp tf L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ t ∈ Set.Icc tp tf, covBound (H t) ≤ L) :
    (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |H t a a'|) ≤ L := by
  rcases isEmpty_or_nonempty (Set.Icc tp tf) with hE | hN
  · rw [Real.iSup_of_isEmpty]
    exact hL
  · exact ciSup_le fun t => hb t.1 t.2

/-- Each matrix is bounded by the supremum over the window. -/
theorem le_iSup_covBound {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {tp tf L : ℝ}
    (hb : ∀ t ∈ Set.Icc tp tf, covBound (H t) ≤ L) {t : ℝ} (ht : t ∈ Set.Icc tp tf) :
    covBound (H t) ≤ ⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |H t a a'| := by
  have hbdd : BddAbove (Set.range fun t : Set.Icc tp tf => ∑ a : Fin 2, ∑ a' : Fin 2, |H t a a'|) :=
    ⟨L, by rintro _ ⟨s, rfl⟩; exact hb s.1 s.2⟩
  exact le_ciSup hbdd (⟨t, ht⟩ : Set.Icc tp tf)

/-- The supremum is nonnegative. -/
theorem iSup_covBound_nonneg (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (tp tf : ℝ) :
    0 ≤ ⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |H t a a'| :=
  Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-! ### The generic form -/

/-- **The size form from a uniform bound `covBound ≤ ρ²` and continuity**, with
`ω = (sup covBound)/ρ²`. -/
theorem covSizeForm_of_bound {D : OCData} (Mn : SuccMenu) (hMn : Mn.anchor = 0) (m : ℕ)
    (tp tf ρ : ℝ) (hρ : 0 < ρ)
    (hb : ∀ t ∈ Set.Icc tp tf, covBound (menuCovPrimitive D Mn m t) ≤ ρ ^ 2)
    (hc : ContinuousOn (fun t => menuCovPrimitive D Mn m t) (Set.Icc tp tf)) :
    CovSizeForm Mn D m tp tf ρ
      ((⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D m t a a'|) / ρ ^ 2) := by
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have e : ∀ t, menuCovPrimitive D Mn m t = covPrimitive D m t := fun t => by
    simp only [menuCovPrimitive, covPrimitive, hMn]
  have hb' : ∀ t ∈ Set.Icc tp tf, covBound (covPrimitive D m t) ≤ ρ ^ 2 := fun t ht => by
    rw [← e]; exact hb t ht
  refine ⟨fun t ht => ?_, ?_, ?_, hc⟩
  · rw [div_mul_cancel₀ _ hρ2.ne', e]
    exact le_iSup_covBound hb' ht
  · exact div_nonneg (iSup_covBound_nonneg _ _ _) hρ2.le
  · rw [div_le_one hρ2]
    exact iSup_covBound_le hρ2.le hb'

/-! ### The band chain estimate -/

/-- The enhanced radius squared is `c_r² κ_{m-1} τ''_m`. -/
theorem rhoEnh_sq (D : OCData) (cr : ℝ) (m : ℕ) (hκ : 0 < D.κ (m - 1))
    (hτ : 0 < ocTauPP D.α D.q D.Λ m) :
    rhoEnh D cr m ^ 2 = cr ^ 2 * (D.κ (m - 1) * ocTauPP D.α D.q D.Λ m) := by
  unfold rhoEnh
  rw [mul_pow, Real.sq_sqrt (mul_pos hκ hτ).le]

/-- **The entrywise band chain estimate at the menu primitive**: `covBound 𝖧(t) ≤ 4 C ε_{m-1}^δ ρ²/c_r²`
at the enhanced radius `ρ = c_r √(κ_{m-1} τ''_m)`. -/
theorem covBound_le_of_bandChain {D : OCData} {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {C : ℝ}
    (Mn : SuccMenu) (hMn : Mn.anchor = 0) (cr : ℝ) (hcr : 0 < cr)
    (hDα : D.α = α) (hDq : D.q = q) (hDΛ : D.Λ = Λ) (hDζ : D.ζ = ζ)
    (hκ : 0 < D.κ (m - 1)) (hτ : 0 < ocTauPP α q Λ m)
    (hent : ∀ (t : ℝ) (i j : Fin 2),
      |ocCovariance α q Λ ζ m (D.κ m) (D.κ (m - 1)) 0 t i j| /
        ocRh α q Λ m (D.κ (m - 1)) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^ ocDelta α q) (t : ℝ) :
    covBound (menuCovPrimitive D Mn m t) ≤
      4 * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q / cr ^ 2 * rhoEnh D cr m ^ 2 := by
  have hρ2 : rhoEnh D cr m ^ 2 = cr ^ 2 * ocRh α q Λ m (D.κ (m - 1)) ^ 2 := by
    rw [rhoEnh_sq D cr m hκ (hDα ▸ hDq ▸ hDΛ ▸ hτ)]
    unfold ocRh
    rw [Real.sq_sqrt (mul_pos hκ hτ).le, hDα, hDq, hDΛ]
  have hpos : 0 < ocRh α q Λ m (D.κ (m - 1)) ^ 2 := by
    unfold ocRh
    rw [Real.sq_sqrt (mul_pos hκ hτ).le]
    exact mul_pos hκ hτ
  have e1 : menuCovPrimitive D Mn m t =
      ocCovariance α q Λ ζ m (D.κ m) (D.κ (m - 1)) 0 t := by
    simp only [menuCovPrimitive, hMn, hDα, hDq, hDΛ, hDζ]
  have h4 : ∀ i j, |menuCovPrimitive D Mn m t i j| ≤
      C * ocEpsilon q Λ (m - 1) ^ ocDelta α q * ocRh α q Λ m (D.κ (m - 1)) ^ 2 := by
    intro i j
    rw [e1]
    exact (div_le_iff₀ hpos).1 (hent t i j)
  rw [hρ2]
  have e2 : 4 * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q / cr ^ 2 * (cr ^ 2 *
      ocRh α q Λ m (D.κ (m - 1)) ^ 2) =
      4 * (C * ocEpsilon q Λ (m - 1) ^ ocDelta α q * ocRh α q Λ m (D.κ (m - 1)) ^ 2) := by
    field_simp
  rw [e2]
  simp only [covBound, Fin.sum_univ_two]
  have := h4 0 0
  have := h4 0 1
  have := h4 1 0
  have := h4 1 1
  linarith

/-! ### The frame statement -/

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The sum of two realized fluxes and the union of the two frontier selections**
(cascade side of the bill residual).

* `not_retained_iff`: on the components of the extended stage (grade at most `H + 1`, and word
  length at most `J + 1` when the grade is at most `H`) the omitted rows `¬ IsRetained m H J` are
  the union of the grade frontier (`grade = H + 1`) and the length frontier
  (`grade ≤ H ∧ |word| = J + 1`), and the two selections are disjoint.
* `readoutFlux_add_sel`: the readout over a union of two disjoint selections is the sum of
  the two readouts.
* `hasFluxBound_add'`: two realized fluxes add, and the bounds add (Minkowski in `L²(I)`).

For `J = 0` the length frontier is the words of length `1`, and with no omitted row both
selections are empty and the sum is `0 + 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The omitted rows are the union of the grade frontier and the length frontier. -/
theorem not_retained_iff {m H J : ℕ} {c : Comp} (hg : compGrade c ≤ H + 1)
    (hl : compGrade c ≤ H → (compWord m c).length ≤ J + 1) :
    ¬ IsRetained m H J c ↔
      (compGrade c = H + 1 ∨ (compGrade c ≤ H ∧ (compWord m c).length = J + 1)) := by
  unfold IsRetained
  constructor
  · intro h
    by_cases h1 : compGrade c ≤ H
    · right
      have h2 := hl h1
      refine ⟨h1, ?_⟩
      by_contra h3
      exact h ⟨h1, by omega⟩
    · left; omega
  · rintro (h | ⟨h1, h2⟩) ⟨h3, h4⟩ <;> omega

/-- The two selections are disjoint. -/
theorem select_disjoint {H J m : ℕ} {c : Comp} :
    ¬ (compGrade c = H + 1 ∧ (compGrade c ≤ H ∧ (compWord m c).length = J + 1)) := by
  rintro ⟨h1, h2, -⟩
  omega

open scoped Classical in
/-- The readout over a union of two disjoint selections is the sum of the readouts. -/
theorem readoutFlux_add_sel {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ) (sel sel₁ sel₂ : Comp → Prop)
    (hsel : ∀ c ∈ S', sel c ↔ sel₁ c ∨ sel₂ c) (hdisj : ∀ c ∈ S', ¬ (sel₁ c ∧ sel₂ c))
    (F : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) :
    readoutFlux (hr := hr) m E η₀ sel F v t x =
      readoutFlux m E η₀ sel₁ F v t x + readoutFlux m E η₀ sel₂ F v t x := by
  unfold readoutFlux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v' _ => ?_
  have hs := hsel v'.1 v'.2
  have hd := hdisj v'.1 v'.2
  by_cases hp : compParent m v'.1 = v.1
  · by_cases h1 : sel₁ v'.1
    · have h2 : ¬ sel₂ v'.1 := fun h2 => hd ⟨h1, h2⟩
      have h3 : sel v'.1 := hs.2 (Or.inl h1)
      simp only [hp, h1, h2, h3, and_self, dite_true, and_false, dite_false, add_zero]
    · by_cases h2 : sel₂ v'.1
      · have h3 : sel v'.1 := hs.2 (Or.inr h2)
        simp only [hp, h1, h2, h3, and_self, dite_true, and_false, dite_false, zero_add]
      · have h3 : ¬ sel v'.1 := fun h3 => (hs.1 h3).elim h1 h2
        simp only [hp, h1, h2, h3, and_false, dite_false, add_zero]
  · simp only [hp, false_and, dite_false, add_zero]

/-! ### The sum of two realized fluxes -/

section Mass

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem mass_neg (k : ℕ) (ρ : ℝ) (π : ι → ℝ)
    (A : ∀ v : ι, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) :
    covTruncMassCLM h k ρ π (fun v => -A v) = -covTruncMassCLM h k ρ π A := by
  rw [← ContinuousLinearMap.map_neg]
  rfl

theorem fluxMassLe_neg' (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (I : Set ℝ) (Y : ℝ) (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hm : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    FluxMassLe (K := fun _ => k) ν ρ π I (fun v t => -G v t) Y := by
  refine ⟨fun v => (hm.1 v).neg, ?_⟩
  have hb := hm.2
  rw [covTrunc_mass_integral k ρ π hπ I (fun v s => -G v s)]
  rw [covTrunc_mass_integral k ρ π hπ I G] at hb
  have hpt : ∀ s, covTruncMassCLM h k ρ π (fun v => -G v s) =
      -covTruncMassCLM h k ρ π (fun v => G v s) := fun s =>
    mass_neg k ρ π (fun v => G v s)
  simpa only [hpt, norm_neg] using hb

theorem fluxMassLe_add (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    (I : Set ℝ) (Y₁ Y₂ : ℝ) (G₁ G₂ : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hm₁ : FluxMassLe (K := fun _ => k) ν ρ π I G₁ Y₁)
    (hm₂ : FluxMassLe (K := fun _ => k) ν ρ π I G₂ Y₂) :
    FluxMassLe (K := fun _ => k) ν ρ π I (fun v t => G₁ v t + G₂ v t) (Y₁ + Y₂) := by
  have h := covTrunc_fluxMassLe_sub k ν ρ π hν hπ I Y₁ Y₂ G₁ (fun v t => -G₂ v t) hm₁
    (fluxMassLe_neg' k ν ρ π hπ I Y₂ G₂ hm₂)
  have e : (fun v t => G₁ v t - -G₂ v t) = fun v t => G₁ v t + G₂ v t := by
    funext v t
    exact sub_neg_eq_add _ _
  rwa [e] at h

end Mass

/-- **Two realized fluxes add, and the bounds add** (the companion of `covTruncSub`). -/
theorem hasFluxBound_add' {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (I : Set ℝ) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν)
    (hπ : ∀ v, 0 < π v) (F₁ F₂ : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (Y₁ Y₂ : ℝ) (h₁ : HasFluxBound k I ν ρ π F₁ Y₁) (h₂ : HasFluxBound k I ν ρ π F₂ Y₂) :
    HasFluxBound k I ν ρ π (fun v t x => F₁ v t x + F₂ v t x) (Y₁ + Y₂) := by
  obtain ⟨G₁, hr₁, hm₁⟩ := h₁
  obtain ⟨G₂, hr₂, hm₂⟩ := h₂
  refine ⟨fun v t => G₁ v t + G₂ v t, ?_, fluxMassLe_add k ν ρ π hν hπ I Y₁ Y₂ G₁ G₂ hm₁ hm₂⟩
  intro v t ht
  filter_upwards [AVRegularity.CycleComparison.Coarse.jet_add_ae (G₁ v t) (G₂ v t),
    hr₁ v t ht, hr₂ v t ht] with x hx h1 h2
  rw [hx, h1, h2]

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The size ledger of the matrix `𝖩_m(t) - κ_{m-1} I`** of the gradient term, at
any stage of a band chain (not only at a terminal context).

`covGradN_ledger`: for `Λ ≥ Λ₀` there is `C_N ≥ 0` (depending on the construction constants
only) such that for every `OCData` of the band chain and every level `2 ≤ m ≤ M`,
`∑_{ij} |N_t(i,j)| ≤ C_N κ_{m-1}` for all `t`, and `t ↦ N_t` is continuous
(`covGradN_entry_le`, `covGradN_continuous` and the clause `ν + ε^{2(1+α)}/ν ≤ C B` of
`bandChain_uniform_ledger`).

In the limit `ε_m → 0`: `𝖩_m → ν I` and `ν ≤ B`, so `N → (ν - B) I`, of size `≤ B`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The size ledger of `N_t = 𝖩_m(t) - κ_{m-1} I`** along a band chain. -/
theorem covGradN_ledger {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ Cn : ℝ, 0 ≤ Cn ∧
      ∀ (D : OCData) (M m : ℕ), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
        IsOCBandChain α q Λ ζ M D.κ → 2 ≤ m → m ≤ M →
        (∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN D m t jl.1 jl.2| ≤ Cn * D.κ (m - 1)) ∧
          Continuous (covGradN D m) := by
  obtain ⟨Cl, hCl1, Λ₂, hΛ₂, hled⟩ := CycleReference.bandChain_uniform_ledger hα0 hα1 hs0 hs1
    hq hζ
  refine ⟨Λ₂, hΛ₂, fun Λ hΛ => ⟨4 * (Cl + 1), by linarith, ?_⟩⟩
  intro D M m hDα hDq hDΛ hDζ hband hm2 hmM
  have hΛ128 : 128 ≤ Λ := hΛ₂.trans hΛ
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < D.κ (m - 1) :=
    CycleReference.bandChain_pos hΛ1 hζ hband (le_trans (Nat.sub_le _ _) hmM)
  have hνm : 0 < D.κ m := CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hl4 := ((hled Λ hΛ M (by omega) D.κ hband).2 m hm2 hmM (D.κ m) (D.κ (m - 1))
    rfl rfl).2.2.2.1
  have hl4' : D.κ m + ocEpsilon D.q D.Λ m ^ (2 * (1 + D.α)) / D.κ m ≤ Cl * D.κ (m - 1) := by
    rw [hDα, hDq, hDΛ]; exact hl4
  have hΛD : 1 ≤ D.Λ := hDΛ ▸ hΛ1
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hε : 0 ≤ ocEpsilon D.q D.Λ m := by
    rw [hDq, hDΛ]; exact (Scales.epsilon_basic (m := m) hq.1 hΛ128).1.le
  refine ⟨fun t => ?_, covGradN_continuous hΛD hζD hνm⟩
  have hent := fun i j => covGradN_entry_le hΛD hζD hνm hl4' hν.le hε t i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have := hent 0 0
  have := hent 0 1
  have := hent 1 0
  have := hent 1 1
  nlinarith

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The lift step of the fine tail: the fine lift step at a frame, statement.**

`FineLiftAt' F law c₀ cr Ck Ain Yw K` says: at the order `K` (the piece is used with
`K = D_* + L_f`), the frame's own lifted field has a representative `Û` of order `K + 1` with
`FieldRealForm` (strong measurability and `L²` in time, the value clause, the classical order)
and `FieldGradEnergyForm` at `ρ_⋆`, with constant `Ck * Ck`, i.e. `FrameFineLiftAt`.

Inputs, all named hypotheses:
* `hFL`: `FullLiftClauses` at the order `K + 1` (the full-lift bound, taken
  as a hypothesis);
* `hhigh`: the retained solution at the order `N_aux + 3` (a conjunct of the proved retained
  production bundle; `retained_high_and_reps` turns it into `Yhi` and the classical
  representatives);
* `hmeas`: joint measurability, at the order `0` only, of `(t, x) ↦ F.uh t x v` on the window
  (in place of `NativeRepresentatives F`). It gives the strong
  measurability of `t ↦ Û(t) ∈ TorusHk (K + 1)` by weak measurability
  (`CycleComparison.Coarse.aestronglyMeasurable_of_weak`: the pairings of the value of `Û(t)` with
  smooth periodic tests are measurable in `t` by Fubini; the value of `Û(t)` is `F.uh t` a.e.
  by the value clause; `TorusHk` is separable and the value map is injective), so no derivative of
  `F.uh` in time or space is needed;
* `hsrc`: the native slot lifts and their order reserve at the order `K + 1`
  (`LiftSource`), for the identification of the frame's `CcT` with the native coefficients
  (`nativeStageLiftFamily_coefficients_unique`) and the existence at `K + 1`
  (`native_liftedFieldW_exists_of_prepared_classical_data`, with the frame's `PZ`, `aRep`);
* the menu is the plain one (`lenFactor = 1`, `anchor = 0`, true for `succMenu`), the level is `m`,
  and the positivity facts of the scales.

The order: `K + 1 + N + 2p ≤ N_aux` (the schedule pays `D_* + L_f + N + 2p + 1 ≤ N_aux`). The
frame's classical order of `aRep` is `N_aux - 2p`, one short of `K + 2 + N`; the missing order
comes from `Yhi`.

The case `Ain < 0` is excluded by `0 ≤ Ain` (otherwise `FullLiftClauses` forces energy `0` and
the conclusion fails). For `Ck ≤ 0` the energy is `0` and `0 ≤ Ck * Ck * Ain` holds; `L_f = 0`
(`K = D_*`) has the same proof; for an empty family all clauses are vacuous and the energy is `0`;
for `tp = tf` the integrals over a point vanish and the clauses are pointwise; for `Ain = 0` the
energy bound `0` forces `Û = 0` on the window. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Residual.Presentation.Cascade
open AVRegularity AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The native slot lifts of the stage of the frame, with the order reserve of the lifted field
of order `K + 1` whose gradient representative has order `K + 2`. -/
def LiftSource (F : Frame D hr Dm b j₀) (law : BirthLaw) (K : ℕ) : Prop :=
  1 ≤ F.G.level ∧ 1 ≤ D.Λ ∧ IsFastProfile D.ζ ∧
  IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ ∧
  IsTorusCompatible F.G.fam F.G.actual (D.eps (F.G.level - 1)) ∧
  ∃ (Kp kp Lp : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S : ℝ)
    (slotLifts : ∀ slot : OddSlot,
      NativeSlotLift F.G slot (F.G.mass law) F.depth F.N Kp kp Lp CG Cw Cj S),
    (∀ slot : OddSlot, K + 2 + (F.N + (slotLifts slot).cap) ≤
      Kp + 4 * (F.depth + 1) * (F.N + (slotLifts slot).cap) ^ 2) ∧
    K + 2 ≤ max kp (Lp + 2)

/-- **The lift step of the fine tail at a frame.** -/
def FineLiftAt' (F : Frame D hr Dm b j₀) (law : BirthLaw) (c₀ cr Ck Ain : ℝ)
    (Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)) (K : ℕ) : Prop :=
  ∀ (hk : K + 1 + F.N + 2 * F.p ≤ F.Naux),
    F.Mn.lenFactor = 1 → F.Mn.anchor = 0 → F.G.level = F.m →
    0 ≤ Ain → (∀ v, 0 < F.G.mass law v) → 0 < rhoStar D c₀ F.m → 0 < D.κ F.m →
    (∀ v : CompIn F.G.comps, Measurable
      (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc F.tp F.tf} => F.uh z.1.1 z.1.2 v)) →
    AVRegularity.Construction.Preservation.Assembly.RetainedHigherValuesStatement
      F.Gr F.Naux F.tp F.tf F.Y →
    LiftSource F law K →
    FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ (K + 1) hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw →
    FrameFineLiftAt F law c₀ K Ain (Ck * Ck)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The partition step, the gluing factor of the partition bound against the third term of the
bill**
(cascade side of the bill residual).

`gateLevel`: at a level `2 ≤ m ≤ M` of a band chain, above the separation threshold `Λ₀`, for
a window `[t_p, t_p + T_obs]` with `0 < T_obs ≤ T₀` and a rate `c_g > 0` of the partition bound,
there is one constant `K_c` (from `(α, s, q, ζ, Λ)`, `T₀`, `c_g`) with
`#pulses · e^{-c_g τ/ℓ²} · ℓ √(1/τ) ≤ K_c · ℓ √((1 + T_obs/τ)/τ) e^{-cτ/ℓ²}`
for every `c ≤ c_g/2`: the count of the observed pulses is absorbed by half of the quiet
exponential (`card_exp_le_of_scaleLaws`), the other half dominates the exponential of the
gluing term of `succReconBill`.

With no observed pulse the left side is `0`, and for `c ≤ 0` the exponential on the right is at
least one. -/

@[expose] public section

open AVenhance AVRegularity

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The partition step, the gluing factor at a level.** -/
theorem gateLevel {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (T₀ cg : ℝ), 0 < cg →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ tp Tobs : ℝ, 0 < Tobs → Tobs ≤ T₀ → ∀ c : ℝ, c ≤ cg / 2 →
        ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
            Real.exp (-(cg * ocTau α q Λ m / ocEll q Λ m (κ m) ^ 2)) *
            (ocEll q Λ m (κ m) * Real.sqrt (1 / ocTau α q Λ m)) ≤
          Kc * (ocEll q Λ m (κ m) *
            Real.sqrt ((1 + Tobs / ocTau α q Λ m) / ocTau α q Λ m) *
            Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m (κ m) ^ 2))) := by
  obtain ⟨C, hC1, Λ₁, hΛ₁, hlaw⟩ := AVRegularity.CycleComparison.Assembly.scale_laws α s hα0 hα1
    hs0 hs1 q hq ζ hζ
  refine ⟨Λ₁, hΛ₁, fun Λ hΛ T₀ cg hcg => ?_⟩
  have h128 : 128 ≤ Λ := le_trans hΛ₁ hΛ
  obtain ⟨Kc, hKc0, hcard⟩ := CycleComparison.Reconstruction.card_exp_le_of_scaleLaws α s hα0 hα1
    hs0 hs1 q hq Λ h128 C hC1 0 T₀ (cg / 2) (half_pos hcg)
  refine ⟨Kc, hKc0, fun M κ hband m hm hmM tp Tobs hTobs hT c hc => ?_⟩
  have hlaws := hlaw Λ hΛ M κ hband m hm hmM (κ m) (κ (m - 1)) rfl rfl
  have hq1 : 1 < q := hq.1
  have hΛ1 : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ1
  have he : 0 < ocEpsilon q Λ m := Applications.eps_pos hq1 h128
  have hℓ : 0 < ocEll q Λ m (κ m) := div_pos he (Real.sqrt_pos.2 hlaws.ν_pos)
  have hℓ2 : 0 < ocEll q Λ m (κ m) ^ 2 := pow_pos hℓ 2
  have hcard' := hcard m (κ m) (κ (m - 1)) hlaws tp Tobs hTobs (by simpa using hT)
  set P : ℝ := ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) with hP
  set ℓ := ocEll q Λ m (κ m) with hℓdef
  set τ := ocTau α q Λ m with hτdef
  have hx : 0 ≤ τ / ℓ ^ 2 := div_nonneg hτ.le hℓ2.le
  have hexp : Real.exp (-(cg * τ / ℓ ^ 2)) =
      Real.exp (-(cg / 2 * τ / ℓ ^ 2)) * Real.exp (-(cg / 2 * τ / ℓ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle : Real.exp (-(cg / 2 * τ / ℓ ^ 2)) ≤ Real.exp (-(c * τ / ℓ ^ 2)) := by
    apply Real.exp_le_exp.2
    have : c * τ / ℓ ^ 2 ≤ cg / 2 * τ / ℓ ^ 2 := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc hx
    linarith
  have hsq : Real.sqrt (1 / τ) ≤ Real.sqrt ((1 + Tobs / τ) / τ) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by have := div_nonneg hTobs.le hτ.le; linarith) hτ.le
  have h0 : 0 ≤ P * Real.exp (-(cg / 2 * τ / ℓ ^ 2)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  calc P * Real.exp (-(cg * τ / ℓ ^ 2)) * (ℓ * Real.sqrt (1 / τ))
      = (P * Real.exp (-(cg / 2 * τ / ℓ ^ 2))) * (Real.exp (-(cg / 2 * τ / ℓ ^ 2)) *
          (ℓ * Real.sqrt (1 / τ))) := by rw [hexp]; ring
    _ ≤ Kc * (Real.exp (-(c * τ / ℓ ^ 2)) * (ℓ * Real.sqrt ((1 + Tobs / τ) / τ))) := by
        apply mul_le_mul hcard' _ (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg hℓ.le (Real.sqrt_nonneg _))) hKc0
        exact mul_le_mul hle (mul_le_mul_of_nonneg_left hsq hℓ.le)
          (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    _ = _ := by ring

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The energy step: the energies at a cascade frame, from the clauses of the full-lift bound.**

At a frame `F` and an order `k` with `k + N + 2p ≤ N_aux` (each statement carries its own
order hypothesis; the constant `C_k` is whatever `FullLiftClauses` carries):

* `readoutEnergy_le`: `readoutEnergy … ≤ C_k A_in` for `w = 1` and `w = marker`, from
  `FullLiftClauses` (its existence conjunct provides the lifted field that the universal conjunct
  asks for; the readout energy does not depend on it);
* `Z_strongEnergy_le`: the strong energy of `Z = 𝖱Y` (truncated to the order `L = k + N + 2p`)
  at the radius `ρ = rhoEnh D c_r m`, in the weights `π = mass`;
* `Z_strongEnergy_liftLength_le`: the same at the lift length `ℓ = liftLength D m = ρ/c_r`,
  with the factor `c_r^{-L}` (for `c_r ≤ 1`);
* `covCost_le`: the cost `C` of the covariance polynomial, from the size form of the covariance
  primitive; with it the strong energy up to the order `m ≤ K'` of `P_pZ` (the frame's `PZ`
  truncated to the order `K' + 1`) is at most `C` times that of `Z`.

The retained pair `(Y, Y_w)` enters through `RetainedPair` (the second and third conjuncts of
`IsKernelWeakSolutionTorus`: `Y_w ∈ L²(I)` and `truncate Y_w = Y` a.e.), which is a consequence of
`IsRegSolution` (`retainedPair_of_isRegSolution`).

For `A_in = 0` every bound is `0` (the right sides are `ofReal 0`), and for an empty family all
energies are `0` (empty sums). For `t_p = t_f` or `t_f < t_p` the suprema over the window are
over a point or the empty set; the statements are not weakened by it. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The data -/

/-- The truncation of the readout `Z = 𝖱Y` to the order `K ≤ N_aux`. -/
def ReadoutZ (F : Frame D hr Dm b j₀) {K : ℕ} (hK : K ≤ F.Naux) :
    ∀ v : CompIn F.G.comps, ℝ → TorusHk K (hr v.1.root) :=
  fun v t => truncateTorusHk hK
    (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)

/-- The truncation of the gradient carrier of the readout, of the order `K + 1`. -/
def ReadoutZw (F : Frame D hr Dm b j₀) (Yw : ∀ v : CompIn F.Gr.comps, ℝ →
    TorusHk (F.Naux + 1) (hr v.1.root)) {K : ℕ} (hK : K ≤ F.Naux) :
    ∀ v : CompIn F.G.comps, ℝ → TorusHk (K + 1) (hr v.1.root) :=
  fun v t => truncateTorusHk (Nat.succ_le_succ hK)
    (succReadout F.m (D.eps (F.m - 1)) F.η₀ (F.Naux + 1) (fun v' => Yw v' t) v)

/-- The retained pair `(Y, Y_w)`: `Y_w ∈ L²(I)` and `truncate Y_w = Y` almost everywhere on the
window (conjuncts 2 and 3 of `IsKernelWeakSolutionTorus`). -/
def RetainedPair (F : Frame D hr Dm b j₀) (Yw : ∀ v : CompIn F.Gr.comps, ℝ →
    TorusHk (F.Naux + 1) (hr v.1.root)) : Prop :=
  (∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
  ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc F.tp F.tf)),
    truncateTorusHk (Nat.le_succ F.Naux) (Yw v t) = F.Y v t

/-- A regular solution of the retained system gives the retained pair. -/
theorem retainedPair_of_isRegSolution (F : Frame D hr Dm b j₀)
    {P : ProvParams} {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
    {ν : ℝ} {bv : ℝ → Vec 2 → Vec 2}
    {Y0 : ∀ v : CompIn F.Gr.comps, TorusHk F.Naux (hr v.1.root)}
    {g₁ : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk F.Naux (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {g₂ : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk F.Naux (hr v.1.root)}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    {Yk : ∀ v u (_ : F.Gr.fam.Γ v u), ℝ → TorusHk (F.Naux + Dm - 1) (hr u.1.root)}
    (h : F.Gr.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv F.Naux F.tp F.tf Y0 g₁ g₂ F.Y Yw Yk) :
    RetainedPair F Yw :=
  ⟨h.2.1, h.2.2.1⟩

/-! ### The readout energy -/

/-- **The energy step, the readout energy**: `readoutEnergy ≤ C_k A_in` at the radius `ρ = rhoEnh D c_r m`,
for `w = 1` and `w = marker`, from `FullLiftClauses`. -/
theorem readoutEnergy_le (F : Frame D hr Dm b j₀) (law : BirthLaw) {k : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) {c₀ cr Ck Ain : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    {w : CompIn F.G.comps → ℝ} (hw : w = (fun _ => 1) ∨ w = F.G.marker law) :
    readoutEnergy law F.G F.Gr F.m F.η₀ (rhoEnh D cr F.m) hk w F.tp F.tf F.Y Yw ≤
      ENNReal.ofReal (Ck * Ain) := by
  obtain ⟨⟨CcT, PZ, aRep, û, ŵ, hL⟩, hall⟩ := cl
  exact (hall CcT PZ aRep û ŵ hL w hw).2

/-- **The energy step, the strong energy of `Z`** at the radius `ρ = rhoEnh D c_r m` in the weights `π = mass`,
at the order `L = k + N + 2p`. -/
theorem Z_strongEnergy_le (F : Frame D hr Dm b j₀) (law : BirthLaw) {k : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) {c₀ cr Ck Ain : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw) :
    strongEnergy (rhoEnh D cr F.m) (D.κ (F.m - 1)) (F.G.mass law) F.tp F.tf
      (ReadoutZ F hk) (ReadoutZw F Yw hk) ≤ ENNReal.ofReal (Ck * Ain) := by
  have h := readoutEnergy_le F law hk cl (w := fun _ => 1) (Or.inl rfl)
  have e : (fun v => F.G.mass law v / (fun _ : CompIn F.G.comps => (1 : ℝ)) v ^ 2) =
      F.G.mass law := by
    funext v
    simp
  unfold readoutEnergy at h
  rw [e] at h
  exact h

/-! ### The gradient carrier -/

/-- The gradient carrier of the readout is square integrable in time. -/
theorem ReadoutZw_memLp (F : Frame D hr Dm b j₀)
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (hp : RetainedPair F Yw) {K : ℕ} (hK : K ≤ F.Naux) (v : CompIn F.G.comps) :
    MemLp (ReadoutZw F Yw hK v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
  have h1 := AVRegularity.Construction.Preservation.FullLift.memLp_succReadout (S := F.G.comps) (S' := F.Gr.comps) F.m (D.eps (F.m - 1)) F.η₀
    (u := Yw) hp.1 v
  exact memLp_truncate (Nat.succ_le_succ hK) h1

/-- Truncations compose (generic in the target). -/
theorem trunc_trunc_swap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K N : ℕ} (hK : K ≤ N)
    (x : TorusHk (N + 1) E) :
    truncateTorusHk (Nat.le_succ K) (truncateTorusHk (Nat.succ_le_succ hK) x) =
      truncateTorusHk hK (truncateTorusHk (Nat.le_succ N) x) := rfl

/-- The truncation of the gradient carrier of the readout is the readout, almost everywhere. -/
theorem ReadoutZw_ae (F : Frame D hr Dm b j₀)
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (hp : RetainedPair F Yw) {K : ℕ} (hK : K ≤ F.Naux) (v : CompIn F.G.comps) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc F.tp F.tf)),
      truncateTorusHk (Nat.le_succ K) (ReadoutZw F Yw hK v t) = ReadoutZ F hK v t := by
  have hall : ∀ᵐ t ∂(volume.restrict (Set.Icc F.tp F.tf)), ∀ v' : CompIn F.Gr.comps,
      truncateTorusHk (Nat.le_succ F.Naux) (Yw v' t) = F.Y v' t :=
    Filter.eventually_all.2 hp.2
  filter_upwards [hall] with t ht
  have e1 := trunc_trunc_swap hK
    (succReadout F.m (D.eps (F.m - 1)) F.η₀ (F.Naux + 1) (fun v' => Yw v' t) v)
  have e2 := AVRegularity.Construction.Preservation.FullLift.truncate_succReadout (Nat.le_succ F.Naux) F.m (D.eps (F.m - 1)) F.η₀
    (fun v' => Yw v' t) v
  have e3 := congrArg (fun X => succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux X v)
    (funext ht : (fun v' => truncateTorusHk (Nat.le_succ F.Naux) (Yw v' t)) =
      fun v' => F.Y v' t)
  exact e1.trans (congrArg (truncateTorusHk hK) (e2.trans e3))

/-! ### The change of radius -/

/-- The enhanced radius is `c_r` times the lift length: `c_r⁻¹ ρ = ℓ`. -/
theorem inv_mul_rhoEnh (D : OCData) {cr : ℝ} (hcr : 0 < cr) (m : ℕ) :
    cr⁻¹ * rhoEnh D cr m = liftLength D m := by
  unfold rhoEnh liftLength
  rw [← mul_assoc, inv_mul_cancel₀ hcr.ne', one_mul]

/-- **The energy step, the strong energy of `Z` at the lift length** `ℓ = ρ/c_r` (`c_r ≤ 1`): the factor of the
change of radius is `c_r^{-L}`, `L = k + N + 2p`. -/
theorem Z_strongEnergy_liftLength_le (F : Frame D hr Dm b j₀) (law : BirthLaw) {k : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) {c₀ cr Ck Ain : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hπ : ∀ v, 0 < F.G.mass law v) :
    strongEnergy (liftLength D F.m) (D.κ (F.m - 1)) (F.G.mass law) F.tp F.tf
      (ReadoutZ F hk) (ReadoutZw F Yw hk) ≤
      ENNReal.ofReal ((cr⁻¹) ^ (k + F.N + 2 * F.p)) * ENNReal.ofReal (Ck * Ain) := by
  have hA : 1 ≤ cr⁻¹ := (one_le_inv₀ hcr).mpr hcr1
  have h := strongEnergy_mul_radius_le hA (rhoEnh D cr F.m) (D.κ (F.m - 1)) F.tp F.tf
    (F.G.mass law) hπ (ReadoutZ F hk) (ReadoutZw F Yw hk)
    (fun i => (integrable_gradFactorialNormSq_torus
      (ReadoutZw_memLp F hp hk i)).aemeasurable.ennreal_ofReal)
  rw [inv_mul_rhoEnh D hcr] at h
  exact h.trans (mul_le_mul' le_rfl (Z_strongEnergy_le F law hk cl))

/-! ### The covariance cost -/

/-- The cost of the covariance polynomial at the order `K`, for `ω ≤ 1`:
`∑_{l ≤ p} K^{2l}/l!`. -/
def CovCost (K p : ℕ) : ℝ := covPolyConst (((K : ℝ)) ^ 2) p

theorem covCost_nonneg (K p : ℕ) : 0 ≤ CovCost K p := by
  unfold CovCost covPolyConst
  exact Finset.sum_nonneg fun l _ => by positivity

/-- **The covariance cost from the size form**: `covBound 𝖧 ≤ ωρ²`, `ω ≤ 1` give
`covPolyConst (fbCovConst ρ 𝖧 K) p ≤ ∑_{l ≤ p} K^{2l}/l!`. -/
theorem covCost_le {Mn : SuccMenu} {m : ℕ} {tp tf ρ ω : ℝ} (hρ : 0 < ρ)
    (hS : CovSizeForm Mn D m tp tf ρ ω) (K p : ℕ) :
    ∀ t ∈ Set.Icc tp tf,
      covPolyConst (fbCovConst ρ (menuCovPrimitive D Mn m t) K) p ≤ CovCost K p := by
  intro t ht
  obtain ⟨hb, hω0, hω1, -⟩ := hS
  have h1 : fbCovConst ρ (menuCovPrimitive D Mn m t) K ≤ ((K : ℝ)) ^ 2 := by
    unfold fbCovConst
    calc covBound (menuCovPrimitive D Mn m t) * ((K : ℝ) / ρ) ^ 2
        ≤ (ω * ρ ^ 2) * ((K : ℝ) / ρ) ^ 2 :=
          mul_le_mul_of_nonneg_right (hb t ht) (sq_nonneg _)
      _ = ω * (K : ℝ) ^ 2 := by field_simp
      _ ≤ 1 * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hω1 (sq_nonneg _)
      _ = (K : ℝ) ^ 2 := one_mul _
  have h0 := fbCovConst_nonneg hρ (menuCovPrimitive D Mn m t) K
  unfold CovCost covPolyConst
  exact Finset.sum_le_sum fun l _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h1 l) (Nat.cast_nonneg _)

/-! ### The covariance step: `P_pZ` -/

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The error side of the producer: statements** (cascade side of the bill residual: the initial
error and the error energy).

Both statements are made at the context `c : BillCtx …` (module `BillCtx`), with their
inputs as named hypotheses. Nothing here opens the prefix.

* `InitialValueConclusion c U CcT PZ aRep û`: the conclusion of the proved
  `successor_initial_value` at the context (a covariance image `Qh` of `P_reg f` and the splitting
  of `U(t_p) - û(t_p)` in three differences).
* `CellVanish c CcT`: the positive lifts of every observed slot with nonvanishing cutoff at
  `t_p` vanish at the cell time of `t_p` (the conclusion of `qz_cc_vanish`; the quiet entrance
  under the quiet margin).
* `FilterEstimate c Cfil ω PZ`: the covariance-filter estimate `(P_p Q_p - I) h`.
* `InitialErrorStatement c Cfil ω`: the initial error `U(t_p) - û(t_p)` in the
  `L²_π` norm at radius `1`.
* `StageScale c`: the scale facts of the stage at order `0` used by the forced energy.
* `ErrorEnergyStatement' c`: from a reconstruction of the lifted field with forcing
  `(R, q)` and the initial error bound `E₀`, the last clause of `ComparisonClauses`.

For `Ain = 0` one has `f = 0` in the weights of the context and the right side is `0`. For an
empty component family every norm is `0`, and for zero residual the error is the propagated
initial error, with constant `2 (3 + 8 W₀)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- The conclusion of `successor_initial_value` at the context, for a regularized solution `U` of
the incoming system from `s₀` and a lifted field `û` (with `CcT`, `PZ`, `aRep`). -/
def InitialValueConclusion
    (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)) : Prop :=
  ∃ Qh : ∀ v : CompIn c.G.comps, TorusHk Naux (hr v.1.root),
    (∀ v, IsCovImage (covPolyQ (covPrimitive c.D c.m c.tp) p) (c.Preg c.f v) (Qh v)) ∧
    (∀ v, IsCovImage (covPolyP (covPrimitive c.D c.m c.tp) p) (Qh v) (PZ v c.tp)) ∧
    ∀ v, U v c.tp - û v c.tp =
      (U v c.tp - truncateTorusHk (Nat.zero_le Nout) (c.Preg c.f v)) -
        (truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp) -
          truncateTorusHk (Nat.zero_le Nout) (c.Preg c.f v)) -
        (û v c.tp - truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp))

/-- The covariance-filter estimate `‖P_p Q_p h - h‖_{L²_π} ≤ C_fil ω^{p+1} ‖h‖_{ρ_enh}` for
`h = P_reg f` (`Q_p h = Qh`, `P_p Q_p h = P Z(t_p)`), with the filter scale `ω`. -/
def FilterEstimate (Cfil ω : ℝ)
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root)) : Prop :=
  ∀ Qh : ∀ v : CompIn c.G.comps, TorusHk Naux (hr v.1.root),
    (∀ v, IsCovImage (covPolyQ (covPrimitive c.D c.m c.tp) p) (c.Preg c.f v) (Qh v)) →
    (∀ v, IsCovImage (covPolyP (covPrimitive c.D c.m c.tp) p) (Qh v) (PZ v c.tp)) →
    weightedNorm 1 (c.G.mass c.law) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp) -
          truncateTorusHk (Nat.zero_le Nout) (c.Preg c.f v)) ≤
      Cfil * ω ^ (p + 1) *
        weightedNorm (rhoEnh c.D kI.cr c.m) (c.G.mass c.law) (fun _ => 1) (c.Preg c.f)

/-- The positive lifts of every observed slot with nonvanishing cutoff at `t_p` vanish at the cell
time of `t_p` (the conclusion of `qz_cc_vanish` at the context: the quiet
entrance, for `t_p` inside the quiet margin). -/
def CellVanish
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root)) : Prop :=
  ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ c.m c.tp c.tp,
    ocCutoff c.D.α c.D.q c.D.Λ c.m k c.tp ≠ 0 →
    c.tp / c.D.cellScaleSq c.m ∈ Set.Icc (c.D.slotStart c.m k / c.D.cellScaleSq c.m)
        ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ c.m) / c.D.cellScaleSq c.m) ∧
      ∀ hh ≤ succSchedR r₀ J H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
        CcT k hh n m α (c.tp / c.D.cellScaleSq c.m) X z v u = 0

/-- The positivity facts of the scales at the level `m` used by the quiet entrance (they hold from
a level `m_*` on: `E_m > 0`, `κ_m > 0`, `κ_{m-1} > 0`, `Λ > 0`). -/
structure QuietScale : Prop where
  hτ : 0 < ocTau c.D.α c.D.q c.D.Λ c.m
  hcs : c.D.cellScaleSq c.m ≠ 0
  hρ : liftLength c.D c.m ≠ 0
  hπ : ∀ v, 0 < c.G.mass c.law v

/-- **The initial error.** At the context, for a regularized solution `U` of the incoming
system from `s₀` and a lifted field `û` of the retained solution (`IsLiftedField`), whose positive
lifts vanish at the cell time of `t_p` (the quiet margin), with the initial value statement and the
covariance-filter estimate as hypotheses:
`‖U(t_p) - û(t_p)‖_{L²_π} ≤ (C_Q E^Q + C_fil C_Q ω^{p+1}) ‖f‖_{L²_π}`. -/
def InitialErrorStatement (Cfil ω : ℝ) : Prop :=
  QuietScale c → 0 ≤ Cfil → 0 ≤ ω →
  ∀ (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
    c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
      U Uw Uk →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
    IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û →
    CellVanish c CcT →
    InitialValueConclusion c U PZ û →
    FilterEstimate c Cfil ω PZ →
    weightedNorm 1 (c.G.mass c.law) (fun _ => 1) (fun v => U v c.tp - û v c.tp) ≤
      (CQ * c.D.eps (c.m - 1) ^ Q + Cfil * ω ^ (p + 1) * CQ) *
        weightedNorm 1 (c.G.mass c.law) (fun _ => 1) c.f

/-- The constant of the forced energy at order `0`: `2 (3 + 8 W₀)`, the factor `2` for the two
terms of `obsErrorNorm`. -/
def ErrConst : ℝ := 2 * (3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0)

/-- **The scale facts of the stage at order `0`** used by the forced energy
(`stage_forced_energy` with `n = 0`: no drift jets are asked, the radius is
`min (rhoStar) (1/2048)`). Each is a smallness or positivity statement at the level `m`; they hold
from a level `m_*` on. -/
structure StageScale : Prop where
  hres0 : ∀ v : CompIn c.G.comps, 0 ≤ compReserve kI v.1
  hq : 1 < c.D.q
  hΛ : 128 ≤ c.D.Λ
  hi : 1 ≤ c.G.level
  hj : j₀ ≤ c.G.level
  hb : 0 < bw
  hε : 0 < c.D.eps (c.G.level - 1)
  hν : 0 < c.D.kap c.G.level
  hR : 0 < rhoStar c.D kI.c₀ c.G.level
  hRε : rhoStar c.D kI.c₀ c.G.level ≤ c.D.eps (c.G.level - 1)
  hD : 2 ≤ succSchedD D₀ N p (H + 1)
  hθ : CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe) ≤ 1 / 8

/-- **The error energy.** At the context, for the regularized solution `U` of the incoming
system from `s₀` and a reconstruction `(û, ŵ, ŷ)` of the lifted field with forcing `(R, q)` on
`[t_p, t_f]` (the hypothesis: the conclusion of `FrameResidualBoundAt` after plain-to-kernel),
with residual norm at most `resBound` and initial error at most `E₀`, the last clause of
`ComparisonClauses`: `obsErrorNorm ≤ 2 (3 + 8 W₀) (E₀ + max 0 resBound)`. -/
def ErrorEnergyStatement' : Prop :=
  StageScale c →
  ∀ (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
    c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
      U Uw Uk →
  ∀ (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (ŵ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (ŷ : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (Rres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
    c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf (fun v => û v c.tp) Rres qres û ŵ ŷ →
    (∀ v, AEStronglyMeasurable (Rres v) (volume.restrict (Set.Icc c.tp c.tf))) →
    (∀ v, AEStronglyMeasurable (qres v) (volume.restrict (Set.Icc c.tp c.tf))) →
  ∀ (resBound E₀ : ℝ),
    residualNorm (c.D.κ c.m) (c.G.mass c.law) (Set.Icc c.tp c.tf)
        (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
        (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤ ENNReal.ofReal resBound →
    weightedNorm 1 (c.G.mass c.law) (fun _ => 1) (fun v => U v c.tp - û v c.tp) ≤ E₀ →
    obsErrorNorm (c.D.κ c.m) (c.G.mass c.law) (fun _ => 0) c.tp c.tf (fun v t => U v t - û v t)
        (fun v t => Uw v t - ŵ v t) ≤
      ENNReal.ofReal (ErrConst * (E₀ + max 0 resBound))

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The covariance gradient form: the gradient term of the covariance truncation at a cascade frame.**

`CovGradForm F.Mn F.G F.m F.p k_c F.aZ (F.G.mass law) t_p t_f (rhoEnh D c_r m) (C ω^p A_in)`:
the flux `T = (𝖩_m - κ_{m-1}I)∇(𝒞^p/p!)Z` has a realization of order `k_c`.

* `covGradForm_of_energy` (at a frame, all inputs named): from the strong energy of `Z`
  (`FullLiftClauses`, the energy step: `Z_strongEnergy_le`), the size form of the covariance primitive,
  and the ledger of `N_t = 𝖩_m(t) - κ_{m-1}I`. The order hypothesis is `k_c + 1 ≤ k + N`
  (so `k_c + 2p + 1 ≤ L = k + N + 2p ≤ N_aux`), the constant is
  `(p!)⁻¹ (k_c+2p)^{2p} C_N C_k`.
* `covGradForm_at_frame`: the frame statement, with `Λ₀`, `C_N`, `m_*` chosen before the frame
  (`Λ₀`, then `C_N` after `Λ`, then `m_*` after `c_r`).

For `ω = 0` and `p ≥ 1` the covariance operator vanishes and the bound is `0`; for `p = 0` the
bound is `C_N C_k A_in`, the term `N∇Z` itself; for `A_in = 0` the bound is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The gradient flux of `Z`** at a frame is realized with the mass `E/κ_{m-1}`, `E = C_k A_in`:
the first step of the covariance gradient form (`covGrad_hasFluxBound_of_strongEnergy`). -/
theorem gradZ_hasFluxBound (F : Frame D hr Dm b j₀) (law : BirthLaw) {k kc : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) (hkc : kc + 1 ≤ k + F.N) {c₀ cr Ck Ain : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (hν : 0 < D.κ (F.m - 1)) (hE : 0 ≤ Ck * Ain)
    (hπ : ∀ v, 0 < F.G.mass law v) :
    HasFluxBound (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (kc + 2 * F.p)
      (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law)
      (fun v t x => toFluxL (gradE (fun z => F.aZ t z v) x)) (Ck * Ain / D.κ (F.m - 1)) := by
  have hK1 : kc + 2 * F.p + 1 ≤ k + F.N + 2 * F.p := by omega
  refine EntryTerminal.CovGrad.covGrad_hasFluxBound_of_strongEnergy hK1 (F.G.mass law) hν hE hπ
    (ReadoutZ F hk) (ReadoutZw F Yw hk) F.aZ
    (fun v => ReadoutZw_memLp F hp hk v) (fun v => ReadoutZw_ae F hp hk v) ?_
    (Z_strongEnergy_le F law hk cl)
  intro v t ht
  have h1 : 1 ≤ F.Naux := by omega
  exact classicalRep_truncate hk (by omega) _ _ (classicalRep_order_mono _ _ (F.readout v t ht) h1)

/-- **The covariance gradient form at a frame, from the energy, the size form and the ledger.** -/
theorem covGradForm_of_energy (F : Frame D hr Dm b j₀) (law : BirthLaw) {k kc : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) (hkc : kc + 1 ≤ k + F.N) {c₀ cr Ck Ain Cn ω : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (hν : 0 < D.κ (F.m - 1)) (hρ : 0 < rhoEnh D cr F.m)
    (hπ : ∀ v, 0 < F.G.mass law v)
    (hS : CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) ω)
    (hCk : 0 ≤ Ck) (hAin : 0 ≤ Ain) (hCn : 0 ≤ Cn)
    (hN : ∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN D F.m t jl.1 jl.2| ≤ Cn * D.κ (F.m - 1))
    (hNc : Continuous (covGradN D F.m)) :
    CovGradForm F.Mn F.G F.m F.p kc F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
      (((F.p.factorial : ℝ)⁻¹) * ((((kc + 2 * F.p : ℕ) : ℝ) ^ 2 * ω) ^ F.p * Cn) * (Ck * Ain)) := by
  have hE : 0 ≤ Ck * Ain := mul_nonneg hCk hAin
  have hF := gradZ_hasFluxBound F law hk hkc cl hp hν hE hπ
  have hreg : ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 2 * F.p + 1 : ℕ) : WithTop ℕ∞) (fun z => F.aZ t z v) ∧
        IsZ2Periodic (fun z => F.aZ t z v) := by
    intro v t ht
    have h1 := F.readout v t ht
    exact ⟨h1.2.1.of_le (by exact_mod_cast (by omega : kc + 2 * F.p + 1 ≤ F.Naux)), h1.2.2.1⟩
  have haN : 0 ≤ Cn * D.κ (F.m - 1) := mul_nonneg hCn hν.le
  have hflux := EntryTerminal.CovGrad.covGrad_flux (ι := CompIn F.G.comps)
    (h := fun v => hr v.1.root) kc F.p (I := Set.Icc F.tp F.tf) measurableSet_Icc
    (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) hν hρ hπ
    (fun t => menuCovPrimitive D F.Mn F.m t) (covGradN D F.m) ω (Cn * D.κ (F.m - 1))
    hS.2.2.2 hNc.continuousOn hS.2.1 (fun t ht => hS.1 t ht) (fun t _ => hN t) haN
    (fun v t z => F.aZ t z v) _ hreg hF
  unfold CovGradForm
  refine hasFluxBound_mono_Y hflux (le_of_eq ?_)
  field_simp

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The covariance size form and the covariance gradient form with the constants before the type data of the frame.**

The statements of `covSizeForm_at_frame` and `covGradForm_at_frame` have the type
data of the frame (`hr` with its instances, `Dm`, `b`, `j₀`) as section variables, so their
constants are chosen after it. Here the type data are quantified after the constants, as the
prefix needs (`Λ₀` first, every constant before `hr`). The proofs are those of the original statements,
re-run from the generic lemmas. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter Topology
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The covariance size form with the constants before `hr`.** -/
theorem covSizeForm_at_frame {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr → ∃ mStar : ℕ, 2 ≤ mStar ∧
      ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
        [∀ r, CompleteSpace (hr r)] {Dm : ℕ} {b : ℝ} {j₀ : ℕ},
      ∀ (D : OCData) (M : ℕ), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
        IsOCBandChain α q Λ ζ M D.κ →
        ∀ (F : Frame D hr Dm b j₀), F.Mn.anchor = 0 → mStar ≤ F.m → F.m ≤ M →
          CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) (frameOmega F cr) := by
  obtain ⟨C, -, Λ₁, hΛ₁, hest⟩ := CycleReference.bandChain_covariance_estimates hα0 hα1 hs0 hs1
    hq hζ
  refine ⟨Λ₁, hΛ₁, fun Λ hΛ cr hcr => ?_⟩
  have hΛ128 : 128 ≤ Λ := hΛ₁.trans hΛ
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα0 hq
  have hev : ∀ᶠ m : ℕ in atTop,
      4 * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q / cr ^ 2 ≤ 1 := by
    have ht := (CycleReference.epsilon_parent_tendsto_zero hq.1 hΛ128).rpow_const
      (p := ocDelta α q) (Or.inr hδ.le)
    have ht2 := ((tendsto_const_nhds (x := 4 * C)).mul ht).div_const (cr ^ 2)
    rw [Real.zero_rpow hδ.ne', mul_zero, zero_div] at ht2
    exact ht2.eventually (eventually_le_nhds one_pos)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 hev
  refine ⟨max M₁ 2, le_max_right _ _, ?_⟩
  intro hr _ _ _ _ _ _ Dm b j₀ D M hDα hDq hDΛ hDζ hband F hanchor hm hmM
  have hm1 : M₁ ≤ F.m := le_trans (le_max_left _ _) hm
  have hm2 : 2 ≤ F.m := le_trans (le_max_right _ _) hm
  have hν : 0 < D.κ (F.m - 1) :=
    CycleReference.bandChain_pos hΛ1 hζ hband (le_trans (Nat.sub_le _ _) hmM)
  have hνM : 0 < D.κ F.m := CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hτ : 0 < ocTauPP α q Λ F.m := Construction.Stream.ocTauPP_pos (α := α) (q := q) hΛ1
  have hτ' : 0 < ocTauPP D.α D.q D.Λ F.m := by rw [hDα, hDq, hDΛ]; exact hτ
  have hρ : 0 < rhoEnh D cr F.m := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hτ'))
  have hent : ∀ (t : ℝ) (i j : Fin 2),
      |ocCovariance α q Λ ζ F.m (D.κ F.m) (D.κ (F.m - 1)) 0 t i j| /
        ocRh α q Λ F.m (D.κ (F.m - 1)) ^ 2 ≤ C * ocEpsilon q Λ (F.m - 1) ^ ocDelta α q :=
    fun t i j => (hest Λ hΛ M (by omega) D.κ hband F.m hm2 hmM 0 t i j).2.2.2
  have hsmall := hM₁ F.m hm1
  have hb : ∀ t ∈ Set.Icc F.tp F.tf, covBound (menuCovPrimitive D F.Mn F.m t) ≤
      rhoEnh D cr F.m ^ 2 := by
    intro t _
    refine (covBound_le_of_bandChain F.Mn hanchor cr hcr hDα hDq hDΛ hDζ hν hτ hent t).trans ?_
    exact mul_le_of_le_one_left (sq_nonneg _) hsmall
  have hc : ContinuousOn (fun t => menuCovPrimitive D F.Mn F.m t) (Set.Icc F.tp F.tf) := by
    have h := covTrunc_primitive_continuous (α := α) (q := q) (m := F.m) (Λ := Λ) (ζ := ζ) hΛ1
      hζ (ν := D.κ F.m) (B := D.κ (F.m - 1)) hνM F.Mn.anchor
    refine h.continuousOn.congr fun t _ => ?_
    simp only [menuCovPrimitive, hDα, hDq, hDΛ, hDζ]
  exact covSizeForm_of_bound F.Mn hanchor F.m F.tp F.tf _ hρ hb hc


/-- **The covariance gradient form with the constants before `hr`.** -/
theorem covGradForm_at_frame {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ cr : ℝ, 0 < cr →
      ∃ mStar : ℕ, 2 ≤ mStar ∧
      ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
        [∀ r, CompleteSpace (hr r)] {Dm : ℕ} {b : ℝ} {j₀ : ℕ},
      ∀ (D : OCData) (M : ℕ), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
        IsOCBandChain α q Λ ζ M D.κ →
        ∀ (F : Frame D hr Dm b j₀), F.Mn.anchor = 0 → mStar ≤ F.m → F.m ≤ M →
        ∀ (law : BirthLaw), (∀ v, 0 < F.G.mass law v) →
        ∀ {k kc : ℕ} (hk : k + F.N + 2 * F.p ≤ F.Naux), kc + 1 ≤ k + F.N →
        ∀ {c₀ Ck Ain : ℝ} {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)},
          FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
            F.tp F.tf Ck Ain F.Y Yw →
          RetainedPair F Yw → 0 ≤ Ck → 0 ≤ Ain →
        CovGradForm F.Mn F.G F.m F.p kc F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
          (((F.p.factorial : ℝ)⁻¹ * (((kc + 2 * F.p : ℕ) : ℝ) ^ (2 * F.p)) * Cn * Ck) *
            frameOmega F cr ^ F.p * Ain) := by
  obtain ⟨Λ₁, hΛ₁, hsize⟩ := covSizeForm_at_frame hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₂, hΛ₂, hled⟩ := covGradN_ledger hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun Λ hΛ => ?_⟩
  obtain ⟨Cn, hCn, hL⟩ := hled Λ (le_trans (le_max_right _ _) hΛ)
  refine ⟨Cn, hCn, fun cr hcr => ?_⟩
  obtain ⟨mStar, hm2, hF⟩ := hsize Λ (le_trans (le_max_left _ _) hΛ) cr hcr
  refine ⟨mStar, hm2, ?_⟩
  intro hr _ _ _ _ _ _ Dm b j₀ D M hDα hDq hDΛ hDζ hband F hanchor hm hmM law hπ k kc hk hkc c₀ Ck Ain Yw cl hp hCk hAin
  have hΛ128 : 128 ≤ Λ := le_trans hΛ₁ (le_trans (le_max_left _ _) hΛ)
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  have hm2' : 2 ≤ F.m := le_trans hm2 hm
  have hν : 0 < D.κ (F.m - 1) :=
    CycleReference.bandChain_pos hΛ1 hζ hband (le_trans (Nat.sub_le _ _) hmM)
  have hτ : 0 < ocTauPP D.α D.q D.Λ F.m := by
    rw [hDα, hDq, hDΛ]; exact Construction.Stream.ocTauPP_pos (α := α) (q := q) hΛ1
  have hρ : 0 < rhoEnh D cr F.m := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hτ))
  obtain ⟨hN, hNc⟩ := hL D M F.m hDα hDq hDΛ hDζ hband hm2' hmM
  have hS := hF D M hDα hDq hDΛ hDζ hband F hanchor hm hmM
  have h := covGradForm_of_energy F law hk hkc cl hp hν hρ hπ hS hCk hAin hCn hN hNc
  unfold CovGradForm at h ⊢
  refine hasFluxBound_mono_Y h (le_of_eq ?_)
  ring
end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
