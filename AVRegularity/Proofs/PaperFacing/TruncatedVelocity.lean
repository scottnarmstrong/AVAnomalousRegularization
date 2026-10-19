-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.CascadeCyclePassage
public import AVRegularity.Assembly.TopWiring.Summary
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Proofs.Results.Finite.TraceClosure

/-! # Regularity for the truncated velocity along the paper's route

* `paper_fresh_kernels_exist`: at the parameters `cfg`, for a band chain of terminal level `M`,
  fresh kernels exist at every birth level `1 ≤ b' < M` (from the fresh axes of the parameters).
* `paper_truncated_velocity_regularity`: the statement of `oc_finite` (`OcFiniteTargetStatement`,
  its verbatim text copy; Proposition 3.1 of the paper follows from it), proved along the proof of
  Proposition 3.1 in the paper: the entry (E1) of `paper_cascade_cycle_passage` gives the seed and
  the bound of `θ(t)` by a representation of the seed solution; the cascade of the same parameters gives that
  representation for a.e. `t`; `csNorm_trace_closure` passes to every `t`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- **Fresh kernels at the parameters `cfg`**: for a band chain of terminal level `M`, there are
fresh kernels at every birth level `1 ≤ b' < M`. -/
theorem paper_fresh_kernels_exist {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) {D : OCData}
    (hDα : D.α = P.ready.cfg.α) (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ)
    (hDζ : D.ζ = P.ready.cfg.ζ)
    (hDΦ : IsOCStreamSeq P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ D.Φ) {M : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ) :
    ∃ freshK : ℕ → KernelSpec, ∀ b', 1 ≤ b' → b' < M →
      IsFreshKernel D P.ready.cfg.kI.cr P.ready.cfg.σ₀ P.ready.cfg.nk.toPNat' b' (freshK b') := by
  classical
  have haxes := P.ready.axes D hDα hDq hDΛ hDζ hDΦ M hband
  choose H₁ H₂ hH using haxes
  let freshK (b' : ℕ) : KernelSpec := {
    width := freshWidth D P.ready.cfg.kI.cr P.ready.cfg.σ₀ b'
    order := P.ready.cfg.nk.toPNat'
    H₁ := if h : 1 ≤ b' ∧ b' < M then H₁ b' h.1 h.2 else fun _ => ContinuousLinearMap.id ℝ (Vec 2)
    H₂ := if h : 1 ≤ b' ∧ b' < M then H₂ b' h.1 h.2 else fun _ => ContinuousLinearMap.id ℝ (Vec 2)
  }
  refine ⟨freshK, fun b' hb hM' => ?_⟩
  have hbirth : 1 ≤ b' ∧ b' < M := ⟨hb, hM'⟩
  exact ⟨rfl, rfl, by simpa only [freshK, dite_eq_left hbirth] using hH b' hb hM'⟩

/-- The constant of `paper_truncated_velocity_regularity` from those of the entry (E1) and of the
cascade. -/
private theorem paper_truncated_velocity_regularity_arith (CE C n l : ℝ) (hC : 0 ≤ C) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hnl : n ≤ CE * l) : CE * (C * n + l) ≤ |CE| * (|C| * |CE| + 1) * l := by
  have h0 : 0 ≤ C * n + l := add_nonneg (mul_nonneg hC hn) hl
  have h1 : CE * (C * n + l) ≤ |CE| * (C * n + l) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
  have h2 : C * n ≤ |C| * |CE| * l := by
    calc C * n ≤ C * (CE * l) := mul_le_mul_of_nonneg_left hnl hC
      _ ≤ C * (|CE| * l) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_abs_self _) hl) hC
      _ = |C| * |CE| * l := by rw [abs_of_nonneg hC, mul_assoc]
  have h3 : |CE| * (C * n + l) ≤ |CE| * (|C| * |CE| * l + l) :=
    mul_le_mul_of_nonneg_left (add_le_add h2 le_rfl) (abs_nonneg _)
  calc CE * (C * n + l) ≤ |CE| * (|C| * |CE| * l + l) := h1.trans h3
    _ = |CE| * (|C| * |CE| + 1) * l := by ring

/-- **Regularity for the truncated velocity** at the parameters `cfg`, from the entry statement
(`C_E`, `M_*`), the cascade (`C ≥ 0`, `m₀`) and fresh kernels for every band chain. -/
private theorem paper_truncated_velocity_regularity_of_cfg {cfg : FiniteParameters} {Mst m₀ : ℕ} {CE C : ℝ}
    (hs₀ : 0 < cfg.s) (hs1 : cfg.s < 1) (ht₀ : 0 < cfg.t₀) (htT : cfg.t₀ < cfg.T₀)
    (hE : PaperEntryStatement cfg Mst CE) (hcas : PaperCascadeStatement cfg m₀ C) (hC : 0 ≤ C)
    (hfreshEx : ∀ D : OCData, D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
      IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → ∀ M : ℕ,
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ →
      ∃ freshK : ℕ → KernelSpec, ∀ b', 1 ≤ b' → b' < M →
        IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b'))
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ Φ) :
    ∃ (Mstar : ℕ) (C' : ℝ), ∀ M : ℕ, Mstar ≤ M →
    ∀ κ ∈ Set.Icc (ocEpsilon cfg.q cfg.Λ M ^ ((1 + cfg.α) - ocGamma cfg.α cfg.q) / 2)
        (2 * ocEpsilon cfg.q cfg.Λ M ^ ((1 + cfg.α) - ocGamma cfg.α cfg.q)),
    ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + cfg.Jw))) κ a (a + cfg.T₀) f θ →
    ∀ t ∈ Set.Icc (a + cfg.t₀) (a + cfg.T₀), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe cfg.s Θt (C' * Real.sqrt (l2NormSq f)) := by
  refine ⟨max Mst (m₀ + 2), |CE| * (|C| * |CE| + 1), ?_⟩
  intro M hM κ hκ a f hf θ hθ
  obtain ⟨D, hDα, hDq, hDΛ, hDζ, hDΦ, hband, hκM, hDterm⟩ :=
    exists_ocData cfg.α cfg.q cfg.Λ cfg.ζ Φ hΦ M κ hκ
  have hΦD : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ := by rw [hDΦ]; exact hΦ
  have hθD : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ := by
    rw [hDΦ, hκM]
    exact hθ
  have hm₀ : m₀ < M - 1 := by have := (le_max_right _ _).trans hM; omega
  obtain ⟨freshK, hfresh⟩ := hfreshEx D hDα hDq hDΛ hDζ hΦD M hband
  obtain ⟨te, seed, rootM, rootR, seedKc, _, _, _, _, _, _, _, _, _, _, _, _, _, hte, -, -,
    hlawEx, hseedAll, hdat⟩ := hE M ((le_max_left _ _).trans hM) D hDα hDq hDΛ hDζ hΦD hband
      hDterm (paperProv cfg D) a
  obtain ⟨law, hlM, hlR, hlaw⟩ := hlawEx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, g, _, -, -, -, -, -, hE1, -⟩ := hdat f hf θ hθD
  have hcasM := hcas D hDα hDq hDΛ hDζ hΦD M hband hDterm (M + cfg.Jw) (by omega) law hlaw
    seedKc freshK hfresh seed (M - 1) te (a + cfg.T₀) hm₀ (by linarith [hte.2])
    (hseedAll law hlM hlR freshK) g
  obtain ⟨U, Uw, Uk, hU⟩ := (hE1.2 freshK).1
  have hrep := ae_restrict_of_ae_restrict_of_subset
    (Set.Icc_subset_Icc (by linarith [hte.2] : te + cfg.t₀ / 2 ≤ a + cfg.t₀) le_rfl)
    (hcasM.2.2 U Uw Uk hU)
  have hg := hE1.1 law hlM hlR
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (a + cfg.t₀) (a + cfg.T₀))),
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe cfg.s Θt (|CE| * (|C| * |CE| + 1) * Real.sqrt (l2NormSq f)) := by
    filter_upwards [hrep, ae_restrict_mem measurableSet_Icc] with t ht htI
    obtain ⟨r, hr, hrv, hsize⟩ := ht
    obtain ⟨Θt, hΘp, hΘae, hΘ⟩ := (hE1.2 freshK).2 U Uw Uk hU law hlM hlR t
      ⟨by linarith [htI.1], htI.2⟩ _ (mul_nonneg hC (Real.sqrt_nonneg _)) r hr hrv hsize
    exact ⟨Θt, hΘp, hΘae, fun x y z hyz => (hΘ x y z hyz).trans
      (paper_truncated_velocity_regularity_arith CE C _ _ hC (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hg)⟩
  exact Providers.csNorm_trace_closure cfg.s hs₀ hs1 (streamVel (Φ (M + cfg.Jw))) κ a
    (a + cfg.T₀) f θ hθ (a + cfg.t₀) (a + cfg.T₀) _ (by linarith) (by linarith) le_rfl hae

/-- **Regularity for the truncated velocity**, the statement of `oc_finite` (Proposition 3.1 of
the paper follows from it), proved along the paper's route: the entry (E1) (Proposition 4.1 of the
paper) and the cascade (Proposition 4.2 of the paper) at one choice of parameters of
`paper_cascade_cycle_passage`. -/
theorem paper_truncated_velocity_regularity : Assembly.TopWiring.OcFiniteTargetStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hI⟩ := paper_cascade_cycle_passage α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ J hJ t₀ T ht₀ htT => ?_⟩
  obtain ⟨P, CE, C, hE, hC, -, -, hcas⟩ := hI Λ hΛ J hJ t₀ T ht₀ htT
  obtain ⟨hbα, hbs, hbq, hbζ, hbΛ, hbJ, hbt, hbT⟩ := P.ready.base
  have hΦc : IsOCStreamSeq P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ Φ := by
    rw [hbα, hbq, hbΛ, hbζ]
    exact hΦ
  have h := paper_truncated_velocity_regularity_of_cfg (by rw [hbs]; exact hs₀) (by rw [hbs]; linarith)
    (by rw [hbt]; exact ht₀) (by rw [hbt, hbT]; exact htT) hE hcas hC.le
    (fun D hDα hDq hDΛ hDζ hDΦ M hband => paper_fresh_kernels_exist P hDα hDq hDΛ hDζ hDΦ hband)
    hΦc
  rw [hbα, hbs, hbq, hbΛ, hbJ, hbt, hbT] at h
  exact h

end AVRegularity.PaperFacing
