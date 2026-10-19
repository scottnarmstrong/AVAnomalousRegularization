-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGDecomp
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation

/-! **The coarse flux of the window.** `F_c = (F_cov - F_filter) - F_front` is a.e.
strongly measurable (each flux is `L²` in time) and its mass norm is bounded by the sum of the three
bounds (`covTrunc_fluxMassLe_sub`, Minkowski in `L²(I)`); the real bound is turned into the lower
integral form of `ReconFluxSumBody`.

Special cases:
- `C_fl = 0`: all three fluxes have mass `0`, so does `F_c`.
- `C_fl < 0`: the premises force the realizations' norms to be `0 ≤ Y_i < 0`, impossible, so the
  premises are false; the lemma is still a valid implication. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- The real bound as a bound in `ℝ≥0∞` with the lower integral. -/
theorem fluxSum_ennreal {S ν Y : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (h : Real.sqrt (ν⁻¹ * S) ≤ Y) :
    ENNReal.ofReal (Real.sqrt ν)⁻¹ * (ENNReal.ofReal S) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) h)
  rw [Real.sqrt_mul (inv_nonneg.2 hν.le), Real.sqrt_inv, Real.sqrt_eq_rpow S]

section Generic

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The lower-integral form of a `FluxMassLe` bound. -/
theorem fluxSum_lintegral (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    (I : Set ℝ) (Y : ℝ) (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    ENNReal.ofReal (Real.sqrt ν)⁻¹ * (∫⁻ s in I, ENNReal.ofReal
      (massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (G v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
  have hmem := covTrunc_mass_memLp k ν ρ π I Y G hG
  have hint : Integrable (fun s => ‖covTruncMassCLM h k ρ π (fun v => G v s)‖ ^ 2)
      (volume.restrict I) := by
    have hm2 : MemLp (fun s => covTruncMassCLM h k ρ π (fun v => G v s)) ((2 : ℕ) : ENNReal)
        (volume.restrict I) := by simpa using hmem
    simpa using hm2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hnn : ∀ s, 0 ≤ massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (G v s).val) := fun s => by
    rw [← massWeightedCarrierCLM_normSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (fun _ => k) ρ π hπ (fun v => G v s)]
    positivity
  have hint2 : Integrable (fun s => massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (G v s).val)) (volume.restrict I) := by
    refine hint.congr (Filter.Eventually.of_forall fun s => ?_)
    exact (massWeightedCarrierCLM_normSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (fun _ => k) ρ π hπ (fun v => G v s))
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall hnn)]
  exact fluxSum_ennreal hν (integral_nonneg hnn) hG.2

end Generic

section Context

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The coarse flux of the window at a context.** -/
theorem reconFluxSum_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc : ℕ) (Cfl : ℝ) (hle : c.tp ≤ c.tp + rTobs c)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (h128 : 128 ≤ A.Λ) : ReconFluxSumAt c x kc Cfl hle F1 F2 F3 := by
  intro h1 h2 h3
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hκ : 0 < c.D.κ (M - 1) := by
    have hch : IsOCBandChain X.α X.q A.Λ X.ζ M c.D.κ := hchain
    exact CycleReference.bandChain_pos (by omega) X.hζ hch (Nat.sub_le _ _)
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hqq hΛ c.lawW v.1
  have hwin : c.tp + rTobs c = c.a + A.T₀ := by simp [rTobs]
  have hone := x.one
  have hRho : c.D.termRho cr M = rRho c := by
    simp only [OCData.termRho, hone, one_mul, OCData.termB, OCData.termH, rRho]
  rw [hRho] at h1 h2 h3
  have h13 := covTrunc_fluxMassLe_sub kc _ _ _ hκ hπ _ _ _ F1 F3 h1 h3
  have h132 := covTrunc_fluxMassLe_sub kc _ _ _ hκ hπ _ _ _ _ F2 h13 h2
  have hsum : Cfl * c.covPrice * c.normF + Cfl * c.filterPrice * c.normF +
      Cfl * c.frontPrice * c.normF = Cfl * c.normF * rTT c := by
    simp only [rTT]; ring
  rw [hsum] at h132
  have h132' : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => kc) (c.D.κ (M - 1)) (rRho c) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀))
      (reconFc c F1 F2 F3) (Cfl * c.normF * rTT c) := h132
  rw [← hwin] at h132'
  exact ⟨fun v => (h132'.1 v).aestronglyMeasurable,
    fluxSum_lintegral kc _ _ _ hκ hπ _ _ _ h132'⟩

end Context

/-- **The coarse flux of the window.** -/
theorem termReconFluxSum : TermReconFluxSumStatement := by
  intro ℓ X
  refine ⟨128, le_rfl, fun A hΛ hV => ?_⟩
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW hcK _ _
    cP CP cHP Cw Ce cker hcP
  exact ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨0, fun M _ c x Cfl hle F1 F2 F3 =>
    reconFluxSum_at c x kc Cfl hle F1 F2 F3 hΛ⟩⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
