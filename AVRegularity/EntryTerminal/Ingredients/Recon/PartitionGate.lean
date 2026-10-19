-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
public import AVRegularity.Construction.Residual.Presentation.Ident
public import AVRegularity.Construction.Residual.Presentation.FluxAe
public import AVRegularity.CycleComparison.Reconstruction.PhysicalLiftPartition
public import AVRegularity.EntryTerminal.Ingredients.PrepFamily.PrepFamily
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The entrance of the terminal anchor**. `τ'_M = τ''_M / L_M` with `L_M = 4⌈ε_{M-1}^{-δ}⌉ + 1 → ∞`, so for every `c > 0` the half-width
of the quiet margin is at most `c τ''_M` for `M` large: the preparation's `a_M + c τ''_M ≤ t_p` gives
the entrance `a_M + τ'_M ≤ t_p` (the premise of the quiet entrance and of the reconstruction's lift sequences).

Degenerate cases:
- `c ≥ 1`: `τ'_M ≤ τ''_M` holds at every level (`L_M ≥ 1`); the threshold is not needed.
- `c → 0`: the threshold grows like the level where `ε_{M-1}^δ ≤ 4c`. -/

@[expose] public section

open Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **`τ'_M ≤ c τ''_M` for large `M`.** -/
theorem ocTauP_le_mul_ocTauPP_eventually {α q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hδ : 0 < ocDelta α q) {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ocTauP α q Λ M ≤ c * ocTauPP α q Λ M := by
  have ht := EntryScales.epsilon_rpow_tendsto_zero (Λ := Λ) hq hΛ hδ
  obtain ⟨N, hN⟩ :=
    (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 4 * c))).exists_forall_of_atTop
  refine ⟨N + 1, fun M hM => ?_⟩
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ
  have hE : 0 < ocEpsilon q Λ (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hEδ : 0 < ocEpsilon q Λ (M - 1) ^ ocDelta α q := Real.rpow_pos_of_pos hE _
  have hsmall : ocEpsilon q Λ (M - 1) ^ ocDelta α q < 4 * c := hN (M - 1) (by omega)
  have hτ : 0 < ocTauPP α q Λ M := Construction.Stream.ocTauPP_pos hΛ1
  -- `L_M ≥ 4 ε^{-δ} ≥ 1/c`
  have hceil : ocEpsilon q Λ (M - 1) ^ (-ocDelta α q) ≤
      (⌈ocEpsilon q Λ (M - 1) ^ (-ocDelta α q)⌉₊ : ℝ) := Nat.le_ceil _
  have hneg : ocEpsilon q Λ (M - 1) ^ (-ocDelta α q) = (ocEpsilon q Λ (M - 1) ^ ocDelta α q)⁻¹ :=
    Real.rpow_neg hE.le _
  have hL : c⁻¹ ≤ (ocL α q Λ M : ℝ) := by
    have h1 : c⁻¹ ≤ 4 * (ocEpsilon q Λ (M - 1) ^ ocDelta α q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hEδ]
      have := mul_le_mul_of_nonneg_left hsmall.le (inv_nonneg.2 hc.le)
      rw [show c⁻¹ * (4 * c) = 4 by field_simp] at this
      linarith
    have h2 : (ocL α q Λ M : ℝ) = 4 * (⌈ocEpsilon q Λ (M - 1) ^ (-ocDelta α q)⌉₊ : ℝ) + 1 := by
      unfold ocL
      push_cast
      ring
    rw [h2, ← hneg] at *
    linarith
  have hLpos : 0 < (ocL α q Λ M : ℝ) := lt_of_lt_of_le (inv_pos.2 hc) hL
  unfold ocTauP
  rw [div_le_iff₀ hLpos]
  have : 1 ≤ c * (ocL α q Λ M : ℝ) := by
    have := mul_le_mul_of_nonneg_left hL hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  nlinarith

/-- **The entrance from the preparation**: if `a_M + c τ''_M ≤ t_p` with `c > 0`, then
`a_M + τ'_M ≤ t_p` for `M` large. -/
theorem entrance_of_prep_eventually {α q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hδ : 0 < ocDelta α q) {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ aM tp : ℝ, aM + c * ocTauPP α q Λ M ≤ tp →
      aM + ocTauP α q Λ M ≤ tp := by
  obtain ⟨M₀, h⟩ := ocTauP_le_mul_ocTauPP_eventually hq hΛ hδ hc
  exact ⟨M₀, fun M hM aM tp hp => by linarith [h M hM]⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **A strongly measurable version of the coarse flux**. The flux sum gives the coarse flux
`F_c` of the window only a.e. strongly measurable. The window theorem also needs its Galerkin
coefficients at the clamped time to be Borel measurable, which an a.e. statement cannot give. The
assembly therefore passes to a strongly measurable version `F_c'` equal to `F_c` a.e. on the window:
- its Galerkin coefficients are measurable (`measurable_coarseModeCoeff_comp`: a coefficient is the
  `L²` pairing of the value class with a fixed mode);
- `IsCoarseDefect` transfers (`isCoarseDefect_congr_ae`): the flux enters `CoupledWeakIdentity`
  through time integrals (a.e. in time) and through the integrability of the integrand at each time,
  which holds for every `L²` jet;
- the flux bound transfers (a lower integral of an a.e. equal integrand).

Degenerate cases:
- `F_c` strongly measurable: `F_c' = F_c` is allowed.
- Empty window `t₁ < t₀`: every a.e. statement on `Icc t₀ t₁` is vacuous. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- `CoupledWeakIdentity` under a change of the flux `F` on a null set of times, when the change
pairs integrably with the test gradient at every time. -/
theorem coupledWeakIdentity_congr_flux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2} {u₀ f φ : Vec 2 → H}
    {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H}
    (hI : CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g)
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)), F' s = F s)
    (hint : ∀ s ∈ Set.Ioc t₀ t, ∀ k : Fin 2,
      Integrable (fun x => inner ℝ (F' s x k - F s x k) (dφ k x)) μ) :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F' g := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  refine ⟨h1, h2, fun s hs => ?_, ?_, ?_⟩
  · have hsum : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F' s x k - F s x k) (dφ k x)) μ :=
      integrable_finsetSum _ fun k _ => hint s hs k
    refine ((h3 s hs).sub hsum).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply, Fin.sum_univ_two, inner_add_left, inner_sub_left]
    ring
  · refine h4.congr_fun_ae ?_
    filter_upwards [hae] with s hs
    simp only [hs]
  · rw [h5]
    refine integral_congr_ae ?_
    filter_upwards [hae] with s hs
    simp only [hs]

/-- **`IsCoarseDefect` for an a.e. equal version of the flux.** -/
theorem isCoarseDefect_congr_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc Fc' : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hd : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc)
    (hae : ∀ v, Fc' v =ᵐ[volume.restrict (Set.Icc t₀ t₁)] Fc v) :
    IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc' := by
  intro v t ht φ
  refine coupledWeakIdentity_congr_flux (hd v t ht φ) ?_ ?_
  · have hsub : Set.Ioc t₀ t ⊆ Set.Icc t₀ t₁ := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hae v)] with s hs
    rw [hs]
  · intro s _ j
    have hc : ∀ X : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp (fun x => X.toFunction.jet (valueIndex2 k) x j) 2
          (volume.restrict AVenhance.unitCube) := fun X =>
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h v) j).comp_memLp'
        (CycleComparison.Coarse.memLp_jet X _)
    exact CycleComparison.Coarse.integrable_inner_memLp ((hc _).sub (hc _))
      (CycleComparison.Coarse.memLp_jet φ _)

/-- **The Galerkin coefficients of a strongly measurable family are measurable** (at any measurable
time change, e.g. the clamp `projIcc`). -/
theorem measurable_coarseModeCoeff_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {K : ℕ} {G : ∀ i, ℝ → TorusHk K (h i)}
    (hG : ∀ i, StronglyMeasurable (G i)) {p : ℝ → ℝ} (hp : Measurable p) (n : ℕ)
    (r : CoupledFourierModeIndex (h := h) n) :
    Measurable fun s => coarseModeCoeff n (fun i => G i (p s)) r := by
  have hm := coupledModeJet_memLp (h := h) n r r.1 0 Fin.elim0
  have heq : (fun s => coarseModeCoeff n (fun i => G i (p s)) r) =
      fun s => inner ℝ (CycleComparison.Coarse.tvalL2 (G r.1 (p s))) (hm.toLp _) :=
    funext fun s => (CycleComparison.Coarse.inner_tvalL2 _ _ _ hm.coeFn_toLp).symm
  rw [heq]
  exact ((CycleComparison.Coarse.continuous_tvalL2.comp_stronglyMeasurable
    ((hG r.1).comp_measurable hp)).inner stronglyMeasurable_const).measurable

/-- The flux bound of an a.e. equal family. -/
theorem fluxBound_congr_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {k : ℕ} {I : Set ℝ} {Fc Fc' : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hae : ∀ v, Fc' v =ᵐ[volume.restrict I] Fc v) (ρ : ℝ) (π : ι → ℝ) :
    (∫⁻ s in I, ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) ρ π (fun v => (Fc' v s).val))) =
      ∫⁻ s in I, ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) ρ π (fun v => (Fc v s).val)) := by
  have hall : ∀ᵐ s ∂(volume.restrict I), ∀ v, Fc' v s = Fc v s := ae_all_iff.2 hae
  refine lintegral_congr_ae ?_
  filter_upwards [hall] with s hs
  have he : (fun v => (Fc' v s).val) = fun v => (Fc v s).val := funext fun v => by rw [hs v]
  rw [he]

/-- The flux bound passes to an a.e. equal family. -/
theorem fluxBound_le_of_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {k : ℕ} {I : Set ℝ} {Fc Fc' : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hae : ∀ v, Fc' v =ᵐ[volume.restrict I] Fc v) {ρ : ℝ} {π : ι → ℝ} {a Y : ℝ≥0∞}
    (hY : a * (∫⁻ s in I, ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) ρ π (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤ Y) :
    a * (∫⁻ s in I, ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) ρ π (fun v => (Fc' v s).val))) ^ (1 / 2 : ℝ) ≤ Y := by
  rw [fluxBound_congr_ae hae]
  exact hY

/-- **The version of the flux.** An a.e. strongly measurable family on a window has a strongly
measurable version, equal to it a.e. on the window. -/
theorem exists_fluxVersion {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {k : ℕ} {I : Set ℝ} {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hFcm : ∀ v, AEStronglyMeasurable (Fc v) (volume.restrict I)) :
    ∃ Fc' : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, Fc' v =ᵐ[volume.restrict I] Fc v) ∧ ∀ v, StronglyMeasurable (Fc' v) :=
  ⟨fun v => (hFcm v).mk _, fun v => (hFcm v).ae_eq_mk.symm,
    fun v => (hFcm v).stronglyMeasurable_mk⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! **The named steps of the terminal reconstruction**.

The terminal reconstruction (`TermReconStatement`) is one instance of the window theorem
`ReconWindowAt.physical_lift` at a context `c` of the terminal residual, at the common order
`k₀ + ℓ`. The data of the window are fixed here:
- the actual family `c.Gw.actualFamily`, the pieces `oddSlotOf k`, the masses of the weak law;
- `ν = κ_M`, `B = κ_{M-1}`, the window `[t_p, t_p + T_obs]`, `T_obs = a + T₀ - t_p`;
- the slots `K_v = k₀ + ℓ + D_t (d_w - rank v)` (`descSlots`), `K_max = k₀ + ℓ + D_t d_w`;
- the orders `A_cl = max 1 A_T`, `K_lift`, `L_lift`, `m'`, `k_res`, `N_χ`, `r₀ = k_c + N_T + D_t - 1`;
- the coarse field `W = P_pZ` truncated to the order `k_c + 1 + N_T + D_t` (`reconW`);
- the lift coefficients `c.CcT` and the classical representative `c.aRep`.

The steps give the fields of the window and the hypotheses of the window theorem, in groups:
- **Lift sequences** (`ReconSeqAt`): the lift sequences of the observed pulses on the clipped windows,
  restarted at `t_p`. Generic core: `r2c_liftSequence_restart` (the restart of a lift sequence at a
  time where its positive lifts vanish) and `r2c_quietZero_core` (positive lifts started at
  zero stay zero through a stretch without drift and with fast-independent edges).
- **Lift settings** (`ReconSettingAt`): the lift settings and the grading of the lift sequences.
- **Family side** (`ReconFamilyAt`): the family side (descent, torus compatibility, atlas, pieces, partition
  at the uniform cutoff constant `reconCpart`, fast independence).
- **Coarse side** (`ReconCoarseAt`): the coarse setting, the coarse defect of `W` with the flux
  `F_c = F_cov - F_filter - F_front`, and the mean presentations.
- **Analytic side** (`ReconAnalyticSideAt`): the scale facts, the coefficient and drift bounds, the
  energies of `W` at the partition order `rpord`, and the dominations of the bill. The partition
  terms are derived in the assembly from `partition_window_input`, with monotonicity of lift
  settings (`LiftSettingMonoStatement`) and the scale of the partition bound
  (`ReconPartitionScaleAt`).

Degenerate cases:
- A weak stage without edges: `K ≡ k₀ + ℓ`; the lift sequences are diagonal.
- `ℓ = 0`: the common order of the terminal residual.
- `t_p` in the trimmed quiet margin with no pulse window containing it: the clipped windows start
  at their slot starts and the lift-sequence step is the restriction on the right only.
- Constant order: every constant of the steps is chosen before `j₀` and `M` (`ReconPrefix`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Lift AVRegularity.ChartTransport
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! ### The generic core of the lift-sequence step -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-! ### The orders of the window -/

/-- The cleanup order `A_cl = max 1 A_T`. -/
abbrev rAcl (A : TermArgs X) : ℕ := max 1 A.AT

/-- `K_max = k₀ + ℓ + D_t d_w`. -/
abbrev rKmax (A : TermArgs X) (ℓ : ℕ) : ℕ := A.k₀ + ℓ + A.Dt * A.dW

/-- `K_lift`. -/
abbrev rKlift (A : TermArgs X) (ℓ : ℕ) : ℕ :=
  2 * rAcl A + 2 + rKmax A ℓ + A.Dt * (A.dW + 1) * A.NT + 2

/-- `L_lift`. -/
abbrev rLlift (A : TermArgs X) (ℓ : ℕ) : ℕ := rKmax A ℓ + A.Dt * (A.dW + 1) * A.NT + 2

/-- The density order `m'`. -/
abbrev rm' (A : TermArgs X) (ℓ : ℕ) : ℕ := rAcl A + 1 + rKmax A ℓ + 2 * A.NT + A.Dt

/-- The residual reserve `k_res`. -/
abbrev rkres (A : TermArgs X) (ℓ : ℕ) : ℕ := rAcl A + 3 + rKmax A ℓ + A.NT

/-- The chart order `N_χ`. -/
abbrev rNχ (A : TermArgs X) (ℓ : ℕ) : ℕ := rAcl A + 2 + rKmax A ℓ + 2 * A.NT + A.Dt

/-- The classical order of the coarse field `r₀ = k_c + N_T + D_t - 1`. -/
abbrev rr₀ (A : TermArgs X) (kc : ℕ) : ℕ := kc + (A.NT + A.Dt) - 1

/-- The partition order `4(N_T + D_t) + 2A_cl + 16 + K_max` of `partition_window_input`:
the order of the energy of `W` passed to the window theorem. -/
abbrev rpord (A : TermArgs X) (ℓ : ℕ) : ℕ := 4 * (A.NT + A.Dt) + 2 * rAcl A + 16 + rKmax A ℓ

/-- The uniform derivative constant of the pulse cutoffs (`cutoff_derivative_uniform_bound`): the
partition constant of the window (the constants of `partition_window_input` depend on it, so it is
fixed before the level). -/
noncomputable def reconCpart : ℝ := Classical.choose CycleReference.cutoff_derivative_uniform_bound

theorem reconCpart_spec : 0 < reconCpart ∧
    ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ k : ℤ, ∀ t : ℝ,
      |deriv (ocCutoff α q Λ m k) t| ≤ reconCpart / ocTau α q Λ m :=
  Classical.choose_spec CycleReference.cutoff_derivative_uniform_bound

section Data

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- The slots of the window: `K_v = k₀ + ℓ + D_t (d_w - rank v)`. -/
abbrev rK (ℓ : ℕ) : CompIn c.Gw.comps → ℕ :=
  fun v => A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v

/-- The length of the window `T_obs = a + T₀ - t_p`. -/
abbrev rTobs : ℝ := c.a + A.T₀ - c.tp

/-- The slow length of the window `√(B τ''_M)`. -/
abbrev rRho : ℝ := Real.sqrt (c.D.κ (M - 1) * ocTauPP c.D.α c.D.q c.D.Λ M)

/-- The coarse field of the window: `P_pZ` truncated to the order `k_c + 1 + N_T + D_t`. -/
abbrev reconW (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) :
    ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (kc + 1 + (A.NT + A.Dt)) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk hW (c.PZ v t)

/-- The lift data of the observed pulse `k` in the form of the window. -/
abbrev rLiftData (k : ℤ) : LiftOperatorData (CompIn c.Gw.comps) (fun v => ScalarH v.1.root) A.Dt :=
  pulseLiftData c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.Φ (M - 1)) (c.D.hΦ (M - 1)) (c.D.κ M)
    (c.D.κ (M - 1)) (rRho c) (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) k
    (c.Gw.actualFamily.fiber (oddSlotOf k) ())

/-- The clipped lift window of the pulse `k`, in cell time: its left end. -/
abbrev rSeqStart (k : ℤ) : ℝ :=
  max (((k : ℝ) - 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) c.tp / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2

/-- The clipped lift window of the pulse `k`, in cell time: its right end. -/
abbrev rSeqEnd (k : ℤ) : ℝ :=
  min (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) (c.tp + rTobs c) /
    ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2

/-- The coarse flux of the window `F_c = F_cov - F_filter - F_front` (a definition, so that the
subtraction on `TorusHk` is elaborated once). -/
def reconFc {kc : ℕ}
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  fun v t => F1 v t - F3 v t - F2 v t

/-- The radius of the window theorem `r_s = min(c_K, 1)·x` (`r_s ≤ x` as the window requires; the
bound at `r_* = c_K x` costs `max(1, c_K)^{K_max}`). -/
abbrev rRs : ℝ := min cK 1 * c.D.eps M

/-- The sum of the flux prices `𝔱 = E^{δ(R_T+1)/2} + E^{δp_T} + [E^{b_T+t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}]`. -/
abbrev rTT : ℝ := c.frontPrice + c.covPrice + c.filterPrice

end Data

/-! ### The steps at a context -/

section Steps

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The lift sequences at a context: the lift sequences of the observed pulses on the clipped windows.** -/
def ReconSeqAt (ℓ : ℕ) : Prop :=
  ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsLiftSequence (rLiftData c k) (rKlift A ℓ + A.Dt + 2) (max (rLlift A ℓ + 1) (rLlift A ℓ + 2))
      (rSeqStart c k) (rSeqEnd c k) A.NT A.dW (c.CcT k)

/-- **The lift-sequence step.** With the lift floors above the orders of the window, the
quiet margin (`x.quietMargin`), `c_r = 1` and the entrance `a_M + τ'_M ≤ t_p`, the stage's lift
sequences (`c.lift.1`, from the slot starts) restricted to the clipped windows are the lift
sequences of the window: for a pulse whose window starts before `t_p`, the stretch
`[slotStart, t_p]` lies in the trimmed quiet margin (`τ'_M = L_M τ_M ≥ 5τ_M`) and in `[a_M, a + T₀]`, where
the pulse drift vanishes and the fibre is fast independent (the stage invariant of `c.weak`), so
`r2c_quietZero_core` and `r2c_liftSequence_restart` apply. -/
def ReconSeqStep (_x : TermResAux c) (ℓ : ℕ) : Prop :=
  rKlift A ℓ + A.Dt + 2 ≤ sXT → max (rLlift A ℓ + 1) (rLlift A ℓ + 2) ≤ sZT →
    c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp → ReconSeqAt c ℓ

/-- The lift settings and the grading at given setting data (the body of the lift-setting step). -/
def ReconSettingBody (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ) : Prop :=
  (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsLiftSetting (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
      (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c)
      (ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (par k) (V k) A.dW A.NT (rKlift A ℓ)
      (rLlift A ℓ) (rLlift A ℓ) qs qf CGl Cw (fun _ _ => Ca) bM Sb) ∧
  ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c), ∀ hh, hh ≤ A.dW →
    ∀ n, 1 ≤ n → n ≤ A.NT → ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ rAcl A + 2 + rKmax A ℓ →
      schurEnergyJet (c.Gw.mass c.lawW) (Set.Icc (rSeqStart c k) (rSeqEnd c k)) (rLlift A ℓ) j
          (c.CcT k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh * (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) ^ (n - m'' + j))

/-- **The lift-setting step: the lift settings and the grading of the observed pulses**, at the
constants `CGl, Cw, Ca, Sb, Cg` (chosen before the level). -/
def ReconSettingAt (_x : TermResAux c) (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ) : Prop :=
  ∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ),
    ReconSettingBody c ℓ CGl Cw Ca Sb Cg qs qf par V bM

/-- The family side of the window at an atlas and a partition constant (the body of the family step). -/
def ReconFamilyBody (ℓ : ℕ) (T : c.Gw.actualFamily.Atlas) (Cpart : ℝ) : Prop :=
    c.Gw.actualFamily.IsDescending (rK c ℓ) ∧
    IsTorusCompatible c.Gw.actualFamily (fun _ => ()) (ocEpsilon c.D.q c.D.Λ (M - 1)) ∧
    T.IsConsecutiveClosed (Set.Icc c.tp (c.tp + rTobs c)) ∧
    T.CoversQuiet (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M) (Set.Icc c.tp (c.tp + rTobs c)) ∧
    T.IsQuiet (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M) (ocEpsilon c.D.q c.D.Λ (M - 1)) ∧
    (∀ p q' (hpq : T.adjacent p q'),
      ((c.Gw.actualFamily.piece p).output ∩ (c.Gw.actualFamily.piece q').output ∩
        Set.Icc c.tp (c.tp + rTobs c)).Nonempty → T.sameCtx p q' hpq () ()) ∧
    (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
      (c.Gw.actualFamily.piece (oddSlotOf k)).label = ocPulseChartIndex c.D.α c.D.q c.D.Λ M k ∧
      (∀ t, ⇑((c.Gw.actualFamily.piece (oddSlotOf k)).material t) =
        ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) t) ∧
      ocPulseWindow c.D.α c.D.q c.D.Λ M k ∩ Set.Icc c.tp (c.tp + rTobs c) ⊆
        (c.Gw.actualFamily.piece (oddSlotOf k)).output) ∧
    Set.InjOn oddSlotOf ↑(ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c)) ∧
    IsLiftPartition (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
      (fun k => c.Gw.actualFamily.weight (oddSlotOf k)) (ocPulseWindow c.D.α c.D.q c.D.Λ M)
      (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M) (Set.Icc c.tp (c.tp + rTobs c))
      (ocTau c.D.α c.D.q c.D.Λ M) Cpart ∧
    c.Gw.actualFamily.IsFastIndependentOn
      (ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M ∩ Set.Icc c.tp (c.tp + rTobs c))

/-- **The family step: the family side of the window** at the actual family of the weak stage
with the slots `rK c ℓ`. -/
def ReconFamilyAt (ℓ : ℕ) : Prop :=
  ∃ T : c.Gw.actualFamily.Atlas, ReconFamilyBody c ℓ T reconCpart

/-- **The family step at a context** (the premises it uses beyond the context: `a_M ≤ t_p` from the
preparation and the deadline `t_p < a + T₀`). -/
def ReconFamilyStep (ℓ : ℕ) : Prop :=
  c.tp < c.a + A.T₀ → ReconFamilyAt c ℓ

/-- The three flux realizations of order `k_c` on the window (from `TermCovTruncAt`,
`TermFrontierAt`, `TermFilterAt`). -/
def ReconFluxRealizations (x : TermResAux c) (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) kc
      (Set.Icc c.tp (c.a + A.T₀))
      (fun v t y => toFluxL (menuCovTruncFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT
        x.aZ v t y)) F1 ∧
    IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) kc
      (Set.Icc c.tp (c.a + A.T₀))
      (fun v t y => toFluxL (menuFrontierFlux (A.Mt M sXT sZT c.tp cr) (A.Pt c.D Cw cr M)
        (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M A.pT 1 A.RT
        (c.D.eps (M - 1)) A.η₀ x.aY v t y)) F2 ∧
    IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) kc
      (Set.Icc c.tp (c.a + A.T₀))
      (fun v t y => toFluxL (menuFilterFlux (A.Mt M sXT sZT c.tp cr) (A.Pt c.D Cw cr M)
        (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt' M A.pT (c.D.eps (M - 1)) A.η₀ x.aZ
        v t y)) F3

/-- **The time regularity of the coarse data**: the three flux realizations
are square integrable in time on the window and `W = P_pZ` is continuous there. The assembly takes
them from the first clauses of the three `FluxMassLe` premises of `TermReconAt` and from the energy step. -/
def ReconTimeRegAt (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  (∀ v, MemLp (F1 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    (∀ v, MemLp (F2 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    (∀ v, MemLp (F3 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    ∀ v, ContinuousOn (reconW c kc hW v) (Set.Icc c.tp (c.a + A.T₀))

/-- The coarse side of the window at given coarse data (the body of the coarse step). -/
def ReconCoarseBody (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root)) : Prop :=
  IsCoarseSetting c.tp (c.tp + rTobs c) (rRho c) (c.D.κ (M - 1)) aC B₀C lamC
    (streamVel (c.D.Φ (M - 1))) (A.NT + A.Dt) A.dW pc Jc kc ((A.NT + A.Dt) + 8 * pc + 4)
    (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4))
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) AD CE (c.Gw.mass c.lawW) Aedge Cstar Θc ∧
  IsCoarseDefect c.tp (c.tp + rTobs c) (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1)))
    (A.NT + A.Dt) A.dW kc (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) AD CE
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) f0 (reconW c kc hW)
    (reconFc c F1 F2 F3) ∧
  ∀ r ∈ Finset.range (A.dW + 1),
    IsMeanPresentation (Set.Icc c.tp (c.tp + rTobs c)) (A.NT + A.Dt) r AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
        (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT r
        (fun k => rLiftData c k) c.CcT
        (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)))

/-- **The coarse step: the coarse side of the window.** For the flux realizations, the coarse
field `W = P_pZ` satisfies the coarse defect equation of the window with the flux
`F_c = F_cov - F_filter - F_front` (the second residual identity `(MI - 𝐄)P_pZ = div F_mean`,
`Frame.macroWeak`, and `MenuMeanFluxSplitStatement`), with letters `(AD, CE)` presenting
the glued means and the coarse setting. -/
def ReconCoarseResult (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ∃ (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root)),
    ReconCoarseBody c kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0

/-- **The coarse step at a context**: the coarse side from the flux realizations and their time regularity, the
lift sequences and a lift setting at the offset `ℓ` (the conversion to the coarse defect uses both). -/
def ReconCoarseAt (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ReconFluxRealizations c x kc F1 F2 F3 → ReconTimeRegAt c kc hW F1 F2 F3 →
    ReconSeqAt c ℓ → ∀ (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ), ReconSettingAt c x ℓ CGl Cw Ca Sb Cg →
    ReconCoarseResult c kc hW F1 F2 F3

/-- **The energy step: the energy of the coarse field.** `W = P_pZ` is continuous in time
and its strong energy at the slow length `√(Bτ''_M)` and the partition order `rpord` is at most
`C_s ‖f‖₂` (`kernel_energy_torus` with `c.seed`, the covariance polynomial bound, the readout,
and `c.prepB`). -/
def ReconEnergyAt (_x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (Cs : ℝ) : Prop :=
  (∀ v, ContinuousOn (reconW c kc hW v) (Set.Icc c.tp (c.tp + rTobs c))) ∧
    strongEnergyUpTo (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.tp + rTobs c) (rpord A ℓ)
      (reconW c kc hW) ≤ ENNReal.ofReal (Cs * c.normF)

/-- **The coefficient step: the drift and the edge coefficients of the window** are measurable
and bounded on the window. -/
def ReconCoeffAt (ℓ : ℕ) : Prop :=
  ∃ Vb CA : ℝ, 0 ≤ CA ∧
    (∀ s ∈ Set.Ioc c.tp (c.tp + rTobs c), ∀ k,
      AEStronglyMeasurable (fun y => streamVel (c.D.Φ M) s y k)
        (volume.restrict AVenhance.unitCube)) ∧
    (∀ s ∈ Set.Ioc c.tp (c.tp + rTobs c), ∀ y k, |streamVel (c.D.Φ M) s y k| ≤ Vb) ∧
    (∀ s ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v u d y,
      ‖(edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
        (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d s y‖ ≤ CA) ∧
    ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient c.Gw.actualFamily (c.D.κ M)
        (ocEpsilon c.D.q c.D.Λ M) (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d s)
        (volume.restrict AVenhance.unitCube)

/-- **The partition terms** (the input of the window theorem). The
partition derivatives of the lifts of the Galerkin approximants of `W` are bounded by `X_p` times
their classical strong energy at the partition order `rpord`, with `X_p ≤ C_px 𝔅_rec`. The
assembly derives it from `partition_window_input` on the window, monotonicity of lift settings
(the lift settings at the partition orders) and the scale of the partition bound
(`ReconPartitionScaleAt`). -/
def ReconPartitionAt (_x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (Cpx cgap Cg : ℝ) : Prop :=
  ∃ Xp : ℝ, 0 ≤ Xp ∧ Xp ≤ Cpx * c.reconBill cgap Cg ∧
    ∀ n, ∫⁻ t in Set.Icc c.tp (c.tp + rTobs c), (∑ j ∈ Finset.range (rKmax A ℓ + 1),
        ∑ w' : DerivativeWord2 j, scalInt (c.Gw.mass c.lawW) (fun y => rRs c ^ j •
          orderedDerivative w' (fun y' =>
            ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
              deriv (c.Gw.actualFamily.weight (oddSlotOf k)) t •
                pulsePhysicalLift (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
                  (ocEpsilon c.D.q c.D.Λ M)
                  (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT A.dW (c.CcT k)
                  (ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
                  (ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
                  (coarseTraj n (reconW c kc hW)) t y') y)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Xp * classicalStrongEnergy (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW)
        (Set.Icc c.tp (c.tp + rTobs c)) (rpord A ℓ) (coarseTraj n (reconW c kc hW))

/-- **The scale of the partition bound at a context**: the gluing factor of
`partition_window_input` (constants `C_gate, c_gate`, grading `S_b`, `H = d_W`) is at most `C_px`
times the reconstruction bill. -/
def ReconPartitionScaleAt (_x : TermResAux c) (Cgate cgate Sb Cpx cgap Cg : ℝ) : Prop :=
  c.tp < c.a + A.T₀ →
  Cgate * (1 + Sb) ^ A.dW *
      ((ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c)).card : ℝ) *
      ocEll c.D.q c.D.Λ M (c.D.κ M) * Real.sqrt (1 / ocTau c.D.α c.D.q c.D.Λ M) *
      Real.exp (-(cgate * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) ≤
    Cpx * c.reconBill cgap Cg

/-- **The scale-facts step: the scales of the window and the dominations of the bill.** With the
deadline `t_p < a + T₀`: the exponents and the construction (`c.data`), the scales
(`ε_M ≤ √(Bτ''_M) ≤ ε_{M-1}`, `r_s ≤ ε_M`), and the five terms of the window's bill dominated by
`𝔅_rec` (`reconBill` at `c_r = 1`, `A_cl = max 1 A_T`). -/
def ReconScaleBody (cgap Cg : ℝ) : Prop :=
  0 < c.D.α ∧ c.D.α < 1 / 3 ∧ 0 < X.s ∧ X.s < (1 - c.D.α) / 2 ∧
  IsAdmissibleQ c.D.α X.s c.D.q ∧ IsFastProfile c.D.ζ ∧ 128 ≤ c.D.Λ ∧
  IsOCStreamSeq c.D.α c.D.q c.D.Λ c.D.ζ c.D.Φ ∧ 2 ≤ M ∧ 0 < c.D.κ M ∧ 0 < c.D.κ (M - 1) ∧
  0 < ocEpsilon c.D.q c.D.Λ M ∧ ocEpsilon c.D.q c.D.Λ M ≤ rRho c ∧
  rRho c ≤ ocEpsilon c.D.q c.D.Λ (M - 1) ∧ 0 < rRs c ∧ 0 ≤ rTT c ∧
  (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ A.NT ≤ c.reconBill cgap Cg ∧
  Real.sqrt (c.D.κ (M - 1) / c.D.κ M) * rTT c ≤ c.reconBill cgap Cg ∧
  (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ 2 * rTT c ≤ c.reconBill cgap Cg ∧
  (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ A.NT *
      (Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
        (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ rAcl A) ≤ c.reconBill cgap Cg ∧
  (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ 2 *
      (Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
        (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ rAcl A) * rTT c ≤ c.reconBill cgap Cg

/-- **The scale-facts step at a context**, with the deadline `t_p < a + T₀`. -/
def ReconScaleAt (_x : TermResAux c) (cgap Cg : ℝ) : Prop :=
  c.tp < c.a + A.T₀ → ReconScaleBody c cgap Cg

/-- The coarse flux of the window is a.e. strongly measurable and bounded (the conclusion of the flux-sum step;
the Borel measurability of its Galerkin coefficients is not asked, the assembly passes to
a strongly measurable version). The order `hle` is kept for the callers. -/
def ReconFluxSumBody (kc : ℕ) (Cfl : ℝ) (_hle : c.tp ≤ c.tp + rTobs c)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  (∀ v, AEStronglyMeasurable (reconFc c F1 F2 F3 v)
    (volume.restrict (Set.Icc c.tp (c.tp + rTobs c)))) ∧
  ENNReal.ofReal (Real.sqrt (c.D.κ (M - 1)))⁻¹ * (∫⁻ s in Set.Icc c.tp (c.tp + rTobs c),
      ENNReal.ofReal (massNormSq (E := fun v : CompIn c.Gw.comps =>
        PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) (K := fun _ => kc) (rRho c)
        (c.Gw.mass c.lawW) (fun v => (reconFc c F1 F2 F3 v s).val))) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Cfl * c.normF * rTT c)

/-- **The flux-sum step: the coarse flux of the window.** From the three flux bounds at the
constant `C_fl`, the flux `F_c = F_cov - F_filter - F_front` is a.e. strongly measurable on the
window, and `B^{-1/2}‖F_c‖_{L²(I;H_{ρ,k_c;π})} ≤ C_fl ‖f‖₂ 𝔱` (Minkowski,
`sqrt_massNormSq_add_le`; `ρ = c_r√(Bh)` at `c_r = 1`). -/
def ReconFluxSumAt (_x : TermResAux c) (kc : ℕ) (Cfl : ℝ)
    (hle : c.tp ≤ c.tp + rTobs c)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F1
      (Cfl * c.covPrice * c.normF) →
  FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F2
      (Cfl * c.frontPrice * c.normF) →
  FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F3
      (Cfl * c.filterPrice * c.normF) →
    ReconFluxSumBody c kc Cfl hle F1 F2 F3

/-- **The conversion step: from the window theorem's output to `ReconBound`.** The glued lift is
the menu's lifted field (`stage_gluedLift_eq_menuLiftedRep`, `c_r = 1`, the weights of the natural
weak stage are the cutoffs), the coefficient is the stage's (`edgeCoefficient_actualFamily`,
`G_w.level = M`), the slots descend (the family step), the window is `[t_p, a + T₀]`, and the residual is
truncated to the common order `k₀ + ℓ` and moved from `r_s` to `r_* = c_K x` at the cost
`max(1, c_K)^{K_max}` (`factorialNormSq_truncateTorusHk_le`, `factorialNormSq_mono_radius`). -/
def ReconConvAt (_x : TermResAux c) (ℓ : ℕ) : Prop :=
  c.Gw.actualFamily.IsDescending (rK c ℓ) →
  ∀ (Xb : ℝ), 0 ≤ Xb →
  ∀ (û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (rK c ℓ v) (ScalarH v.1.root))
    (ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (rK c ℓ v + 1) (ScalarH v.1.root))
    (Rres : ∀ v : CompIn c.Gw.comps, ℝ →
      TorusHk (rK c ℓ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (qres : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (rK c ℓ v) (ScalarH v.1.root)),
    (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v,
      (û v t).toFunction.jet (valueIndex2 (rK c ℓ v)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => gluedLift (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
          (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
          (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c) (ocEpsilon c.D.q c.D.Λ M)
          (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT A.dW c.CcT
          (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
          (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)) c.aRep t y v) →
    IsCoupledWeakSolutionTorus (c.D.κ M) c.tp (c.tp + rTobs c) (streamVel (c.D.Φ M)) A.Dt (rK c ℓ)
      (edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
        (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) (fun v => û v c.tp) Rres qres û ŵ →
    (∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc c.tp (c.tp + rTobs c)))) →
    (∀ v, Integrable (qres v) (volume.restrict (Set.Icc c.tp (c.tp + rTobs c)))) →
    (c.D.κ M)⁻¹ * ∫ s in Set.Icc c.tp (c.tp + rTobs c),
        massNormSq (E := fun v : CompIn c.Gw.comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := rK c ℓ) (rRs c) (c.Gw.mass c.lawW) (fun v => (Rres v s).val) ≤ Xb ^ 2 →
    ∫ s in Set.Icc c.tp (c.tp + rTobs c),
        Real.sqrt (massNormSq (E := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (K := rK c ℓ)
          (rRs c) (c.Gw.mass c.lawW) (fun v => (qres v s).val)) ≤ Xb →
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M) (max 1 cK ^ rKmax A ℓ * Xb)

end Steps

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The partition bound of the window**. `partition_window_input` bounds the partition
terms of the approximants on a reconstruction window by
`C (1 + S_b)^H #pulses ℓ √(1/τ) e^{-cτ/ℓ²}` times their strong energy at the partition order
`rpord`. Its constants `(C, c)` depend on the orders and on the lift-setting constants `C_Gl, C_w, C_a` and the partition
constant `reconCpart`; they are fixed here by choice (`recPartC`, `recPartc`), so that the join and
the assembly use the same values. The two remaining inputs are steps:
- **Monotonicity of lift settings** (`LiftSettingMonoStatement`): a lift setting at orders `(K, k, L)` is one at lower
  orders, with the smoothness floors `qs, qf` recomputed;
- **Scale of the partition bound** (`ReconPartitionScaleAt`): the factor of
  `partition_window_input` is at most `C_px 𝔅_rec`.

Degenerate cases:
- `K' = K`, `k' = k`, `L' = L`: monotonicity is the identity when `qs, qf` already have the formula
  values (they do: `IsLiftSetting.qs_eq`, `qf_eq`).
- No observed pulse: the factor of `partition_window_input` is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.EntryTerminal.Route

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction}

/-- The constant `C` of `partition_window_input` at the window's orders. -/
def recPartC (A : TermArgs X) (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  Classical.choose (partition_window_input.{0, 0, 0, 0} (rAcl A) A.NT A.Dt A.dW (rKmax A ℓ)
    (rKlift A ℓ) (rLlift A ℓ) CGl Cw Ca reconCpart (le_max_left _ _))

/-- The rate `c` of `partition_window_input` at the window's orders. -/
def recPartc (A : TermArgs X) (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec (partition_window_input.{0, 0, 0, 0} (rAcl A) A.NT A.Dt
    A.dW (rKmax A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cw Ca reconCpart (le_max_left _ _)))

theorem recPartC_nonneg (A : TermArgs X) (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca : ℝ) :
    0 ≤ recPartC A ℓ CGl Cw Ca :=
  (Classical.choose_spec (Classical.choose_spec (partition_window_input.{0, 0, 0, 0} (rAcl A) A.NT
    A.Dt A.dW (rKmax A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cw Ca reconCpart (le_max_left _ _)))).1

theorem recPartc_pos (A : TermArgs X) (ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca : ℝ) :
    0 < recPartc A ℓ CGl Cw Ca :=
  (Classical.choose_spec (Classical.choose_spec (partition_window_input.{0, 0, 0, 0} (rAcl A) A.NT
    A.Dt A.dW (rKmax A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cw Ca reconCpart (le_max_left _ _)))).2.1

/-- **Monotonicity of lift settings**: a lift setting at orders `(K, k, L)` is a lift setting at
lower orders `(K', k', L')`, with the smoothness floors given by the formulas of
`IsLiftSetting.qs_eq`, `qf_eq`. -/
def LiftSettingMonoStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ},
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
    ∀ K' k' L' : ℕ, K' ≤ K → k' ≤ k → L' ≤ L →
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K' k' L'
      (K' + 4 * (H + 1) * (N + D) ^ 2) (max k' (L' + 2) + H * D + 2 * N + 2 * D) CG Cw Cj b Θ

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
