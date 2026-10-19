-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.InnerOrderFacts
import AVRegularity.Construction.Residual.Presentation.Cascade.Part1
import AVRegularity.Construction.Residual.Presentation.Cascade.GluedConclusion
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.Producer
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.Frontier.MarkerReadout.Producer
import AVRegularity.Construction.Preservation.Frontier.LengthPrice.Producer
import AVRegularity.Construction.Preservation.Frontier.LengthEnergy.Producer
public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterRows
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.SourcesA
import AVRegularity.Families.TorusCompatible.WeakStage

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Providers.WeakGen.Residual.CoarseDefect
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **B-recon at every context** (cascade side of the bill residual, the assembly of
`frameReconAt_of_steps` over the contexts).

`succPrefix_recon`: in the common prefix form, constants `(C_G, C_w, C_a, C_g, c_g, m_*)` and a
function `C_fl ↦ C` such that at every context of level `≥ m_*` with a nondegenerate window
`t_p < t_f`, under the quiet margin of the preparation endpoint, at the frame of every lifted field
with classical representatives, for every flux constant `C_fl`:

    The coarse reconstruction (`FrameReconCoarseAt`) →
      FrameReconAt F law k_c k_I.c₀ k_I.c_r c_g σ₀ L_c A_cl θ₁ θ₂ A_in C_fl (C C_fl)

at the coarse order `k_c = succKc` of the window. The other steps are discharged: the lift sequences, the lift settings
(`succPrefix_reconSetting`), the family side (`succPrefix_reconFamily`), the energy step (`succPrefix_reconEnergy`),
the coefficient step (`succPrefix_reconCoeff`, with the pointwise envelope `hpw` of the seed),
the partition and scale steps (`succPrefix_reconScalePartition`, evaluated at the constants of the lift settings), the flux-sum step and
Conv (`frameReconFluxSumAt_of_factor`, `frameReconConvAt_of_natural` with the facts of the
context). The gluing rate of the bill is the rate `c_g` of the partition.

The constant is `C = reconBillConst(…; C_G, C_w, C_a, C_I, C_g, C_s, max C_fs 0, C_px C_s)·C₁`
with `C_fs = radiusChangeFactor c_r⁻¹ k_c·C_fl`.

The case `t_p = t_f` is excluded here; `A_in = 0` and a stage without
identities are allowed. -/

/-- **B-recon at every context of level `≥ m_*` with `t_p < t_f`**, from the coarse reconstruction at the frame,
for the flux constant `C_fl`. -/
def ReconCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (CGl Cwl : ℕ → ℝ)
    (Ca Cgr cg Cfl C : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
      (hW : succKc r₀ D₀ H J N p Acl + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p),
      FrameReconCoarseAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl
        (succKc r₀ D₀ H J N p Acl) 0 hW kI.cr σ₀ Lc (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain Cfl CGl Cwl Ca CI Cgr →
      FrameReconAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law (succKc r₀ D₀ H J N p Acl)
        kI.c₀ kI.cr cg σ₀ Lc Acl (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain Cfl C

/-- **B-recon in the common prefix form** from the coarse reconstruction only; the constants are
`(C_G, C_w, C_a, C_g, c_g, C_fl ↦ C, m_*)` with `0 ≤ C_g`, `0 < c_g`. -/
theorem succPrefix_recon (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℝ × (ℝ → ℝ) × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.2.2.2.1 ∧ 0 < x.2.2.2.2.1 ∧
        ∀ Cfl : ℝ, ReconCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 Cfl
          (x.2.2.2.2.2.1 Cfl) x.2.2.2.2.2.2) := by
  have h1 := succPrefix_reconSetting α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_reconScalePartition α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h3 := succPrefix_reconEnergy α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h4 := succPrefix_reconFamily α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h5 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  have h6 := succPrefix_reconCoeff α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine (((((h1.and h2).and h3).and h4).and h5).and h6).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨⟨⟨⟨⟨CGl, Cwl, Ca, Cg, ms⟩, C₁, m₂, pf⟩, Cs, me⟩, mf⟩, Cread, mk⟩, mc⟩ := x
  obtain ⟨⟨⟨⟨⟨⟨hCg, hset⟩, hC₁, hscale, hpartf⟩, hCs, hen⟩, hfam⟩, -, hpk⟩, hcoef⟩ := hx
  obtain ⟨hcg, hCpx, hpart⟩ := hpartf CGl Cwl Ca Cg
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hD2 : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN1 : 1 ≤ N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  have hA1 : 1 ≤ Acl :=
    succSchedule_one_le_Acl hα₁ (ocDelta_pos_of_admissible hα₀ hq) hfacts.sched
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hCI : 0 ≤ CI := by
    obtain ⟨CIthr, Cwthr, hled⟩ := hfacts.ledger
    exact le_trans (le_trans zero_le_one hfacts.hCe) hled.1
  have hkc1 : 1 ≤ succKc r₀ D₀ H J N p Acl :=
    le_trans (le_trans (by norm_num) hD2) (le_wKcFloor _ _ _ _ _)
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  refine ⟨(CGl, Cwl, Ca, Cg, (pf CGl Cwl Ca).1,
    fun Cfl => reconBillConst (succSchedR r₀ J H) N (succSchedD D₀ N p (H + 1)) Acl
      (wKmax (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) 0)
      (wDens (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0)
      (wKres (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0)
      (wNchi (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0)
      (wKlift (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0)
      (wLlift (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N 0) CGl Cwl Ca CI Cg Cs
      (max (radiusChangeFactor kI.cr⁻¹ (succKc r₀ D₀ H J N p Acl) * Cfl) 0)
      ((pf CGl Cwl Ca).2.1 * Cs) * C₁,
    max (max (max ms (max m₂ (pf CGl Cwl Ca).2.2)) (max me mf)) (max mk mc)), hCg, hcg, ?_⟩
  intro Cfl hr _ _ _ _ _ _ _ c hm htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hW hR5
  have hms : ms ≤ c.m :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hm
  have hmp : max m₂ (pf CGl Cwl Ca).2.2 ≤ c.m :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hm
  have hme : me ≤ c.m :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hm
  have hmf : mf ≤ c.m :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hm
  have hmk : mk ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hmc : mc ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  obtain ⟨hgeom, -, -⟩ := hpk hk0 c hmk
  obtain ⟨hR2, hR3⟩ := hset c hms hgeom hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have hAin : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  have hπ := c.mass_pos hq.1 hfacts.hΛ
  have hΛD : 1 ≤ c.D.Λ := le_trans (by norm_num) (c.lambda_ge hfacts.hΛ)
  have hρ0 : 0 ≤ rhoStar c.D kI.c₀ c.m := (c.hlevel ▸ hgeom.2.2.2.2.2.2.2.2.1).le
  exact frameReconAt_of_steps (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law (s := s) Acl
    (succKc r₀ D₀ H J N p Acl) kI.c₀ kI.cr _ σ₀ Lc _ _ c.Ain Cfl _ C₁
    (lt_of_lt_of_le one_pos hC₁) hD2 hN1 hA1 le_rfl hW (sub_pos.2 htt) hAin _ _ _ CI _ _ _
    (radiusChangeFactor kI.cr⁻¹ (succKc r₀ D₀ H J N p Acl) * Cfl) hCI hCg hCs hCpx hR2 hR3
    (hfam c hmf CcT PZ aRep û hlift aZ aY hZ hY) hR5
    (hen c hme CcT PZ aRep û hlift aZ aY hZ hY hW)
    (hcoef c hmc CcT PZ aRep û hlift aZ aY hZ hY)
    (hpart c hmp htt CcT PZ aRep û hlift aZ aY hZ hY _ hW hkc1)
    (hscale c (le_trans (le_max_left _ _) hmp) htt CcT PZ aRep û hlift aZ aY hZ hY _)
    (frameReconFluxSumAt_of_factor (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law _ kI.cr σ₀ Lc
      _ _ c.Ain Cfl _ hcr (c.kappa_pred_pos hΛ1 hζ) hπ
      (mul_nonneg hAin (fTT_nonneg (c.frame CcT PZ aRep û hlift aZ aY hZ hY) kI.cr σ₀ Lc _ _
        (Construction.Stream.ocEpsilon_pos hΛD).le)) le_rfl)
    (frameReconConvAt_of_natural (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law 0 _ hρ0
      c.hlevel c.m_le_term hΛD (c.kappa_pos hΛ1 hζ) rfl c.weight_eq hπ)
    le_rfl

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.Construction.Preservation.Assembly AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **K3.1, inputs (S) and (R): the Schur bound and the regularity of the coefficients of
the full successor at a context** (the route of the frontier grade rows,
`Preservation/Frontier/GradeRows/AtData.lean`, for the root rows of the filter defect).

* `kernelSchur_filt_le`: the kernel Schur matrix of the coefficients of the edges of a mask,
  with regularizer constants `c ≤ c'`, is entrywise below the matrix of all the coefficients
  with `c'`; a Schur bound passes.
* `coeffReg_of_operator`: a kernel operator whose coefficients are the physical coefficients
  of a stage gives their regularity `CoeffReg`.
* `filterSchur_at_ctx`: at a context of large level, with the constants of the extended
  certificates, the record lengths, the enhanced radius, the pass scales and the native kernel
  operator (regularizer constants `max 1 c_ker`) chosen before the stage: `CoeffReg` of the full
  successor `G'` on `[t_p, t_f]` at the radius `rhoEnh` and the order `n`, and the Schur bound
  `1/8` of the root coefficients of `G'` with regularizer constants `1`, masses of `G'`, kernel
  widths of `G'`, diffusivity `κ_{m-1}`.

Special cases: a mask that keeps every edge (the comparison is `c ≤ c'` only); a successor
without edges (both matrices vanish). -/

/-- A Schur bound passes to a larger constant. -/
theorem schurBound_mono {ι : Type*} [Fintype ι] {θ θ' : ℝ} {b : ι → ι → ℝ}
    (h : SchurBound θ b) (hθ : θ ≤ θ') : SchurBound θ' b :=
  ⟨fun i => (h.1 i).trans hθ, fun i => (h.2 i).trans hθ⟩

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The Schur matrix of a mask with smaller regularizer constants is entrywise smaller.** -/
theorem kernelSchur_filt_le (G' : GenStage D hr Dm bw j₀)
    (pm : ∀ v u : CompIn G'.comps, G'.fam.Γ v u → Prop) (ν ρ : ℝ) (π : CompIn G'.comps → ℝ)
    (k : ℕ) (a b : ℝ) (c c' : ℕ → ℝ) (r : ∀ v u : CompIn G'.comps, G'.fam.Γ v u → ℝ)
    (hν : 0 < ν) (hrpos : ∀ v u γ, 0 < r v u γ) (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j ∧ c j ≤ c' j)
    (θ : ℝ)
    (h : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm a b c' r
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (fun v u γ (d : ↥(Finset.Icc 2 Dm)) => G'.physCoeff v u γ d.1))) :
    SchurBound θ (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm a b c r
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root)) (filtCoeff G' pm)) := by
  have he : ∀ i j, kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm a b c r
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root)) (filtCoeff G' pm) i j ≤
      kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm a b c' r
        (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
        (fun v u γ (d : ↥(Finset.Icc 2 Dm)) => G'.physCoeff v u γ d.1) i j := by
    intro i j
    unfold kernelSchurMatrix
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d _ => ?_) (norm_nonneg _)
    have hd : d.1 - 2 + 2 ≤ Dm := by
      have := Finset.mem_Icc.1 d.2
      omega
    obtain ⟨hc0, hcc⟩ := hc _ hd
    have hden : 0 < ν * r i j α ^ (d.1 - 2) := mul_pos hν (pow_pos (hrpos i j α) _)
    refine div_le_div_of_nonneg_right ?_ hden.le
    have hsn : (coefficientSeminorm ρ k a b (filtCoeff G' pm i j α d)).toReal ≤
        (coefficientSeminorm ρ k a b (G'.physCoeff i j α d.1)).toReal := by
      unfold filtCoeff
      split_ifs
      · exact le_rfl
      · rw [CycleComparison.Coarse.coefficientSeminorm_zero_coefficient, ENNReal.toReal_zero]
        exact ENNReal.toReal_nonneg
    exact mul_le_mul hsn hcc hc0 ENNReal.toReal_nonneg
  exact ⟨fun i => (Finset.sum_le_sum fun i' _ => he i i').trans (h.1 i),
    fun i' => (Finset.sum_le_sum fun i _ => he i i').trans (h.2 i')⟩

/-- **A kernel operator on the physical coefficients of a stage gives their regularity.** -/
theorem coeffReg_of_operator (G' : GenStage D hr Dm bw j₀) {a b ρ ν : ℝ} {n : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G'.comps => hr v.1.root)
      (Γ := G'.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν n Dm)
    (hB : R.B = fun v u γ (d : ↥(Finset.Icc 2 Dm)) => G'.physCoeff v u γ d.1) :
    CoeffReg G' a b ρ n := by
  intro i j α d
  have h1 := R.hB_meas i j α d
  have h2 := R.hB_smooth i j α d
  have h3 := R.hB_per i j α d
  have h4 := R.hB_fin i j α d
  rw [hB] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Stage

section Ctx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]

/-- **(S) and (R) at a context**, from the constants chosen before the stage. -/
theorem filterSchur_at_ctx (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ)
    (h128 : 128 ≤ Λ)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1)
    (mc : ℕ) (hcert : Frontier.ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p
      nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (Λl : ℕ) (hlength : UniformRecordLengths α q ζ Λl) (hΛl : Λl ≤ Λ)
    (mr : ℕ) (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr)
    (Cu : ℝ) (hscale : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu)
    (n : ℕ) (A : ℝ) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw n (succSchedD D₀ N p (H + 1))
      (fun j => max 1 (kI.cker j)) A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    (hm : max mc (max mr (max (mo + 3) (max ma (j₀ + 3)))) ≤ c.m) :
    CoeffReg c.G' c.tp c.tf (rhoEnh c.D kI.cr c.m) n ∧
    SchurBound (1 / 8) (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) (c.D.κ (c.m - 1))
      (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) n (succSchedD D₀ N p (H + 1)) c.tp c.tf
      (fun _ => 1)
      (fun v u γ => (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
        c.seedK c.freshK v u γ).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff c.G' (fun _ u _ => u.1 ∈ c.G.comps))) := by
  classical
  have hmc : mc ≤ c.m := by omega
  have hmr' : mr ≤ c.m := by omega
  have hmo' : mo + 1 ≤ c.m - 1 := by omega
  have hma : ma ≤ c.m := by omega
  have hjGr' : j₀ ≤ c.m - 1 := by omega
  have hm2 : 2 ≤ c.m := by omega
  have hiGr' : 1 ≤ c.m - 1 := by omega
  have hm1 : 1 ≤ c.m := by omega
  have hmterm : c.m ≤ c.D.term := c.m_le_term
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge h128
  have hζD : IsFastProfile c.D.ζ := c.hζ.symm ▸ hζ
  have hbandD := c.bandD
  have hGrlevel : c.G'.level = c.m - 1 := by rw [c.hactual.2.1, c.hlevel]
  have hGrI := hcert c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law
    c.hlaw c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hmc c.hmn c.hnM c.tA
    c.htA c.G c.G' c.hcascade c.hlevel c.hinv c.hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn c.G'.comps).1 :=
    AVRegularity.Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod
      (AVRegularity.Providers.CascadeInvariants.grade_le_of_succ
        (AVRegularity.Providers.CascadeInvariants.grade_le_of_cascade c.hseed.2.1 c.hcascade) c.hactual v)
  have hm2Gr v : compReserve kI (v : CompIn c.G'.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := c.hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : c.seed.fam.Γ v u), 1 ≤ (c.seed.fam.identity v u γ).record.birthExcess →
      (c.seed.fam.identity v u γ).record.length ≤ c.D.eps c.seed.level := by
    intro v u γ hb
    simpa only [c.hseed.1] using (c.hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength hr c.D c.hα c.hq c.hζ (by rw [c.hΛ]; omega) hbandD
    _ bw j₀ (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) Cw kI.cr σ₀
    (succEta0 α q s) N p hcrle c.seed c.G hseedI.2.1 hlens
    (by rw [c.hseed.1, c.hterm]; exact c.hnM.le) c.hcascade (c.hlevel.symm ▸ hm1)
  have hscl := hscale c.D c.hα c.hq c.hΛ c.hζ hbandD c.m hm2 hmterm
  have hlenGr := Frontier.extended_successor_record_lengths _ _ c.G c.G' c.hactual c.hinv.2.1
    hlenG (EntryScales.epsilon_antitone hqD hΛD (by rw [c.hactual.2.1]; omega))
    (by
      change freshLength c.D kI.cr (c.G.level - 1) ≤ c.D.eps c.G'.level
      rw [c.hactual.2.1, c.hlevel]
      simpa only [Nat.sub_add_cancel hm1] using
        AVRegularity.Providers.CascadeInvariants.freshLength_le_eps_of_passScales hcrle
          (show AVRegularity.Providers.CascadeInvariants.PassScales c.D ((c.m - 1) + 1) Cu from
            (Nat.sub_add_cancel hm1).symm ▸ hscl))
  have he (l : ℕ) : 0 < c.D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ c.D.term) : 0 < c.D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA c.D.α c.D.q c.D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs : 0 < rhoStar c.D kI.c₀ (c.m - 1) ∧ rhoStar c.D kI.c₀ (c.m - 1) ≤ c.D.eps (c.m - 1) := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he (c.m - 1)) (hκ (c.m - 1) (by omega))
      (ha (c.m - 1))
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he _).le hc0le)⟩
  have hrhos := hradius c.D c.hα c.hq c.hΛ c.hζ hbandD c.m hmr' hmterm
  have hρe : rhoEnh c.D kI.cr c.m ≤ c.D.eps c.G'.level := by
    rw [hGrlevel]
    exact hrhos.trans hrs.2
  have hρE : rhoEnh c.D kI.cr c.m ≤ c.D.eps (c.G'.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD hΛD (Nat.sub_le _ _))
  have hρpos : 0 < rhoEnh c.D kI.cr c.m := by
    unfold rhoEnh
    exact mul_pos hcrpos (Real.sqrt_pos.2 (mul_pos (hκ (c.m - 1) (by omega))
      (Construction.Stream.ocTauPP_pos (by omega))))
  have htptf : c.tp ≤ c.tf := c.tp_le_tf
  have hsub : Set.Icc c.tp c.tf ⊆ Set.Icc (c.tA + 3 * ocTau α q Λ c.m) c.tf :=
    fun t ht => ⟨c.entrance.trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : c.G'.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh c.D kI.cr c.m) 0
      (succSchedD D₀ N p (H + 1)) c.tp c.tf (fun j => max 1 (kI.cker j))
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width
      (c.G'.sysS (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
        hφ₀ v u γ) := by
    intro v u γ
    have hpos : 0 ≤ (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
        c.seedK c.freshK v u γ).width := by
      rw [(hker v u γ).1]
      exact (c.G'.fam.identity v u γ).record.width_pos.le
    exact spatial_regularizer_constants_mono
      (Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub) hpos
      (fun j _ => le_max_right _ _)
  have hkap : c.D.kap c.G'.level = c.D.κ (c.m - 1) := by
    change c.D.κ (min c.G'.level c.D.term) = _
    rw [Nat.min_eq_left (by omega), hGrlevel]
  have hsmall : A * (CI * c.D.eps (c.m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, c.hq, c.hΛ] using habs c.m hma
  have hlengthop : ∀ v u (γ : c.G'.fam.Γ v u), 3 ≤ (c.G'.fam.identity v u γ).maxOrder →
      (c.G'.fam.identity v u γ).record.length ≤ c.D.eps (c.G'.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (c.G'.fam.identity v u γ).record.birthExcess := by
      have hh := (c.G'.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD hΛD (Nat.sub_le _ _))
  have hop' := hop hr c.D c.hα c.hq c.hΛ c.hζ c.hseq j₀ c.Mnat c.G' kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hκ (c.m - 1) (by omega))
    hslot hmGr hm2Gr (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
    (fun v u γ => (hker v u γ).1) φ₀ hφ₀ c.tp c.tf
    (rhoEnh c.D kI.cr c.m) (CI * c.D.eps (c.m - 1) ^ min (ocDelta α q / 4) τe)
    (c.G'.mass c.law) (c.G'.marker c.law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD c.law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD c.law v.1) hled hsmall.le hSzero
  obtain ⟨R, hB, hC, -, hπ, hRr, hRc, hθ⟩ := hop' (fun _ => 1) (Or.inl rfl)
  refine ⟨coeffReg_of_operator c.G' R hB, ?_⟩
  have hs := R.hschur
  have hπ' : R.π = c.G'.mass c.law := by
    rw [hπ]
    funext v
    simp only [one_pow, div_one]
  rw [hB, hC, hπ', hRr, hRc, hθ, hkap] at hs
  have hf := kernelSchur_filt_le c.G' (fun _ u _ => u.1 ∈ c.G.comps) (c.D.κ (c.m - 1))
    (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) n c.tp c.tf (fun _ => 1)
    (fun j => max 1 (kI.cker j))
    (fun v u γ => (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
      c.seedK c.freshK v u γ).width)
    (hκ (c.m - 1) (by omega)) (fun v u γ => R.hr v u γ |>.trans_eq (by rw [hRr]))
    (fun j _ => ⟨zero_le_one, le_max_left _ _⟩) _ hs
  exact schurBound_mono hf hsmall.le

end Ctx

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The frontier inner flux in the common prefix form** (cascade side of the bill residual).

`prodPrefix`: the default-join frontier production at one grade, in the prefix form with the
constants `(C, m_*)`.  `dataMono`: a production at `(C₁, m₁)` holds at every `C ≥ |C₁|`,
`m_* ≥ m₁`.  `succPrefix_frontierInner`: `FrontierInnerPrefixStatement`, with the constant
`C³ |C_pr|` (`C` dominating both grades) and the level `max (j₀ + 2)` of the four levels. -/

/-- **A default-join production at `(C₁, m₁)` holds at `(C, m_*)` with `|C₁| ≤ C`, `m₁ ≤ m_*`.** -/
theorem dataMono {α s q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (hq1 : 1 < q)
    {Λ : ℕ} (hΛ : 128 ≤ Λ) {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {bw Ce τe : ℝ}
    {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ} {σ₀ : ℝ}
    {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ} {grade : Bool}
    {C₁ C : ℝ} {m₁ mStar : ℕ} (hC : |C₁| ≤ C) (hm : m₁ ≤ mStar)
    (h : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C₁ m₁ grade) :
    FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar grade := by
  refine frontier_data_and α s q ζ hζ hq1 Λ hΛ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres
    npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ grade C₁ C₁ C₁ C m₁ m₁ m₁ mStar hC hC hC hm hm hm ?_ ?_ ?_
  all_goals
    intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
      tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual
      tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom F
    have := h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n
      tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual tp Preg
      hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom
  · exact this.1
  · exact this.2.1
  · exact this.2.2

/-- **The default-join frontier production at one grade, in the prefix form.** -/
theorem prodPrefix (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (grade : Bool) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
          Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ x.1 x.2 grade) := by
  have hprod : FrontierAnalyticProductionStatement α s q ζ grade := by
    cases grade
    · exact frontier_analytic_production_and α s q ζ hζ hq.1 false
        (LengthPrice.length_rows_production hα₀ hα₁ hs₀ hs₁ hq hζ)
        (marker_readout_production hα₀ hα₁ hs₀ hs₁ hq ζ false)
        (LengthEnergy.length_source_energy_production hα₀ hα₁ hs₀ hs₁ hq hζ)
    · exact frontier_analytic_production_and α s q ζ hζ hq.1 true
        (grade_rows_production hα₀ hα₁ hs₀ hs₁ hq hζ)
        (marker_readout_production hα₀ hα₁ hs₀ hs₁ hq ζ true)
        (grade_source_energy_production hα₀ hα₁ hs₀ hs₁ hq hζ)
  refine SuccPrefix.of_tail (hprod : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ _hfacts htail CQ Cpr
  obtain ⟨C, mStar, h⟩ := htail CQ Cpr
  exact ⟨(C, mStar), h⟩

/-- `D_{H+1} ≥ 2`. -/
theorem D_ge_two (D₀ N p H : ℕ) : 2 ≤ succSchedD D₀ N p (H + 1) := by
  change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
  omega

/-! **K2b in the common prefix form: `FrontierInnerPrefixStatement`**.

The statement of `Cascade/CtxFrontierStatement.lean`, proved from the native inputs
(`succPrefix_nativeInput`), the regularizer clause (`succPrefix_regClause`) and the two frontier
productions (`prodPrefix`), via `form`.  The constant is `C³ |C_pr|` with `C` dominating
both production constants; the level is the largest of the four levels and `j₀ + 2`. -/

/-- **K2b at every context of level `≥ m_*`, in the common prefix form.** -/
theorem succPrefix_frontierInner (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : FrontierInnerPrefixStatement α s q ζ := by
  have h := (((succPrefix_nativeInput α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).and
    (succPrefix_regClause α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)).and
    (prodPrefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ true)).and
    (prodPrefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ false)
  refine SuccPrefix.imp h ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨⟨hN, hR⟩, hT⟩, hF⟩ := hx
  obtain ⟨⟨⟨mN, ⟨Creg, mR⟩⟩, ⟨Cg, mg⟩⟩, ⟨Cl, ml⟩⟩ := x
  simp only at hN hR hT hF
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hΛ := hfacts.hΛ
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ
  have hC0 : 0 ≤ max |Cg| |Cl| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hT' := dataMono (mStar := max mg (max ml (max mN (max mR (j₀ + 2))))) hζ hq.1 hΛ
    (le_max_left |Cg| |Cl|) (le_max_left _ _) hT
  have hF' := dataMono (mStar := max mg (max ml (max mN (max mR (j₀ + 2))))) hζ hq.1 hΛ
    (le_max_right |Cg| |Cl|) ((le_max_left ml _).trans (le_max_right mg _)) hF
  have hKs := Kres_le_Ks hkI
  obtain ⟨hord, hDk⟩ := orders hfacts.recon
  refine ⟨(max |Cg| |Cl| ^ 3 * |Cpr|, max mg (max ml (max mN (max mR (j₀ + 2))))), ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg hC0 3) (abs_nonneg _)
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  have hmN : mN ≤ c.m := (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hm
  have hmR : mR ≤ c.m := (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _)))).trans hm
  have hjm : j₀ + 2 ≤ c.m := (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_right _ _)))).trans hm
  obtain ⟨hi⟩ := hN c hmN CcT PZ aRep û hlift aZ aY hZ hY
  have hbw : 0 < bw := hfacts.hbw
  have hsupp := hfacts.support
  have hk : succKc r₀ D₀ H J N p Acl + 2 * p ≤ kI.Ks := by
    have := hfacts.hNaux
    omega
  have hST : c.G'.IsSlotTransverse := by
    obtain ⟨k0, hcert, -⟩ := hi.outgoing_context
    exact native_context_slot_transverse (by rw [c.hΛ]; exact hΛ1) hbw hcert
  exact c.form CcT PZ aRep û hlift aZ aY hZ hY hi hST hα₀ hα₁ hs₀ hs₁ hq hq.1 hζ hΛ hbw hjm
    hfacts.smooth (Construction.KernelDefect.kd_hasCompactSupport hsupp) hsupp hord hDk
    (D_ge_two D₀ N p H) hfacts.hNaux
    (hR c hmR _ hk) hC0 hm hT' hF'

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.ActualMeans
open AVRegularity.Construction.Preservation AVRegularity.EntryWeakProofs
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- High-order pulse input from the proved cascade settings and sequences, at 3τ entrance. -/
theorem pulseInput {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N kc : ℕ, 2 ≤ Dm → 1 ≤ N → ∃ m₁ : ℕ, 2 ≤ m₁ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (F : Frame D hr Dm bw j₀) (law : BirthLaw) (hφ₀ : Integrable F.φ₀)
      (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G →
    F.depth = H → F.N = N → F.G.level = F.m → m₁ ≤ F.m → F.m < D.term → j₀ ≤ F.m →
    F.G.fam.HasDepthAtMost H →
    (∀ v : CompIn F.G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn F.G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (F.G.fam.identity v u γ).record.birthExcess →
      (F.G.fam.identity v u γ).record.length ≤ D.eps F.G.level) →
    F.Mn.lenFactor = 1 →
    tA + 3 * ocTau D.α D.q D.Λ F.m ≤ F.tp → F.tp ≤ tB →
    Set.Icc (F.tp - ocTauP D.α D.q D.Λ F.m) (F.tp + ocTauP D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m →
    Nonempty (PulseInput F law kc) := by
  obtain ⟨Λ₁, hΛ₁, hseq⟩ := frameReconSeqAt hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₂, hΛ₂, hset⟩ := frameReconSettingBody hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λ₁ Λ₂, hΛ₁.trans (le_max_left _ _), fun Λ hΛ bw hbw Dm H N kc hDm hN => ?_⟩
  let A := kc + (H + 3) * (N + Dm + 12)
  obtain ⟨m₁, hm₁, hseqF⟩ := hseq Λ ((le_max_left _ _).trans hΛ) bw hbw Dm H N A 0 hDm hN
  obtain ⟨CG, Cw, Ca, Cg, m₂, hm₂, -, hsetF⟩ :=
    hset Λ ((le_max_right _ _).trans hΛ) bw hbw Dm H N A 0 hDm hN
  refine ⟨max m₁ m₂, hm₁.trans (le_max_left _ _), ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK hinv hH hNN
    hlev hm hmt hj hdepth hres hres2 hlen hone hentry htp hquietMargin
  have hseqAt := hseqF hr D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK
    hinv hH hNN hlev ((le_max_left _ _).trans hm) hmt hj hdepth hres hres2 hlen hone hentry htp hquietMargin
  have hsetAt := hsetF hr D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK
    hinv hH hNN hlev ((le_max_right _ _).trans hm) hmt hj hdepth hres hres2 hlen hseqAt S le_rfl
  refine ⟨{
    K := wKlift Dm F.depth F.N A 0
    L := wLlift Dm F.depth F.N 0
    order := ?_
    CG := CG
    Cw := Cw
    Cj := fun _ _ => Ca
    qs := wQs Dm F.depth F.N A 0
    qf := wQf Dm F.depth F.N 0
    par := pulseParallel
    V := fun k => pulseShearProfile D.α D.q D.Λ F.m D.ζ (D.κ F.m) k
    price := S
    settings := hsetAt.1
    sequences := hseqAt }⟩
  have hA : fNc F kc = A := by simp only [fNc, A, hH, hNN]; ring
  rw [hA]
  simp only [wKlift]
  omega

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the letters statement `FrameReconLettersAt` at a cascade frame. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The letters statement `FrameReconLettersAt`, with numeric thresholds before carriers and
frames and the cascade 3τ entrance. -/
theorem frameReconLetters {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N kc : ℕ, 2 ≤ Dm → 1 ≤ N → ∃ m₁ : ℕ, 2 ≤ m₁ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (F : Frame D hr Dm bw j₀) (law : BirthLaw) (hφ₀ : Integrable F.φ₀)
      (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G →
    F.depth = H → F.N = N → F.G.level = F.m → m₁ ≤ F.m → F.m < D.term → j₀ ≤ F.m →
    F.G.fam.HasDepthAtMost H →
    (∀ v : CompIn F.G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn F.G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (F.G.fam.identity v u γ).record.birthExcess →
      (F.G.fam.identity v u γ).record.length ≤ D.eps F.G.level) →
    F.Mn.lenFactor = 1 →
    tA + 3 * ocTau D.α D.q D.Λ F.m ≤ F.tp → F.tp ≤ F.tf → F.tf ≤ tB →
    Set.Icc (F.tp - ocTauP D.α D.q D.Λ F.m) (F.tp + ocTauP D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m →
    FrameReconLettersAt F law kc := by
  obtain ⟨Λ₁, hΛ₁, hinput⟩ := pulseInput hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₂, hΛ₂, hgeometry⟩ := windowGeometry hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λ₁ Λ₂, hΛ₁.trans (le_max_left _ _), fun Λ hΛ bw hbw Dm H N kc hDm hN => ?_⟩
  obtain ⟨m₁, hm₁, hinputF⟩ := hinput Λ ((le_max_left _ _).trans hΛ) bw hbw Dm H N kc hDm hN
  obtain ⟨m₂, hm₂, hgeometryF⟩ := hgeometry Λ ((le_max_right _ _).trans hΛ)
  refine ⟨max m₁ m₂, hm₁.trans (le_max_left _ _), ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK hinv hH hNN
    hlev hm hmt hj hdepth hres hres2 hlen hone hentry htp htf hquietMargin
  have h128 : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ₁.trans ((le_max_left _ _).trans hΛ)
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hband' : IsOCBandChain α q Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  obtain ⟨g⟩ := hgeometryF D hDα hDq hDΛ hDζ hΦ hband' F law kc
    ((le_max_right _ _).trans hm) hmt.le (by rw [hNN]; omega) htp
  obtain ⟨p⟩ := hinputF hr D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK
    hinv hH hNN hlev ((le_max_left _ _).trans hm) hmt hj hdepth hres hres2 hlen hone hentry
    (htp.trans htf) hquietMargin
  have hν : 0 < D.κ F.m := CycleReference.bandChain_pos
    (by rw [← hDΛ]; exact hΛ1) hζ hband' hmt.le
  have hseq' : IsOCStreamSeq α q D.Λ ζ D.Φ := hDΛ.symm ▸ hΦ
  have cb := chartBounds hα0 hα1 hs0 hs1 hq hζ F hDα hDq hseq' h128
    (hm₁.trans ((le_max_left _ _).trans hm)) hν
  have hdepthF : F.G.fam.HasDepthAtMost F.depth := hH.symm ▸ hdepth
  have htA : tA ≤ F.tp := le_trans (le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (Construction.Stream.ocTau_pos hΛ1).le)) hentry
  have hfamily := frameReconFamilyBody F law hφ₀ Mnat kI tA tB S θK hinv hlev hmt.le hΛ1
    hζD hdepthF htA htf 0
  obtain ⟨m⟩ := pulseModel_of_input F law kc p g h128 hν hDm hfamily cb.jets
  obtain ⟨budget⟩ := meanBudget_of_model F law kc p m g h128 hν hζD cb hfamily
  exact lettersAt_of_budget F law kc hdepthF g budget

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The reconstruction defect at every context** (cascade side of the bill residual): the
`frameReconDefectConvAt` with its named hypotheses discharged.

* `frameReconDefectConvAt_of_native`: at a frame with a native input `NativeInput F`
  (incoming and outgoing certificates, naturality, levels, band and profile, menu equalities, the
  order floors), the torus compatibility of the incoming family and `lenFactor = 1`,
  `FrameReconDefectConvAt` for every order and every constant. The glue
  (`CovTruncGluedPeriodicBounded` on the window) is `frame_gluedPeriodic` from the slow
  periodicity of the lift coefficients, which the lift sequences and settings of the window give
  (`frame_liftSlow`; both are premises of `FrameReconDefectConvAt`). The joint smoothness of
  the actual flux coefficients is `native_actual_flux_joint_contDiff` from the incoming
  certificate.
* `succPrefix_reconDefectConvCtx`: `ReconDefectConvCtxAt` in the common prefix form, from the
  native inputs at every context (`succPrefix_nativeInput`) and the stage invariant.

A stage without identities is allowed. -/

section
section Frame

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux coefficients of the actual contexts of the incoming stage are jointly smooth. -/
theorem frame_actualFluxJointSmooth (F : Frame D hr Dm b j₀) (hi : NativeInput F) :
    Construction.Preservation.Residual.FluxCancellation.CovFluxReg.ActualFluxJointSmooth F.G := by
  obtain ⟨kG, hcertG, hresG⟩ := hi.incoming_context
  have hΛ := hi.stage.base
  have hb := hi.stage.bandwidth
  have hslotG := native_context_slot_transverse hΛ hb hcertG
  have hlev2 := hi.stage.level
  have hε : 0 < D.eps (F.G.level - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos hΛ
  intro p v u γ d I t ht n
  exact Construction.Preservation.FullLift.native_actual_flux_joint_contDiff hcertG hslotG
    hi.stage.natural (by omega) (by omega) hb hε p v u γ d I (hresG v)
    (GenStage.compReserve_le_two kG v.1) n t ht

/-- **The reconstruction defect at a frame from a native input**, for every order and every constant. -/
theorem frameReconDefectConvAt_of_native (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (hi : NativeInput F) (htorus : IsTorusCompatible F.G.fam F.G.actual (D.eps (F.G.level - 1)))
    (hlen : F.Mn.lenFactor = 1) {Acl kc ℓ : ℕ} (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) :
    FrameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr := by
  intro hmacro F1 F2 F3 h1 h2 h3 hc hseq hset
  obtain ⟨qs, qf, par, V, bM, hsb⟩ := hset
  have hΛ := hi.stage.base
  have hζ := hi.stage.profile
  have hband := hi.stage.band
  have hlev : F.G.level = F.m := hi.level
  have htop : F.m ≤ D.term := hlev ▸ hi.stage.top
  have hj2 : j₀ + 2 ≤ F.m := hlev ▸ hi.stage.level
  have hν : 0 < D.κ F.m := CycleReference.bandChain_pos hΛ hζ hband htop
  have hνp : 0 < D.κ (F.m - 1) := CycleReference.bandChain_pos hΛ hζ hband (by omega)
  have hρ : fRho F ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos hνp (Construction.Stream.ocTauPP_pos hΛ))).ne'
  have htorusA : IsTorusCompatible F.G.actualFamily (fun _ => ())
      (ocEpsilon D.q D.Λ (F.m - 1)) := by
    have ht := F.G.isTorusCompatible_actualFamily htorus
    rw [hlev] at ht
    exact ht
  have hslow := frame_liftSlow F law hΛ hν htop htorusA hseq hsb
  have hglue := frame_gluedPeriodic F hΛ hν htop (by omega) hlev hlen hρ htorus hslow
  have hslowF := hi.slow
  have hfastF := hi.fast
  have hX : F.Mn.sX = F.sX := hi.menuSlow
  have hZ : F.Mn.sZ = F.sZ := hi.menuFast
  have hFF : FrameFacts F :=
    { level := hlev, menuN := hi.menuN.symm, menuX := hX.symm, menuZ := hZ.symm, base := hΛ,
      profile := hζ, band := hband, order := hi.stage.order,
      smooth := frame_actualFluxJointSmooth F hi,
      xfloor := by rw [hX]; omega, zfloor := by rw [hZ]; omega }
  obtain ⟨k0, hcert, hres⟩ := hi.outgoing_context
  have hST := native_context_slot_transverse hΛ hi.stage.bandwidth hcert
  have hl' : F.G'.level = F.m - 1 := by
    have := hi.actual.2.1
    rw [hlev] at this
    exact this
  have hε' : 0 < D.eps (F.G'.level - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos hΛ
  have hK : 2 * F.p + Dm ≤ F.Naux := by
    have := hi.auxiliary
    omega
  exact frameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb
    Cgr hFF hglue hcert hST hi.actual.2.2.2.1 (nativeUpsilon_shift hi) (by omega) (by omega)
    hi.stage.bandwidth hε' hres hi.smooth hi.support hK hi.stage.natural hlev hlen (by omega) htop
    hmacro F1 F2 F3 h1 h2 h3 hc hseq ⟨qs, qf, par, V, bM, hsb⟩

end Frame

/-- **The reconstruction defect at every context** in the common prefix form; the constant is the level `m_*`. -/
theorem succPrefix_reconDefectConvCtx (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconDefectConvCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x) := by
  refine (succPrefix_nativeInput α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  refine ⟨x, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm _htt _hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hW hf Cfl CGl Cwl Ca
    Sb Cgr
  obtain ⟨hi⟩ := hx c hm CcT PZ aRep û hlift aZ aY hZ hY
  exact frameReconDefectConvAt_of_native (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law hi
    c.hinv.isTorusCompatible rfl hW hf kI.cr σ₀ Lc _ _ c.Ain Cfl CGl Cwl Ca Sb Cgr
end

/-! **The fine tail bound at every context** (cascade side of the bill residual, the discharge of
the `frameFineDefectAt` and of the assembly `frameFineTail_of_lift_defect`).

`succPrefix_fineTail`: in the common prefix form, constants `(C, m_*)` such that at every context
of level `≥ m_*`, at the frame of every lifted field of the context with classical
representatives whose lifted field is jointly measurable on the window,
`FrameFineTailAt F law k_I.c₀ L_f A_in C`: the hypothesis `h4` of `frameResidualBound_of_parts`.

* the lift step of the fine tail is `succPrefix_fineLift` at the order `K = D_* + L_f`, and `D_* = D_m − 2`, so the order
  condition `(D_m − 2) + L_f ≤ K` of the defect is an equality;
* the constant of the defect is `stageFineMconst φ₀ L_f D_m 0 (max Γ_k 0) c_ker / 8`: the kernel
  price bound of the invariant, `θ_K = C_I·ε_{m−1}^{q·min(δ/4, τ_e)}`, is `≤ 1/8` from the level
  of `succPrefix_levelFloor` on, and the kernel derivative constants are `≥ 1`
  (`succPrefix_ckerPos`).

For a stage without identities the defect vanishes; `L_f = 0` is excluded by the
schedule (`q σ_f L_f > Q + 4`). -/

/-- **The fine tail bound at every context of level `≥ m_*`**, with the constant `C`. -/
def FineTailCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Lf : ℕ) (C : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) →
      FrameFineTailAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀ Lf c.Ain C

/-- **The fine tail bound in the common prefix form**; the constants are `(C, m_*)`. -/
theorem succPrefix_fineTail (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FineTailCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Lf x.1 x.2) := by
  have h1 := succPrefix_fineLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  have h3 := succPrefix_ckerPos α s q
  have h4 := succPrefix_levelFloor α s hα₀ q hq
  refine ((h1.and h2).and (h3.and h4)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨hfl, -, hpk⟩, hck, hfloor⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcpos : ∀ j, j + 2 ≤ succSchedD D₀ N p (H + 1) → 0 < kI.cker j :=
    fun j _ => lt_of_lt_of_le one_pos (hck j)
  have hMnn : 0 ≤ stageFineMconst φ₀ Lf (succSchedD D₀ N p (H + 1)) 0 (max kI.Γk 0) kI.cker :=
    stageFineMconst_nonneg φ₀ Lf _ 0 (le_max_right _ _) hcpos
  refine ⟨(stageFineMconst φ₀ Lf (succSchedD D₀ N p (H + 1)) 0 (max kI.Γk 0) kI.cker * (1 / 8) *
    x.1.1.1, max (max x.1.1.2 x.1.2.2) (max x.2.2 2)), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY hmeas
  have hm1 : x.1.1.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : x.1.2.2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : x.2.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm4 : 2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  obtain ⟨hgeom, -, -⟩ := hpk hk0 c hm2
  obtain ⟨-, -, -, hj, -, hres, -, -, hρ0, hρε⟩ := hgeom
  have hqD : 1 < c.D.q := by rw [c.hq]; exact hq.1
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hΛ]; exact hfacts.hΛ
  have hΛ1 : 1 ≤ c.D.Λ := le_trans (by norm_num) hΛD
  have hmt : c.m ≤ c.D.term := by rw [c.hterm]; exact le_trans c.hmn c.hnM.le
  have hkap : c.D.kap c.G.level = c.D.κ c.m := by
    unfold OCData.kap
    rw [c.hlevel, min_eq_left hmt]
  have hκ : 0 < c.D.κ c.m :=
    CycleReference.bandChain_pos (le_trans (by norm_num) hfacts.hΛ) hζ c.hband
      (le_trans c.hmn c.hnM.le)
  have hθ : CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe) ≤ 1 / 8 := by
    show CI * ocEpsilon c.D.q c.D.Λ (c.m - 1) ^ _ ≤ 1 / 8
    rw [c.hq, c.hΛ]
    exact (hfloor c.m hm3).1
  have hsmall : kI.Cwid * c.D.eps c.G.level ^ kI.σf ≤ 1 := by
    show kI.Cwid * ocEpsilon c.D.q c.D.Λ c.G.level ^ _ ≤ 1
    rw [c.hq, c.hΛ, c.hlevel]
    exact (hfloor c.m hm3).2
  have hA : c.tA ≤ c.tp := by
    have h1 := c.hs₀
    have h2 : c.s₀ ≤ c.tp := c.hprep.2.1
    have hτ : 0 < ocTau α q Λ c.m :=
      Construction.Stream.ocTau_pos (le_trans (by norm_num) hfacts.hΛ)
    linarith
  have hi : 1 ≤ c.G.level := by rw [c.hlevel]; omega
  have hκ' : 0 < c.D.kap c.G.level := by rw [hkap]; exact hκ
  have hρ : 0 < rhoStar c.D kI.c₀ c.m := c.hlevel ▸ hρ0
  have hρε' : rhoStar c.D kI.c₀ c.m ≤ c.D.eps (c.G.level - 1) :=
    (c.hlevel ▸ hρε : rhoStar c.D kI.c₀ c.m ≤ c.D.eps c.m).trans (by
      rw [c.hlevel]
      exact Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _))
  have hLf : Lf ≤ kI.Lker :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdef := frameFineDefectAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law hφ₀
    hfacts.smooth hfacts.nonneg hfacts.mass hfacts.support c.Mnat kI c.tA c.tf _ _ c.hinv hres
    hqD hΛD hi hj hfacts.hbw (Construction.Stream.ocEpsilon_pos hΛ1) hκ'
    (Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H) hθ
    (succDstar D₀ N p H + Lf) Lf kI.c₀ c.hlevel hkap rfl hρ hρε' hLf le_rfl hsmall hcpos hA le_rfl
    _ (mul_le_mul_of_nonneg_left (max_le hθ (by norm_num)) hMnn)
  exact frameFineTail_of_lift_defect (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
    (hfl c hm1 CcT PZ aRep û hlift aZ aY hZ hY hmeas) hdef

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
