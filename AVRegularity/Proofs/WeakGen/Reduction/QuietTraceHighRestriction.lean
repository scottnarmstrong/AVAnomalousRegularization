-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Reduction.ScalarIdentification
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.Proofs.WeakGen.Reduction.ScalarForced
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The higher order of the weak reduction** (shared higher-order lemma, consistency half).

Every weak reduction at the order `K_w` is the truncation of the coupled families at the reduction
reserves `K_w + m` plus the descending reserve, for every order offset `m` (the reserves do not
depend on `D_m`). The proof is over the raw data `S : WeakRawSetting R` and a clock
`K : WeakRawClock S`, so that it serves both the weak entry and a passage instance.

* `weakStage_passage_identified`: one passage. The given passage solution, truncated to order
  zero (`kernel_solution_truncate_torus`), is a width-zero kernel solution of a triangular system
  with identity kernels; the coupled passage family from a trace with the same order-zero value
  is identified with it (`kernel_solution_identified`, row by row in rank order).
* `weakStage_agreeZero_root`, `weakStage_agreeZero`: the root, where the only component `⟨0, []⟩`
  has the value `θ(t)` in both families from the root time on, then downward induction over the
  passages.
* `weakStage_coupled_consistent`: the values agree after truncation to `K_w` (a carrier is
  determined by its value, `TorusHk.ext_value`): the root on `[t_root, T]`, the level `i - 1` on
  `[t_i, T]`; the gradient lifts agree at almost every time.
* `weakStage_higher`: for every reduction at `K_w` on the clock and every `m`, coupled families at
  the reserves raised by `m`, solving every passage, whose truncations are the reduction.
* `weakReduction_higher`: the weak entry (`weakEntryRawSetting g`, `weakEntryRawClock s`, root
  time `t_{M+J_w+1}`), with the windows `[t_{j+1}, T]` for `M ≤ j ≤ M + J_w`.
* `weakReduction_higher_reduction`: the form used downstream, a weak reduction at the order `K_w + m`
  whose truncation to `K_w` is `r` (from the families at the offset `m + D_m - 2`).

The degenerate cases are included:
- `m = D_m - 2`: the families of `weak_entry_reduction`, truncated to `K_w`, are `r` itself.
- `J_w = 1`: one passage; the root window is `[t_root, T]` and the level-`M` window `[t_{M+1}, T]`.
- `θ = 0`: both families vanish (uniqueness of every row from zero data).
- A passage instance: `t_root = t_{M+J_w}`, strictly after the start because
  `t_{M+J_w+1} + τ' ≤ t_{M+J_w}`; the root at the reserves is not claimed at the start itself. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs Comparison

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Two carriers whose values agree almost everywhere have the same order-zero truncation. -/
theorem truncate_zero_eq_of_jet_ae {k k' : ℕ} (X : TorusHk k E) (Y : TorusHk k' E)
    (h : X.toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      Y.toFunction.jet (valueIndex2 k')) :
    truncateTorusHk (Nat.zero_le k) X = truncateTorusHk (Nat.zero_le k') Y := by
  apply TorusHk.ext_value
  change X.val (valueIndex2 k) = Y.val (valueIndex2 k')
  refine Lp.ext ?_
  filter_upwards [periodicJetRepresentative_ae X.val (valueIndex2 k),
    periodicJetRepresentative_ae Y.val (valueIndex2 k'), h] with y h1 h2 h3
  exact h1.symm.trans (h3.trans h2)

/-- A carrier whose order-zero truncation is that of a lower-order carrier truncates to it. -/
theorem truncate_eq_of_truncate_zero_eq {k k' : ℕ} (hk : k ≤ k') (X : TorusHk k' E)
    (Y : TorusHk k E)
    (h : truncateTorusHk (Nat.zero_le k') X = truncateTorusHk (Nat.zero_le k) Y) :
    truncateTorusHk hk X = Y :=
  TorusHk.ext_value (congrArg (fun z : TorusHk 0 E => z.val (valueIndex2 0)) h)

/-- **The gradient lifts agree** almost everywhere once the values agree after truncation. -/
theorem lift_truncate_ae {a b : ℝ} {k k' : ℕ} (hk : k ≤ k') {U' : ℝ → TorusHk k' E}
    {W' : ℝ → TorusHk (k' + 1) E} {U : ℝ → TorusHk k E} {W : ℝ → TorusHk (k + 1) E}
    (hv : ∀ t ∈ Set.Icc a b, truncateTorusHk hk (U' t) = U t)
    (h₁ : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ k') (W' t) = U' t)
    (h₂ : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ k) (W t) = U t) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.succ_le_succ hk) (W' t) = W t := by
  filter_upwards [h₁, h₂, ae_restrict_mem measurableSet_Icc] with t ht₁ ht₂ ht
  apply TorusHk.ext_value
  rw [show (W t).val (valueIndex2 (k + 1)) =
    (truncateTorusHk (Nat.le_succ k) (W t)).val (valueIndex2 k) from rfl, ht₂, ← hv t ht, ← ht₁]
  rfl

end Carrier

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **A width-zero regularized solution of a triangular stage is identified at order zero** with
every coupled solution at larger reserves from data with the same order-zero value
(`kernel_solution_identified` after truncation to order zero, at the instance path of
`GenStage.IsRegSolution`). -/
theorem regSolution_identified (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀) {ν t₀ t₁ ρ : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {D' k Kmax : ℕ} {K : CompIn G.comps → ℕ}
    {A : ∀ v u, (d : admissibleOrders K D' v u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => hr u.1.root) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => hr v.1.root)}
    (hd : TorusDriftData ν ρ t₀ t₁ bv Kmax) (hab : t₀ ≤ t₁) (hρ : 0 < ρ) (hν : 0 < ν)
    (hD : D' ≤ Dm) (hD' : 2 ≤ D')
    (hA : ∀ v u d s y, A v u d s y = ∑ γ : G.fam.Γ v u, G.physCoeff v u γ d.1 s y)
    (hP : ∀ v u (γ : G.fam.Γ v u) n, n ∈ Finset.Icc 2 Dm → n ∉ admissibleOrders K D' v u →
      ∀ s y, G.physCoeff v u γ n s y = 0)
    (r : CompIn G.comps → ℕ) (htri : ∀ v u, Nonempty (G.fam.Γ v u) → r u < r v)
    (hS : ∀ v u γ s, G.sysS P seedK freshK φ₀ hφ₀ v u γ s = ContinuousLinearMap.id ℝ _)
    {f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)}
    {U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (hreg : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f (fun _ _ => 0) (fun _ _ => 0)
      U W Y)
    {f' : ∀ v : CompIn G.comps, TorusHk (K v) (hr v.1.root)}
    {u' : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    {w' : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)}
    (hc : IsCoupledWeakSolutionTorus ν t₀ t₁ bv D' K A f' (fun _ _ => 0) (fun _ _ => 0) u' w')
    (hf : ∀ v, truncateTorusHk (Nat.zero_le _) (f' v) = truncateTorusHk (Nat.zero_le k) (f v)) :
    ∀ v, ∀ t ∈ Set.Icc t₀ t₁,
      truncateTorusHk (Nat.zero_le _) (u' v t) = truncateTorusHk (Nat.zero_le k) (U v t) :=
  kernel_solution_identified (P := fun v u γ n => G.physCoeff v u γ n) hd hab hρ hν hD hD' hA hP
    r htri hS (Providers.kernel_solution_truncate_torus t₀ t₁ ν bv 0 k Dm (Nat.zero_le k) _ _ _ _ _
      _ _ _ _ hreg) hc hf (fun _ _ => (ContinuousLinearMap.map_zero _).trans (ContinuousLinearMap.map_zero _).symm)
    (fun _ _ => (ContinuousLinearMap.map_zero _).trans (ContinuousLinearMap.map_zero _).symm)

end Stage

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

theorem weakReductionReserve_kw_le (R : WeakPassageRequest A) (m : ℕ) (c : Comp) :
    R.Kw ≤ weakReductionReserve R m c :=
  (Nat.le_add_right _ _).trans (weakReductionReserve_kw R m c)

/-- The diffusivity and the drift hypotheses of `coupled_energy_torus` at the level `i - 1` of a
passage, on any window. -/
theorem weakStage_level_drift (S : WeakRawSetting R) (hM2 : 2 ≤ S.M) (i : ℕ) (hMi : S.M < i)
    (hi : i ≤ S.M + A.Jw) (t₀ t₁ : ℝ) (Kmax : ℕ) :
    0 < S.D.kap (S.stage (i - 1)).level ∧ ∃ ρ : ℝ, 0 < ρ ∧
      TorusDriftData (S.D.kap (S.stage (i - 1)).level) ρ t₀ t₁
        (streamVel (S.D.Φ (S.stage (i - 1)).level)) Kmax := by
  have hlevel : (S.stage (i - 1)).level = i - 1 := S.level_eq (i - 1) (by omega) (by omega)
  have hν : 0 < S.D.kap (S.stage (i - 1)).level :=
    EntryWeakProofs.weakData_kap_pos S.D S.lambda_pos S.profile S.band' _
  have hm1 : 1 ≤ (S.stage (i - 1)).level := by rw [hlevel]; omega
  obtain ⟨ρ₀, hρ₀, hdrift⟩ := stream_torusDriftData B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ A.Λ S.base128 S.D.Φ S.streams (S.stage (i - 1)).level hm1 hν t₀ t₁ Kmax
  exact ⟨hν, ρ₀, hρ₀, hdrift ρ₀ hρ₀ le_rfl⟩

/-- The order-zero value of the reduction trace is that of a terminal trace whose old values have
the same order-zero value. -/
theorem weakStageTrace_truncate_zero (S : WeakRawSetting R) (m i : ℕ)
    (Ui : WeakStageFamily S m i) (t : ℝ)
    {U : ∀ v : CompIn (S.stage i).comps, TorusHk R.Kw (ScalarH v.1.root)}
    {Ub₀ : ∀ v : CompIn (S.stage (i - 1)).comps, TorusHk R.Kw (ScalarH v.1.root)}
    (htr : IsTerminalTrace (S.stage i) (S.stage (i - 1)) U Ub₀)
    (htrace : ∀ v, truncateTorusHk (Nat.zero_le _) (Ui v t) =
      truncateTorusHk (Nat.zero_le _) (U v))
    (v : CompIn (S.stage (i - 1)).comps) :
    truncateTorusHk (Nat.zero_le _) (weakStageTrace S m i Ui t v) =
      truncateTorusHk (Nat.zero_le R.Kw) (Ub₀ v) := by
  by_cases hv : v.1 ∈ (S.stage i).comps
  · exact (congrArg (truncateTorusHk (Nat.zero_le _))
      (weakStageTrace_old S m i Ui t v hv)).trans
      ((htrace ⟨v.1, hv⟩).trans (congrArg (truncateTorusHk (Nat.zero_le R.Kw)) (htr.1 v hv)).symm)
  · have h1 : truncateTorusHk (Nat.zero_le (weakReductionReserve R m v.1))
        (weakStageTrace S m i Ui t v) = 0 :=
      (congrArg (truncateTorusHk (Nat.zero_le _)) (weakStageTrace_new S m i Ui t v hv)).trans
        (ContinuousLinearMap.map_zero _)
    have h2 : truncateTorusHk (Nat.zero_le R.Kw) (Ub₀ v) = 0 :=
      (congrArg (truncateTorusHk (Nat.zero_le R.Kw)) (htr.2 v hv)).trans (ContinuousLinearMap.map_zero _)
    exact h1.trans h2.symm

/-- The edges of a stage of the reduction lower the rank. -/
theorem weakStage_rank_lt (S : WeakRawSetting R) (i : ℕ) (hMi : S.M ≤ i)
    (hi : i ≤ S.M + A.Jw) (v u : CompIn (S.stage i).comps)
    (h : Nonempty ((S.stage i).fam.Γ v u)) : weakComponentRank u.1 < weakComponentRank v.1 :=
  h.elim fun γ => (EntryWeakProofs.weakConstruction_rank_bounds S.P _ S.M A.Jw 0 _ S.stage
    S.construction i hMi hi).2 v u γ

/-- **One passage is identified**: the coupled passage family from a trace with the order-zero
value of a weak passage solution's trace has the order-zero value of that solution on the whole
window. -/
theorem weakStage_passage_identified (S : WeakRawSetting R) (hM2 : 2 ≤ S.M)
    (K : WeakRawClock S) (m : ℕ) {Uhi : ∀ i, WeakStageFamily S m i}
    {Whi : ∀ i, WeakStageLift S m i} (i : ℕ) (hMi : S.M < i) (hi : i ≤ S.M + A.Jw)
    (hp : WeakStagePassage S K m Uhi Whi i)
    {U : ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)}
    {Ub : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)}
    {Ubw : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)}
    {Ubk : ∀ v u (_ : (S.stage (i - 1)).fam.Γ v u), ℝ →
      TorusHk (R.Kw + S.Dm - 1) (ScalarH u.1.root)}
    (hpass : IsWeakPassageSolution S.P A.φ₀ A.hφ₀ R.nW R.Kw (S.stage i) (S.stage (i - 1))
      (K.tq i) (K.a + A.T₀) U Ub Ubw Ubk)
    (htrace : ∀ v, truncateTorusHk (Nat.zero_le _) (Uhi i v (K.tq i)) =
      truncateTorusHk (Nat.zero_le _) (U v (K.tq i))) :
    ∀ v, ∀ t ∈ Set.Icc (K.tq i) (K.a + A.T₀),
      truncateTorusHk (Nat.zero_le _) (Uhi (i - 1) v t) =
        truncateTorusHk (Nat.zero_le _) (Ub v t) := by
  obtain ⟨Ub₀, htr, hreg⟩ := hpass
  obtain ⟨hν, ρ, hρ, hd⟩ := weakStage_level_drift S hM2 i hMi hi (K.tq i) (K.a + A.T₀) 0
  have hab := K.tq_le i hMi hi
  have hD : 1 + A.Jw * A.Nw ≤ S.Dm := S.order_ge
  have hD' : 2 ≤ 1 + A.Jw * A.Nw := by have := Nat.mul_le_mul A.Jw_pos A.Nw_pos; omega
  have hP := weakStage_physCoeff_nonadmissible S m (i - 1) (by omega) (by omega)
  have htri := weakStage_rank_lt S (i - 1) (by omega) (by omega)
  have hS := fun v u γ s =>
    sysS_isoPairedKernel_zero S.P R.nW A.hφ₀ A.mass (S.stage (i - 1)) v u γ s
  have hf := weakStageTrace_truncate_zero S m i (Uhi i) (K.tq i) htr htrace
  -- The implicit arguments are named: inferring them from `hreg` and `hp` unifies the `ScalarH`
  -- fibres and exceeds the default budget.
  exact regSolution_identified (K := fun v => weakReductionReserve R m v.1)
    (A := weakStageCoeff S m (i - 1)) (f := Ub₀) (U := Ub) (W := Ubw) (Y := Ubk)
    (f' := weakStageTrace S m i (Uhi i) (K.tq i)) (u' := Uhi (i - 1)) (w' := Whi (i - 1))
    S.P (fun _ => isoPairedKernel 0 R.nW) (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀
    (S.stage (i - 1)) hd hab hρ hν hD hD' (fun _ _ _ _ _ => rfl) hP (fun v => weakComponentRank v.1)
    htri hS hreg hp hf

/-- The coupled family and a reduction agree at order zero at the level `j`, on the window
`[t₀, T]`. -/
def WeakStageAgreeZero (S : WeakRawSetting R) (K : WeakRawClock S) (m : ℕ)
    (Uhi : ∀ i, WeakStageFamily S m i)
    (Ur : (i : ℕ) → ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root))
    (t₀ : ℝ) (j : ℕ) : Prop :=
  ∀ v : CompIn (S.stage j).comps, ∀ t ∈ Set.Icc t₀ (K.a + A.T₀),
    truncateTorusHk (Nat.zero_le _) (Uhi j v t) = truncateTorusHk (Nat.zero_le _) (Ur j v t)

section Induction

variable (S : WeakRawSetting R) (K : WeakRawClock S) (m : ℕ) {θ : ℝ → Vec 2 → ℝ}
  {Uhi : ∀ i, WeakStageFamily S m i} {Whi : ∀ i, WeakStageLift S m i}
  {Ur : (i : ℕ) → ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)}
  {Urw : (i : ℕ) → ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)}
  {Urk : (i : ℕ) → ∀ v u (_ : (S.stage i).fam.Γ v u), ℝ →
    TorusHk (R.Kw + S.Dm - 1) (ScalarH u.1.root)}

/-- **One step of the downward induction** over the passages. -/
theorem weakStage_agreeZero_step (hM2 : 2 ≤ S.M)
    (hpass : ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i)
    (hred : IsWeakReduction S.P A.φ₀ A.hφ₀ R.nW S.M A.Jw R.Kw 0 K.a (K.a + A.T₀) θ S.stage K.tq
      Ur Urw Urk)
    (i : ℕ) (hMi : S.M < i) (hi : i ≤ S.M + A.Jw) {t₀ : ℝ} (ht₀ : t₀ ≤ K.tq i)
    (h : WeakStageAgreeZero S K m Uhi Ur t₀ i) :
    WeakStageAgreeZero S K m Uhi Ur (K.tq i) (i - 1) :=
  weakStage_passage_identified S hM2 K m i hMi hi (hpass i hMi hi)
    (hred.2.2.2 i hMi hi).2.2.2.2.2 (fun v => h v (K.tq i) ⟨ht₀, K.tq_le i hMi hi⟩)

/-- **Agreement at order zero on the root stage**, from the root time of the clock. -/
theorem weakStage_agreeZero_root
    (hroot : ∀ (hr : (⟨0, []⟩ : Comp) ∈ (S.stage (S.M + A.Jw)).comps),
      ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
        (Uhi (S.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
            (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
          AVenhance.unitCube] θ t)
    (hred : IsWeakReduction S.P A.φ₀ A.hφ₀ R.nW S.M A.Jw R.Kw 0 K.a (K.a + A.T₀) θ S.stage K.tq
      Ur Urw Urk) :
    WeakStageAgreeZero S K m Uhi Ur K.troot (S.M + A.Jw) := by
  intro v t ht
  obtain ⟨c, hc⟩ := v
  have hcomps : (S.stage (S.M + A.Jw)).comps = {⟨0, []⟩} := S.construction.2.1.2.1
  obtain rfl : c = ⟨0, []⟩ := Finset.mem_singleton.1 (hcomps ▸ hc)
  exact truncate_zero_eq_of_jet_ae _ _ ((hroot hc t ht).trans
    (hred.2.2.1 hc t ⟨K.troot_ge.trans ht.1, ht.2⟩).symm)

/-- **Agreement at order zero below the root**, by downward induction: at the level `i - 1` on
`[t_i, T]`, for every passage `i`. -/
theorem weakStage_agreeZero (hM2 : 2 ≤ S.M)
    (hroot : ∀ (hr : (⟨0, []⟩ : Comp) ∈ (S.stage (S.M + A.Jw)).comps),
      ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
        (Uhi (S.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
            (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
          AVenhance.unitCube] θ t)
    (hpass : ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i)
    (hred : IsWeakReduction S.P A.φ₀ A.hφ₀ R.nW S.M A.Jw R.Kw 0 K.a (K.a + A.T₀) θ S.stage K.tq
      Ur Urw Urk) :
    ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStageAgreeZero S K m Uhi Ur (K.tq i) (i - 1) := by
  have main : ∀ n, n < A.Jw → ∀ i, i = S.M + A.Jw - n →
      WeakStageAgreeZero S K m Uhi Ur (K.tq i) (i - 1) := by
    intro n
    induction n with
    | zero =>
      intro hn i hi
      subst hi
      exact weakStage_agreeZero_step S K m hM2 hpass hred _ (by omega) (by omega) K.troot_le
        (weakStage_agreeZero_root S K m hroot hred)
    | succ n ih =>
      intro hn i hi
      have hMi : S.M < i := by omega
      have hiJ : i ≤ S.M + A.Jw := by omega
      have h' : WeakStageAgreeZero S K m Uhi Ur (K.tq (i + 1)) i :=
        ih (by omega) (i + 1) (by omega)
      exact weakStage_agreeZero_step S K m hM2 hpass hred i hMi hiJ (K.tq_step i hMi hiJ) h'
  intro i hMi hi
  exact main (S.M + A.Jw - i) (by omega) i (by omega)

/-- **Consistency** (shared higher-order lemma): coupled families at the reduction reserves
raised by `m`, whose root component has the value `θ(t)` and which solve every passage, truncate
to every weak reduction of `θ` at the order `K_w`: the root on `[t_root, T]`, the level `i - 1` on
`[t_i, T]` for every passage `i`, and the gradient lifts at almost every time. -/
theorem weakStage_coupled_consistent (hM2 : 2 ≤ S.M)
    (hroot : ∀ (hr : (⟨0, []⟩ : Comp) ∈ (S.stage (S.M + A.Jw)).comps),
      ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
        (Uhi (S.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
            (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
          AVenhance.unitCube] θ t)
    (hpass : ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i)
    (hred : IsWeakReduction S.P A.φ₀ A.hφ₀ R.nW S.M A.Jw R.Kw 0 K.a (K.a + A.T₀) θ S.stage K.tq
      Ur Urw Urk) :
    (∀ v : CompIn (S.stage (S.M + A.Jw)).comps, ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (S.M + A.Jw) v t) =
        Ur (S.M + A.Jw) v t) ∧
    (∀ i, S.M < i → i ≤ S.M + A.Jw → ∀ v : CompIn (S.stage (i - 1)).comps,
      ∀ t ∈ Set.Icc (K.tq i) (K.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
          Ur (i - 1) v t) ∧
    ∀ i, S.M < i → i ≤ S.M + A.Jw → ∀ v : CompIn (S.stage (i - 1)).comps,
      ∀ᵐ t ∂(volume.restrict (Set.Icc (K.tq i) (K.a + A.T₀))),
        truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_kw_le R m v.1))
          (Whi (i - 1) v t) = Urw (i - 1) v t := by
  have hval : ∀ i, S.M < i → i ≤ S.M + A.Jw → ∀ v : CompIn (S.stage (i - 1)).comps,
      ∀ t ∈ Set.Icc (K.tq i) (K.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
          Ur (i - 1) v t :=
    fun i hMi hi v t ht => truncate_eq_of_truncate_zero_eq _ _ _
      (weakStage_agreeZero S K m hM2 hroot hpass hred i hMi hi v t ht)
  refine ⟨fun v t ht => truncate_eq_of_truncate_zero_eq _ _ _
    (weakStage_agreeZero_root S K m hroot hred v t ht), hval, fun i hMi hi v => ?_⟩
  have hp : WeakStagePassage S K m Uhi Whi i := hpass i hMi hi
  obtain ⟨_, _, hreg⟩ := (hred.2.2.2 i hMi hi).2.2.2.2.2
  have h₁ : ∀ᵐ t ∂(volume.restrict (Set.Icc (K.tq i) (K.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (Whi (i - 1) v t) = Uhi (i - 1) v t := hp.2.2.1 v
  have h₂ : ∀ᵐ t ∂(volume.restrict (Set.Icc (K.tq i) (K.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (Urw (i - 1) v t) = Ur (i - 1) v t := hreg.2.2.1 v
  exact lift_truncate_ae _ (hval i hMi hi v) h₁ h₂

end Induction

/-- **The higher order of the reduction over raw data** (shared higher-order lemma): for every
reduction of `θ` at `K_w` on the clock and every order offset `m`, coupled families at the
reduction reserves raised by `m`, with root value `θ(t)` from the root time on and every passage
solved, whose truncations to `K_w` are the reduction: the root on `[t_root, T]`, the level `i - 1`
on `[t_i, T]`, the gradient lifts at almost every time. -/
theorem weakStage_higher (S : WeakRawSetting R) (hM2 : 2 ≤ S.M) (hreg : S.CoeffRegular)
    (K : WeakRawClock S) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (S.D.Φ (S.M + A.Jw))) (S.D.κ S.M) K.a (K.a + A.T₀) f θ)
    {Ur : (i : ℕ) → ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)}
    {Urw : (i : ℕ) → ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)}
    {Urk : (i : ℕ) → ∀ v u (_ : (S.stage i).fam.Γ v u), ℝ →
      TorusHk (R.Kw + S.Dm - 1) (ScalarH u.1.root)}
    (hred : IsWeakReduction S.P A.φ₀ A.hφ₀ R.nW S.M A.Jw R.Kw 0 K.a (K.a + A.T₀) θ S.stage K.tq
      Ur Urw Urk) (m : ℕ) :
    ∃ (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i),
      (∀ (hr : (⟨0, []⟩ : Comp) ∈ (S.stage (S.M + A.Jw)).comps),
        ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
          (Uhi (S.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
              (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
            AVenhance.unitCube] θ t) ∧
      (∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i) ∧
      (∀ v : CompIn (S.stage (S.M + A.Jw)).comps, ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (S.M + A.Jw) v t) =
          Ur (S.M + A.Jw) v t) ∧
      (∀ i, S.M < i → i ≤ S.M + A.Jw → ∀ v : CompIn (S.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (K.tq i) (K.a + A.T₀),
          truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
            Ur (i - 1) v t) ∧
      ∀ i, S.M < i → i ≤ S.M + A.Jw → ∀ v : CompIn (S.stage (i - 1)).comps,
        ∀ᵐ t ∂(volume.restrict (Set.Icc (K.tq i) (K.a + A.T₀))),
          truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_kw_le R m v.1))
            (Whi (i - 1) v t) = Urw (i - 1) v t := by
  obtain ⟨Uhi, Whi, hroot, hpass⟩ :=
    weakStage_coupled_families S hM2 hreg K weak_scalar_smoothing f θ hθ m
  exact ⟨Uhi, Whi, hroot, hpass, weakStage_coupled_consistent S K m hM2 hroot hpass hred⟩

/-! ### The weak entry -/

variable {plan : WeakEntryGluePlan} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The higher order of the reduction** (shared higher-order lemma): for every reduction `r`
of `θ` and every order offset `m`, coupled families at the reduction reserves raised by `m`, with
root value `θ(t)` and every passage solved, whose truncations to `K_w` are `r` (values on each
window, gradient lifts at almost every time). -/
theorem weakReduction_higher (hcommon : WeakEntryCommonOK plan) {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (r : WeakEntryReduced s θ) (m : ℕ) :
    ∃ (Uhi : ∀ i, WeakReductionFamily g m i) (Whi : ∀ i, WeakReductionLift g m i),
      (∀ (hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps),
        ∀ t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀),
          (Uhi (x.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
              (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
            AVenhance.unitCube] θ t) ∧
      (∀ i, x.M < i → i ≤ x.M + A.Jw → WeakReductionPassage s m Uhi Whi i) ∧
      (∀ j, x.M ≤ j → j ≤ x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀),
          truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi j v t) = r.Ur j v t) ∧
      ∀ j, x.M ≤ j → j < x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ᵐ t ∂(volume.restrict (Set.Icc (s.tq (j + 1)) (x.a + A.T₀))),
          truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_kw_le R m v.1)) (Whi j v t) =
            r.Urw j v t := by
  obtain ⟨Uhi, Whi, hroot, hpass, hvr, hval, hlift⟩ :=
    weakStage_higher (weakEntryRawSetting g) (weakEntryData_M_ge_two hcommon x)
      (weakEntryRawSetting_coeffRegular hcommon g) (weakEntryRawClock s) f θ hθ r.reduction m
  refine ⟨Uhi, Whi, hroot, hpass, fun j hj hj' v t ht => ?_, fun j hj hj' v => ?_⟩
  · by_cases hjJ : j = x.M + A.Jw
    · subst hjJ
      exact hvr v t ht
    · exact hval (j + 1) (show x.M < j + 1 by omega) (show j + 1 ≤ x.M + A.Jw by omega) v t ht
  · exact hlift (j + 1) (show x.M < j + 1 by omega) (show j + 1 ≤ x.M + A.Jw by omega) v

/-- **The higher order of the reduction, in the form used downstream**: a weak reduction at the order
`K_w + m` for the same `θ`, clock and stages, whose truncation to `K_w` is `r` (from the families
at the offset `m + D_m - 2`). -/
theorem weakReduction_higher_reduction (hcommon : WeakEntryCommonOK plan)
    {x : WeakEntryData plan C} {g : WeakEntryStages x} (s : WeakEntrySchedule g)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (r : WeakEntryReduced s θ) (m : ℕ) :
    ∃ (Ur : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk (R.Kw + m) (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ →
        TorusHk (R.Kw + m + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (g.stage i).fam.Γ v u), ℝ →
        TorusHk (R.Kw + m + x.Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction x.P A.φ₀ A.hφ₀ R.nW x.M A.Jw (R.Kw + m) 0 x.a (x.a + A.T₀) θ g.stage
        s.tq Ur Urw Urk ∧
      (∀ j, x.M ≤ j → j ≤ x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀),
          truncateTorusHk (Nat.le_add_right R.Kw m) (Ur j v t) = r.Ur j v t) ∧
      ∀ j, x.M ≤ j → j < x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ᵐ t ∂(volume.restrict (Set.Icc (s.tq (j + 1)) (x.a + A.T₀))),
          truncateTorusHk (Nat.succ_le_succ (Nat.le_add_right R.Kw m)) (Urw j v t) =
            r.Urw j v t := by
  obtain ⟨Uhi, Whi, hroot, hpass, hval, hlift⟩ :=
    weakReduction_higher hcommon s f θ hθ r (m + x.Dm - 2)
  exact ⟨_, _, _, weakReduction_of_coupled s θ m hroot hpass, hval, hlift⟩

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **A passage instance over the raw data** (`WeakRawSetting`, `WeakRawClock`).

The results of the reduction that both the entry and the passages need are stated over the raw data.
This module reads them on a passage instance `c : WeakPassageInstance plan R` and a run
`r : WeakPassageRun c`.

* `weakPassageRawSetting c`, `weakPassageRawClock r`: the raw data and the clock. The root time of
  the clock is `t_{M+J_w}`: a run gives only `a ≤ t_{M+J_w+1}`, and the clock needs `a < t_root`.
* `weakPassage_coeffRegular`: the stage coefficients of every order, on a plan above the common
  plan's thresholds (`WeakPassageCommonOK`), from the carrier `(1, 400)` of the instance.
* On a run, the higher order of the reduction (`weakStage_higher` over the raw data): for every
  order offset `m` there are coupled families at the reduction reserves raised by `m`, with every
  passage solved, whose truncations to `K_w` are the families of the run (values on each window,
  gradient lifts at almost every time).

The degenerate cases are included:
- `m = 0`: the families are at the reserves `K_w + weakComparisonReserve`, still above `K_w`.
- `J_w = 1`: one passage; the root window `[t_{M+1}, a + T₀]` is the window of the level `M`. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The raw data of a passage instance. -/
@[reducible] def weakPassageRawSetting (c : WeakPassageInstance plan R) : WeakRawSetting R where
  D := c.D
  alpha := c.alpha
  q_eq := c.q_eq
  base_eq := c.base_eq
  profile_eq := c.profile_eq
  base128 := (plan.base_ge B).trans c.base_ge
  streams := c.streams
  M := c.M
  band := c.band
  terminal := c.terminal
  Dm := c.Dm
  order_ge := c.order_ge
  j₀ := c.j₀
  P := c.P
  stage := c.stage
  construction := c.construction

/-- The clock of a run of a passage instance; the root time is `t_{M+J_w}`. -/
@[reducible] def weakPassageRawClock {c : WeakPassageInstance plan R} (r : WeakPassageRun c) :
    WeakRawClock (weakPassageRawSetting c) where
  a := r.a
  tq := r.tq
  troot := r.tq (c.M + A.Jw)
  troot_gt :=
    have h := weak_quiet_window c r (c.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl
    lt_of_le_of_lt h.1 h.2.2.1
  troot_ge :=
    (weak_quiet_window c r (c.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl).2.2.1.le
  troot_le := le_rfl
  tq_le := fun i hi hit => (weak_quiet_window c r i hi hit).2.1
  tq_step := fun i hi hit => (weak_quiet_window c r i hi hit).2.2.1.le

/-- **The stage coefficients of a passage instance at every order**, on a plan above the common
plan's thresholds. -/
theorem weakPassage_coeffRegular (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) : (weakPassageRawSetting c).CoeffRegular :=
  fun i hMi hit v u γ n d a b =>
    weakData_physCoeff_allOrder R ((hcommon.1 B).trans c.base_ge)
      ((plan.base_ge B).trans c.base_ge) c.j₀ c.carrier c.M
      ((hcommon.2 R c.j₀).trans c.level_ge) c.D c.alpha c.q_eq c.base_eq c.profile_eq c.streams
      c.band c.terminal c.Dm c.order_ge c.P c.stage c.construction i hMi hit v u γ n d a b

/-- The terminal level of an instance above the common plan's thresholds is at least `2`. -/
theorem weakPassage_two_le_M (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) : 2 ≤ c.M := by
  have hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) c.j₀ ≤ c.M :=
    (hcommon.2 R c.j₀).trans c.level_ge
  have hj2 : c.j₀ + 2 ≤ c.M :=
    ((weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext).2
      (weakCoeffRequestOne R) c.j₀).trans hlev
  omega

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! The finite old-component restriction of the quiet trace bound, with variable Sobolev reserves.
The sum restriction is the existing terminal-family finite-sum lemma. -/

/-- Pure finite restriction: keep the old components, put zero on the new
ones, lower the radius and truncate from the maximal reserve. -/
def WeakEntryHighTraceRestrictionStatement (hr : ℕ → Type)
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] : Prop :=
  ∀ (S S' : Finset Comp) (K : Comp → ℕ) (P : ℕ), (∀ v, K v ≤ P) →
    ∀ (ρ ρ' : ℝ), 0 ≤ ρ → ρ ≤ ρ' → ∀ (π : Comp → ℝ), (∀ v, 0 ≤ π v) →
    ∀ (U : ∀ v : CompIn S, TorusHk (K v.1) (hr v.1.root))
      (V : ∀ v : CompIn S, TorusHk P (hr v.1.root)),
      (∀ v, truncateTorusHk (Nat.zero_le _) (U v) = truncateTorusHk (Nat.zero_le P) (V v)) →
      massNormSq ρ (fun v : CompIn S' => π v.1)
        (fun v => (if hv : v.1 ∈ S then U ⟨v.1, hv⟩ else
          (0 : TorusHk (K v.1) (hr v.1.root))).val) ≤
      massNormSq ρ' (fun v : CompIn S => π v.1) (fun v => (V v).val)

/-- Restriction to old components, truncation and radius lowering cost no
constant, independently of the number of components or the ambient cap. -/
theorem weak_entry_high_trace_restriction (hr : ℕ → Type)
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] :
    WeakEntryHighTraceRestrictionStatement hr := by
  intro S S' K P hK ρ ρ' hρ hρ' π hπ U V hUV
  let F : Comp → ℝ := fun v => if hv : v ∈ S then
    (π v)⁻¹ * factorialNormSq ρ' (V ⟨v, hv⟩).val else 0
  have hF (v : Comp) (hv : v ∈ S) : 0 ≤ F v := by
    simp only [F, hv, ↓reduceDIte]
    exact mul_nonneg (inv_nonneg.mpr (hπ v)) (factorialNormSq_nonneg _ _)
  have hterm (v : CompIn S') :
      (π v.1)⁻¹ * factorialNormSq ρ (if hv : v.1 ∈ S then U ⟨v.1, hv⟩ else
        (0 : TorusHk (K v.1) (hr v.1.root))).val ≤
        if v.1 ∈ S then F v.1 else 0 := by
    by_cases hv : v.1 ∈ S
    · simp only [hv, ↓reduceDIte, ↓reduceIte, F]
      have he : truncateTorusHk (hK v.1) (V ⟨v.1, hv⟩) = U ⟨v.1, hv⟩ :=
        truncate_eq_of_truncate_zero_eq (hK v.1) _ _ (hUV _).symm
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hπ v.1))
      rw [← he]
      exact (CycleComparison.Error.factorialNormSq_truncateTorusHk_le (hK v.1) ρ _).trans
        (CycleJointProofs.factorialNormSq_mono_radius hρ hρ' _)
    · simp only [hv, ↓reduceDIte, ↓reduceIte, ZeroMemClass.coe_zero]
      simp [factorialNormSq, derivativeNormSq]
  unfold massNormSq
  apply (Finset.sum_le_sum fun v _ => hterm v).trans
  calc
    _ ≤ ∑ v : CompIn S, F v.1 := EntryTerminal.Ingredients.sum_compIn_ite_le F hF
    _ = _ := Finset.sum_congr rfl fun v _ => by simp only [F, v.2, ↓reduceDIte]

end AVRegularity.Providers.WeakGen.Reduction
end
