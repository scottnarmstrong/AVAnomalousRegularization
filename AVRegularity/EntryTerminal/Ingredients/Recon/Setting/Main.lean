-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
public import AVRegularity.CycleComparison.LiftSetting.Metric
public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.CycleReference.ChartTestTransport

section
section
/-! # Transfer of a lift setting between operator data that agree on a window

If `Q₁` is a lift setting on `[s₀, s₁]` and `Q₂` has the same contrast, metric and drift and the same
edges up to coefficients that agree on a subwindow `[t₀, t₁] ⊆ [s₀, s₁]` (and the coefficients of
`Q₂` are measurable in time), then `Q₂` is a lift setting on `[t₀, t₁]` with the same parameters.

Special cases:
- `t₀ = s₀`, `t₁ = s₁` and `Q₂ = Q₁`: the identity.
- `t₀ = t₁`: a single time. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Setting

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The edges agree elementwise: same maps, coefficients equal on `[t₀, t₁]`. -/
def EdgeAgree (E₁ E₂ : ConstituentEdges D h) (t₀ t₁ : ℝ) : Prop :=
  ∀ v u (d : Finset.Icc 2 D), List.Forall₂ (fun (γ₁ γ₂ : Constituent d.1 (h u) (h v)) =>
    γ₁.map = γ₂.map ∧ ∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t) (E₁ v u d) (E₂ v u d)

theorem edgeAgree_mem {E₁ E₂ : ConstituentEdges D h} {t₀ t₁ : ℝ} (hE : EdgeAgree E₁ E₂ t₀ t₁)
    {v u} {d : Finset.Icc 2 D} {γ₂ : Constituent d.1 (h u) (h v)} (hγ : γ₂ ∈ E₂ v u d) :
    ∃ γ₁ ∈ E₁ v u d, γ₁.map = γ₂.map ∧ ∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t := by
  have key : ∀ (l₁ l₂ : List (Constituent d.1 (h u) (h v))), List.Forall₂
      (fun (γ₁ γ₂ : Constituent d.1 (h u) (h v)) =>
      γ₁.map = γ₂.map ∧ ∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t) l₁ l₂ →
      ∀ γ₂ ∈ l₂, ∃ γ₁ ∈ l₁, γ₁.map = γ₂.map ∧
        ∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t := by
    intro l₁ l₂ hl
    induction hl with
    | nil => intro γ hγ; simp at hγ
    | cons hxy _ ih =>
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ'
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨γ₁, h1, h2⟩ := ih γ hγ'
        exact ⟨γ₁, List.mem_cons_of_mem _ h1, h2⟩
  exact key _ _ (hE v u d) γ₂ hγ

theorem edgeAgree_nil {E₁ E₂ : ConstituentEdges D h} {t₀ t₁ : ℝ} (hE : EdgeAgree E₁ E₂ t₀ t₁)
    {v u} {d : Finset.Icc 2 D} (h1 : E₁ v u d = []) : E₂ v u d = [] := by
  have := hE v u d
  rw [h1] at this
  exact List.forall₂_nil_left_iff.mp this

theorem edgeAgree_sum {E₁ E₂ : ConstituentEdges D h} {t₀ t₁ : ℝ} (hE : EdgeAgree E₁ E₂ t₀ t₁)
    (v u) (d : Finset.Icc 2 D) (f : Constituent d.1 (h u) (h v) → ℝ≥0∞)
    (hf : ∀ (γ₁ γ₂ : Constituent d.1 (h u) (h v)), γ₁.map = γ₂.map →
      (∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t) → f γ₁ = f γ₂) :
    ((E₁ v u d).map f).sum = ((E₂ v u d).map f).sum := by
  have key : ∀ (l₁ l₂ : List (Constituent d.1 (h u) (h v))), List.Forall₂
      (fun (γ₁ γ₂ : Constituent d.1 (h u) (h v)) =>
      γ₁.map = γ₂.map ∧ ∀ α, ∀ t ∈ Set.Icc t₀ t₁, γ₁.coeff α t = γ₂.coeff α t) l₁ l₂ →
      (l₁.map f).sum = (l₂.map f).sum := by
    intro l₁ l₂ hl
    induction hl with
    | nil => rfl
    | cons hxy _ ih =>
      simp only [List.map_cons, List.sum_cons, ih, hf _ _ hxy.1 hxy.2]
  exact key _ _ (hE v u d)

theorem jetSup_congr_on {I : Set ℝ} {r q : ℕ} {f g : ℝ → Vec 2 → Vec 2 → Vec 2}
    (h : ∀ t ∈ I, f t = g t) : jetSup I r q f = jetSup I r q g := by
  unfold jetSup
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  rw [h t ht]

/-- The jet sum of the edges over a subwindow, for edges that agree there, is bounded by the sum
over the larger window. -/
theorem edge_jetSum_le {E₁ E₂ : ConstituentEdges D h} {s₀ s₁ t₀ t₁ : ℝ}
    (hE : EdgeAgree E₁ E₂ t₀ t₁) (hs₀ : s₀ ≤ t₀) (hs₁ : t₁ ≤ s₁) (v u : ι) (r q : ℕ) :
    ∑ d : Finset.Icc 2 D, ((E₂ v u d).map fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ.coeff α)).sum ≤
      ∑ d : Finset.Icc 2 D, ((E₁ v u d).map fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, jetSup (Set.Icc s₀ s₁) r q (γ.coeff α)).sum := by
  refine Finset.sum_le_sum fun d _ => ?_
  have e : ((E₁ v u d).map fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ.coeff α)).sum =
      ((E₂ v u d).map fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ.coeff α)).sum := by
    refine edgeAgree_sum hE v u d (fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ.coeff α)) fun γ₁ γ₂ hm hc => ?_
    have e2 : ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ₁.coeff α) =
        ∑ α, jetSup (Set.Icc t₀ t₁) r q (γ₂.coeff α) :=
      Finset.sum_congr rfl fun α _ => jetSup_congr_on fun t htt => hc α t htt
    rw [hm, e2]
  rw [← e]
  refine List.sum_le_sum fun γ _ => ?_
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun α _ => ?_)
  exact biSup_mono fun t htt => ⟨hs₀.trans htt.1, htt.2.trans hs₁⟩

/-- **Transfer of a lift setting to a subwindow and to operator data with the same edges there.** -/
theorem isLiftSetting_transfer [Fintype ι] {Q₁ Q₂ : LiftOperatorData ι h D} {π : ι → ℝ}
    {s₀ s₁ t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q₁ π s₀ s₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hs₀ : s₀ ≤ t₀) (ht : t₀ ≤ t₁) (hs₁ : t₁ ≤ s₁)
    (hη : Q₂.η = Q₁.η) (hG : Q₂.G = Q₁.G) (hv : Q₂.v = Q₁.v)
    (hE : EdgeAgree Q₁.edge Q₂.edge t₀ t₁)
    (hmeas : ∀ v u d, ∀ γ ∈ Q₂.edge v u d, ∀ α X z, Measurable fun t => γ.coeff α t X z) :
    IsLiftSetting Q₂ π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ := by
  have hsub : ∀ t ∈ Set.Icc t₀ t₁, t ∈ Set.Icc s₀ s₁ := fun t htt => ⟨hs₀.trans htt.1, htt.2.trans hs₁⟩
  refine
    { window := ht
      e_pos := hset.e_pos
      ν_pos := hset.ν_pos
      B_pos := hset.B_pos
      ρ_pos := hset.ρ_pos
      E_pos := hset.E_pos
      ℓ_eq := hset.ℓ_eq
      η_eq := hη.trans hset.η_eq
      η_le := hη ▸ hset.η_le
      dstar_eq := hset.dstar_eq
      εc_eq := hset.εc_eq
      εc_le := hset.εc_le
      lam_eq := hset.lam_eq
      lam_le := hset.lam_le
      N_ge := hset.N_ge
      D_ge := hset.D_ge
      qs_eq := hset.qs_eq
      qf_eq := hset.qf_eq
      mass_pos := hset.mass_pos
      G_symm := hG ▸ hset.G_symm
      G_meas := hG ▸ hset.G_meas
      G_smooth := fun t htt i j => hG ▸ hset.G_smooth t (hsub t htt) i j
      G_ellip := fun t htt => hG ▸ hset.G_ellip t (hsub t htt)
      G_jets := fun r hr => ?_
      v_shear := hv ▸ hset.v_shear
      V_smooth := fun t htt => hset.V_smooth t (hsub t htt)
      V_per := fun t htt => hset.V_per t (hsub t htt)
      V_mean := fun t htt => hset.V_mean t (hsub t htt)
      v_meas := hv ▸ hset.v_meas
      w_jets := fun q hq => ?_
      depth := ?_
      transverse := ?_
      coeff_meas := hmeas
      coeff_smooth := ?_
      envelope := ?_ }
  · rw [hG]
    exact le_trans (biSup_mono fun t htt => hsub t htt) (hset.G_jets r hr)
  · rw [hv, hη]
    exact le_trans (biSup_mono fun t htt => hsub t htt) (hset.w_jets q hq)
  · intro p
    obtain ⟨i, hi⟩ := hset.depth p
    exact ⟨i, fun d => edgeAgree_nil hE (hi d)⟩
  · intro v u d γ hγ α
    obtain ⟨γ₁, h1, -, h3⟩ := edgeAgree_mem hE hγ
    intro t htt X z s
    rw [← h3 α t htt]
    exact hset.transverse v u d γ₁ h1 α t (hsub t htt) X z s
  · intro v u d γ hγ α t htt
    obtain ⟨γ₁, h1, -, h3⟩ := edgeAgree_mem hE hγ
    rw [← h3 α t htt]
    exact hset.coeff_smooth v u d γ₁ h1 α t (hsub t htt)
  · have hen := hset.envelope
    refine ⟨hen.nonneg, hen.row_sum, hen.col_sum, fun v u r hr q hq => ?_⟩
    exact le_trans (mul_le_mul' le_rfl (edge_jetSum_le hE hs₀ hs₁ v u r q)) (hen.jets v u r hr q hq)

/-- Rewriting the real parameters of a lift setting. -/
theorem isLiftSetting_congr_params [Fintype ι] {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam e' ν' B' ρ' E' ℓ' dstar' εc' lam' : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ}
    {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (he : e = e') (hν : ν = ν') (hB : B = B') (hρ : ρ = ρ') (hE : E = E') (hℓ : ℓ = ℓ')
    (hd : dstar = dstar') (hc : εc = εc') (hl : lam = lam') :
    IsLiftSetting Q π t₀ t₁ e' ν' B' ρ' E' ℓ' dstar' εc' lam' par V H N K k L qs qf CG Cw Cj b Θ := by
  subst he hν hB hρ hE hℓ hd hc hl
  exact hset

/-- A lift setting stays one with larger jet constants and a larger price bound. -/
theorem isLiftSetting_mono_const [Fintype ι] {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj Cj' : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ Θ' : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hC : ∀ r, r ≤ qs → ∀ q, q ≤ qf → Cj r q ≤ Cj' r q) (hΘ : Θ ≤ Θ') :
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj' b Θ' := by
  have hlam : 0 ≤ lam := by
    rw [hset.lam_eq]; exact (div_pos hset.ρ_pos hset.E_pos).le
  have hen := hset.envelope
  exact { hset with
    envelope := ⟨hen.nonneg, fun v => (hen.row_sum v).trans hΘ,
      fun u => (hen.col_sum u).trans hΘ, fun v u r hr q hq =>
        (hen.jets v u r hr q hq).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC r hr q hq)
            (pow_nonneg hlam r)) (hen.nonneg v u)))⟩ }

end AVRegularity.EntryTerminal.Ingredients.Recon.Setting
end
end

section
/-! # The edges of the native lift data and of the actual family agree on the output window

The native lift data of a slot (the fibre of the stage's family at the actual context, lifted,
extended by the clamp to the native window and restricted to the order `D`) and the lift data of the
actual family (the fibre of `G.actualFamily`, lifted) have the same edges on every time whose physical
time lies in the output window of the piece. This gives `EdgeAgree` on a window inside the native
window whose physical image lies in the output window.

Special cases:
- A stage without edges: both edge families are empty.
- The window is a single time: the clamp is the identity there. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev MeasureTheory

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Setting

/-- Elementwise agreement of two `filterMap` lists under a pointwise relation. -/
theorem forall₂_filterMap_map {α β γ : Type*} (R : γ → γ → Prop) (L : List α) (g₁ g₂ : α → Option β)
    (φ₁ φ₂ : β → γ) (hsome : ∀ x, (g₁ x).isSome = (g₂ x).isSome)
    (hR : ∀ x y₁ y₂, g₁ x = some y₁ → g₂ x = some y₂ → R (φ₁ y₁) (φ₂ y₂)) :
    List.Forall₂ R ((L.filterMap g₁).map φ₁) ((L.filterMap g₂).map φ₂) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    have hx := hsome x
    rcases e1 : g₁ x with _ | y₁ <;> rcases e2 : g₂ x with _ | y₂
    · simpa only [List.filterMap_cons, e1, e2] using ih
    · simp [e1, e2] at hx
    · simp [e1, e2] at hx
    · simp only [List.filterMap_cons, e1, e2, List.map_cons]
      exact List.Forall₂.cons (hR x y₁ y₂ e1 e2) ih

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The edges of the native lift data and of the actual family agree on the window.** -/
theorem edgeAgree_native_actual (G : GenStage D hr Dm b j₀) (p : OddSlot) (c0 lam a a' t₀ t₁ : ℝ)
    (hw : ∀ t ∈ Set.Icc t₀ t₁, a ≤ t ∧ t ≤ a' ∧ c0 * t ∈ (G.fam.piece p).output) :
    EdgeAgree
      (EntryWeakProofs.restrictConstituentEdges Dm le_rfl
        (Construction.Preservation.FullLift.windowEdges a a'
          (liftEdges c0 lam (G.fam.fiber p (G.actual p)))))
      (liftEdges c0 lam (G.actualFamily.fiber p ())) t₀ t₁ := by
  intro v u d
  simp only [EntryWeakProofs.restrictConstituentEdges, Construction.Preservation.FullLift.windowEdges,
    liftEdges, ChartedFamily.fiber, List.map_map]
  refine forall₂_filterMap_map _ Finset.univ.toList _ _ _ _ ?_ ?_
  · intro x
    by_cases hd : (d : ℕ) ≤ (G.fam.identity v u x).maxOrder
    · simp [GenStage.actualFamily, hd]
    · simp [GenStage.actualFamily, hd]
  · intro x y₁ y₂ e1 e2
    by_cases hd : (d : ℕ) ≤ (G.fam.identity v u x).maxOrder
    · simp only [hd, ↓reduceDIte, Option.some.injEq] at e1
      simp only [GenStage.actualFamily, hd, ↓reduceDIte, Option.some.injEq] at e2
      subst e1 e2
      refine ⟨rfl, fun α t ht => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hw t ht
      funext X z
      simp only [Function.comp, h3, ↓reduceIte,
        max_eq_right h1, min_eq_right h2]
    · simp [hd] at e1

/-- **The coefficients of the lifted fibre of the actual family are measurable in time.** -/
theorem actual_liftEdges_coeff_measurable (G : GenStage D hr Dm b j₀)
    (hm : G.actualFamily.IsTimeMeasurable) (p : OddSlot) (c0 lam : ℝ) :
    ∀ v u d, ∀ γ ∈ liftEdges c0 lam (G.actualFamily.fiber p ()) v u d, ∀ α X z,
      Measurable fun t => γ.coeff α t X z := by
  intro v u d γ hγ α X z
  simp only [liftEdges, ChartedFamily.fiber, List.mem_map, List.mem_filterMap] at hγ
  obtain ⟨γ', ⟨x, -, hx⟩, rfl⟩ := hγ
  by_cases hd : (d : ℕ) ≤ (G.actualFamily.identity v u x).maxOrder
  · simp only [hd, ↓reduceDIte, Option.some.injEq] at hx
    subst hx
    exact (hm p () v u x d.1 α (lam • X) z).comp (measurable_const.mul measurable_id)
  · simp [hd] at hx

end AVRegularity.EntryTerminal.Ingredients.Recon.Setting
end
end

section
/-! # The assembly of `termReconSetting`

The lift-setting step (`TermReconSettingStatement`) is the lift settings of the observed pulses together with the
grading of the lift coefficients `c.CcT k` on the clipped windows. The grading is a statement about
the sequence `c.CcT k`, so it needs the conclusion `ReconSeqAt` of the lift-sequence step (the sequence is a lift sequence of
the setting on the clipped window). This module states the core of the step with `ReconSeqAt` as a premise
(`TermReconSettingCoreStatement`) and proves `termReconSetting_of`: the step from the core, the lift-sequence step
(`TermReconSeqStatement`), the times step (`TermReconTimesStatement`, proved) and the floors on the
lift orders (proved here).

Special cases:
- `sXT, sZT` above the floors: the premises of `ReconSeqStep` hold, so `ReconSeqAt` follows from the lift-sequence step.
- A weak stage without edges: the core has nothing to grade. -/

@[expose] public section

open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The core of the lift-setting step**: with the lift sequences of the observed pulses as a premise. -/
def TermReconSettingCoreStatement : Prop :=
  ReconPrefixU (κ := {k : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℝ // 0 ≤ k.2.2.2.1 ∧ 0 ≤ k.2.2.2.2})
    fun c x _ ℓ k =>
      ReconSeqAt c ℓ → ReconSettingAt c x ℓ k.1.1 k.1.2.1 k.1.2.2.1 k.1.2.2.2.1 k.1.2.2.2.2

/-- The floors of the lift orders (the premises of `ReconSeqStep`). -/
def TermReconFloorsStatement : Prop :=
  ReconPrefixU (κ := Unit) fun {_} {A} {_} {sXT} {sZT} {_ _} {_} {_} {_} {_} {_ _ _ _ _ _} {_}
    {_ _ _ _ _} {_} {_} {_} _ _ _ ℓ _ =>
      rKlift A ℓ + A.Dt + 2 ≤ sXT ∧ max (rLlift A ℓ + 1) (rLlift A ℓ + 2) ≤ sZT

/-- The floors, by choosing the lift floors. -/
theorem termReconFloors : TermReconFloorsStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV ℓ => ?_⟩
  refine ⟨0, fun kc _ => ⟨rKlift A ℓ + A.Dt + 2, max (rLlift A ℓ + 1) (rLlift A ℓ + 2), 0,
    fun sXT sZT hX hZ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker hcP
  exact ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨0, fun M _ c x => ⟨hX, hZ⟩⟩⟩

/-- **The lift-setting step from its core and the lift-sequence step.** -/
theorem termReconSetting_of (hcore : TermReconSettingCoreStatement)
    (hseq : TermReconSeqStatement) : TermReconSettingStatement := by
  have h := (((hseq.and termReconTimes).and termReconFloors).and hcore)
  refine ReconPrefixU.mono (fun k => k.2) ?_ h
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x
    kc ℓ k hk
  obtain ⟨⟨⟨hs, ht⟩, hf⟩, hc⟩ := hk
  exact hc (hs hf.1 hf.2 ht.1)

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! # The native lift setting of an odd slot at the orders of the window

`terminal_level_lift` at the orders `(K, k, L) = (K_lift, L_lift, L_lift)` of the window (not the
floors of `QuietEntrance`), with the source envelope of `stage_native_lift_source_exists_envelope` and
the scale bounds of the terminal band. This is the proof of `qe_liftSetting` with the orders of the window.

Special cases:
- `ℓ = 0`: the orders of the window of the terminal residual.
- A weak stage without edges: the source envelope is the zero matrix. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.QuietEntrance

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Setting

/-- **The native lift setting of the odd slot `k`** at the terminal slow length `cr · liftLength`:
the setting of the restricted, window-clamped native lift data, at the orders `(K, kk, L)`. -/
def NativeSlotSetting {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} (D : OCData) (M : ℕ)
    (Gw : GenStage D ScalarH Dt bw j₀) (law : BirthLaw) (cr Θmax : ℝ) (N H K kk L : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (k : ℤ) (hk : Odd k) : Prop :=
  ∃ Θ : ℝ, Θ ≤ Θmax ∧
    IsLiftSetting
      (restrictLiftData Dt le_rfl
        {familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
            (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)) with
          edge := Construction.Preservation.FullLift.windowEdges
            (D.slotStart M k / D.cellScaleSq M)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
            (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
              (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge})
      (Gw.mass law) (D.slotStart M k / D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
      (D.eps M) (D.kap M) (D.kap (M - 1)) (cr * liftLength D M) (D.eps (M - 1))
      (D.eps M / Real.sqrt (D.kap M))
      (ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)))
      (ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M))
      ((cr * liftLength D M) / D.eps (M - 1)) (pulseParallel k)
      (pulseShearProfile D.α D.q D.Λ M D.ζ (D.kap M) k)
      H N K kk L (K + 4 * (H + 1) * (N + Dt) ^ 2)
      (max kk (L + 2) + H * Dt + 2 * N + 2 * Dt) CG Cw Cj (recordMajorant (Gw.mass law) Gw.fam) Θ

/-- **The native settings of the odd slots at the orders of the window.** The constants `C_G, C_w`
and the jet constants `C_j` precede the data. -/
theorem native_setting (X : TermConstruction) : ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
    ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid → ∀ ℓ : ℕ,
    ∃ (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ), (∀ r q, 0 ≤ Cj r q) ∧
    ∀ (nW : ℕ+) (cr cK CL Cχ : ℝ) (kW : InvConsts), 0 < cr → cr ≤ 1 → 0 < cK → kW.c₀ = cK →
      ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ D : OCData, IsTermData X A.Λ M D →
      ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
        IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
          Gw aM → kW.G0 ≤ kW.Hprod + 1 →
        ∀ (k : ℤ) (hk : Odd k), NativeSlotSetting D M Gw lawW cr (Cχ * D.eps M ^ A.χw) A.NT A.dW
          (rKlift A ℓ) (rLlift A ℓ) (rLlift A ℓ) CG Cw Cj k hk := by
  obtain ⟨Λa, hΛa, hsc⟩ := band_enhanced_lift_scale_bounds X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λa 128, le_max_right _ _, fun A hΛ hV ℓ => ?_⟩
  have hΛA : Λa ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hN : 1 ≤ A.NT := qe_one_le_NT A hV
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  have hbw : 0 < A.bw := hV.2.2.1.1
  obtain ⟨CG, Cw, m₀, hCG, hCw, hm₀, hmain⟩ := Construction.TerminalLift.terminal_level_lift
    X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq A.Λ hΛ128 X.ζ X.hζ A.dW A.NT (rKlift A ℓ)
    (rLlift A ℓ) (rLlift A ℓ) A.Dt hN hDt
  obtain ⟨B, hB, hsrc⟩ := stage_native_lift_source_exists_envelope A.bw hbw
    (rKlift A ℓ + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2)
    (max (rLlift A ℓ) (rLlift A ℓ + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt)
  refine ⟨CG, Cw, fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q),
    fun r q => mul_nonneg (Nat.cast_nonneg _) (hB _), ?_⟩
  intro nW cr cK CL Cχ kW hcr hcr1 hcK hkc j₀
  obtain ⟨m₁, hm₁, hscale⟩ := hsc A.Λ hΛA cr hcr
  obtain ⟨M₂, hM₂, hratio⟩ := qe_eps_ratio (q := X.q) (Λ := A.Λ) X.hq.1 hΛ128 CL
  refine ⟨max (max m₀ m₁) (max j₀ M₂), fun M hM D hD a lawW PW Gw aM hW hG0 k hk => ?_⟩
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := hD
  obtain ⟨-, -, hlev, hdepth, hroot, -, hid, -, -, hinv⟩ := hW
  have hm₀M : m₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hm₁M : m₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hjM : j₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hM₂M : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ128
  have hqD : 1 < D.q := hDq ▸ X.hq.1
  have hbandD : IsOCBandChain X.α X.q A.Λ X.ζ D.term D.κ := hterm ▸ hband
  have hscl := hscale D.term D.κ hbandD M hm₁M (le_of_eq hterm.symm)
  have hprev : M - 1 ≤ D.term := le_trans (Nat.sub_le M 1) (le_of_eq hterm.symm)
  have key : 0 < cr * liftLength D M ∧
      ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M) ≤ 1 ∧
      (cr * liftLength D M) / D.eps (M - 1) ≤ 1 := by
    simpa only [liftLength, OCData.kap, Nat.min_eq_left (le_of_eq hterm.symm),
      Nat.min_eq_left hprev, OCData.eps, hDα, hDq, hDΛ, hDζ] using hscl.2
  rw [← hlev] at key
  obtain ⟨hρ, hcell, hlam⟩ := key
  have hres : ∀ v : CompIn Gw.comps, 0 ≤ compReserve kW v.1 :=
    fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).1
  have hres2 : ∀ v : CompIn Gw.comps, compReserve kW v.1 ≤ 2 :=
    fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).2
  have hlen : ∀ v u γ, 1 ≤ (Gw.fam.identity v u γ).record.birthExcess →
      (Gw.fam.identity v u γ).record.length ≤ D.eps Gw.level := by
    intro v u γ _
    have hE : D.eps Gw.level = D.eps M := congrArg D.eps hlev
    rw [hE]
    have h1 := (hid v u γ).2.2.1
    have h2 := hratio M hM₂M
    have h3 : D.eps (M + 1) = ocEpsilon X.q A.Λ (M + 1) := by
      simp only [OCData.eps, hDq, hDΛ]
    have h4 : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
    rw [h3] at h1
    rw [h4]
    exact h1.trans h2
  have hinv0 := hinv
  obtain ⟨hnat, -, -, -, hpar, hcert, -, -⟩ := hinv
  have hπ : ∀ v : CompIn Gw.comps, 0 < Gw.mass lawW v :=
    fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD lawW v.1
  have hεpos : 0 ≤ D.eps (Gw.level - 1) :=
    le_of_lt (Construction.Stream.ocEpsilon_pos (q := D.q) (Λ := D.Λ) (by omega))
  have hsrc' := hsrc ScalarH D A.Dt j₀ Gw lawW PW _ _ A.φ₀ A.hφ₀ (M + A.Jw) kW aM (a + A.T₀) _ _
    hinv0 (by omega) (by omega) (Construction.Stream.ocEpsilon_pos (by omega)) hqD hΛD
    (hDζ ▸ X.hζ) (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) hres hres2 hlen ⟨k, hk⟩
    ((cr * liftLength D Gw.level) / D.eps (Gw.level - 1)) (div_nonneg hρ.le hεpos)
    (fun _ => 1) (Or.inl rfl)
  simp only [one_pow, div_one] at hsrc'
  have hz : ∀ v u (d : Finset.Icc 2 A.Dt), A.Dt < d.1 →
      (familyLiftData D Gw.level k (nativeChain Gw.level k) (cr * liftLength D Gw.level)
        (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hset := hmain ScalarH D hDα hDq hDΛ hDζ hseq
    (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) A.Dt j₀ (M + A.Jw) A.bw Gw kW hbw hcert hpar hnat
    (by omega) (by omega) (by omega) hdepth hres hres2 ⟨k, hk⟩ (cr * liftLength D Gw.level) hρ
    hcell hlam (Gw.mass lawW) hπ le_rfl
    (fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q))
    (recordMajorant (Gw.mass lawW) Gw.fam) (Cχ * D.eps M ^ A.χw) hz hsrc'
  obtain ⟨hsetting, -, -, -⟩ := hset
  rw [← hlev]
  exact ⟨Cχ * D.eps M ^ A.χw, by rw [hlev], hsetting⟩

end AVRegularity.EntryTerminal.Ingredients.Recon.Setting
end
end

section
/-! # The lift setting of the window at a context

From the native setting of the slot (`NativeSlotSetting`) to `IsLiftSetting (rLiftData c k)` on the
clipped window: the data agree (contrast, metric, drift at all times; edges on the output window),
the clipped window lies in the native window, and the constants are raised to `C_a`, `S_b`.

Special cases:
- `t_p` before the slot start and the deadline after the slot end: the clipped window is the native one.
- `S_b = Θ`: the price bound is unchanged. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryWeakProofs
open AVRegularity.EntryTerminal.Ingredients.Recon.Seq

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Setting

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- **The lift setting of the observed pulse `k` on the clipped window.** -/
theorem setting_of_native (hone : cr = 1) (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (ℓ : ℕ)
    {CG CwL : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {Ca Sb : ℝ}
    (hCa : ∀ r, r ≤ rKlift A ℓ + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2 → ∀ q,
      q ≤ max (rLlift A ℓ) (rLlift A ℓ + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt → Cj r q ≤ Ca) (hSb : Cχ * c.D.eps M ^ A.χw ≤ Sb)
    {k : ℤ} (hkobs : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (hnat : NativeSlotSetting c.D M c.Gw c.lawW cr (Cχ * c.D.eps M ^ A.χw) A.NT A.dW
      (rKlift A ℓ) (rLlift A ℓ) (rLlift A ℓ) CG CwL Cj k
      (CycleComparison.LiftSetting.obsPulse_odd hkobs)) :
    IsLiftSetting (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
      (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c) (ocEpsilon c.D.q c.D.Λ (M - 1))
      (ocEll c.D.q c.D.Λ M (c.D.κ M)) (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (pulseParallel k)
      (pulseShearProfile c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.κ M) k) A.dW A.NT (rKlift A ℓ)
      (rLlift A ℓ) (rLlift A ℓ) (rKlift A ℓ + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2)
      (max (rLlift A ℓ) (rLlift A ℓ + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt) CG CwL
      (fun _ _ => Ca) (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) Sb := by
  have hk : Odd k := CycleComparison.LiftSetting.obsPulse_odd hkobs
  obtain ⟨Θ, hΘ, hset⟩ := hnat
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hkap1 : c.D.kap (M - 1) = c.D.κ (M - 1) := by
    unfold OCData.kap; rw [hterm, min_eq_left (Nat.sub_le M 1)]
  have hρ : cr * liftLength c.D M = rRho c :=
    (congrArg (· * liftLength c.D M) hone).trans (one_mul _)
  have hc : ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 = c.D.cellScaleSq M := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  have hcpos : 0 < c.D.cellScaleSq M := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  obtain ⟨-, -, hlev, -, -, -, -, -, -, hinv⟩ := c.weak
  obtain ⟨hnatS, -, -, -, -, hcert, -, -⟩ := hinv
  have hout : ∀ p, (c.Gw.fam.piece p).output = ocPulseWindow c.D.α c.D.q c.D.Λ M p.1 :=
    fun p => seq_output_eq c p
  have hmeasF : c.Gw.actualFamily.IsTimeMeasurable :=
    c.Gw.isTimeMeasurable_actualFamily_of_certified hcert fun p => by rw [hout p, hlev]
  have e2 : (rLiftData c k).edge = liftEdges (c.D.cellScaleSq M)
      (cr * liftLength c.D M / c.D.eps (M - 1)) (c.Gw.actualFamily.fiber ⟨k, hk⟩ ()) := by
    show liftEdges (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1))
      (c.Gw.actualFamily.fiber (oddSlotOf k) ()) = _
    rw [oddSlotOf_of_odd hk, hc, hρ]
    rfl
  have hη := (seq_agree c hone hΛ hM hk).1
  have hG : (rLiftData c k).G = (seqQ c k hk).G := by
    funext t X' i j
    show _ = (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M) _).G t X' i j
    rw [EntryWeakProofs.native_familyLiftData_metric c.D M hM k _ _ t X', hρ]
    show ocMaterialMetric c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 * t)
      (rRho c • X') i j = _
    unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
    rw [hc, ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ'']
  have hv : (rLiftData c k).v = (seqQ c k hk).v := by
    funext t z
    show _ = ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.kap M) k t z
    rw [hkap]
    rfl
  have hs₀ : c.D.slotStart M k / c.D.cellScaleSq M ≤ rSeqStart c k := by
    show _ ≤ max _ _ / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2
    rw [hc]
    exact div_le_div_of_nonneg_right (le_max_left _ _) hcpos.le
  have hs₁ : rSeqEnd c k ≤ (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M := by
    show min _ _ / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 ≤ _
    rw [hc]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hcpos.le
  have ht : rSeqStart c k ≤ rSeqEnd c k := CycleComparison.LiftSetting.window (c.D.κ M) hkobs
  have hw : ∀ t ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k),
      c.D.slotStart M k / c.D.cellScaleSq M ≤ t ∧
        t ≤ (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M ∧
        c.D.cellScaleSq M * t ∈ (c.Gw.fam.piece ⟨k, hk⟩).output := by
    intro t htt
    refine ⟨hs₀.trans htt.1, htt.2.trans hs₁, ?_⟩
    have := (CycleComparison.LiftSetting.mul_mem_pulseWindow_inter
      (by rw [hc]; exact hcpos : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) htt).1
    rw [hc] at this
    rw [hout]; exact this
  have hE : EdgeAgree (restrictLiftData A.Dt le_rfl
        {familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
            (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩)) with
          edge := Construction.Preservation.FullLift.windowEdges
            (c.D.slotStart M k / c.D.cellScaleSq M)
            ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M)
            (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
            (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))).edge}).edge
      (rLiftData c k).edge (rSeqStart c k) (rSeqEnd c k) := by
    rw [e2]
    exact edgeAgree_native_actual c.Gw ⟨k, hk⟩ (c.D.cellScaleSq M)
      (cr * liftLength c.D M / c.D.eps (M - 1)) _ _ _ _ hw
  have hmeas : ∀ v u d, ∀ γ ∈ (rLiftData c k).edge v u d, ∀ α X z,
      Measurable fun t => γ.coeff α t X z := by
    rw [e2]
    exact actual_liftEdges_coeff_measurable c.Gw hmeasF ⟨k, hk⟩ (c.D.cellScaleSq M)
      (cr * liftLength c.D M / c.D.eps (M - 1))
  have htr := isLiftSetting_transfer hset hs₀ ht hs₁ (Q₂ := rLiftData c k) hη.symm hG hv hE hmeas
  have hcg := isLiftSetting_congr_params (e' := ocEpsilon c.D.q c.D.Λ M)
    (E' := ocEpsilon c.D.q c.D.Λ (M - 1)) (ℓ' := ocEll c.D.q c.D.Λ M (c.D.κ M))
    (dstar' := ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
    (εc' := ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (lam' := rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) htr rfl hkap hkap1 hρ rfl
    (by rw [hkap]; rfl) (by rw [hkap, hkap1]) (by rw [hkap, hkap1, hρ]) (by rw [hρ]; rfl)
  rw [hkap] at hcg
  exact isLiftSetting_mono_const hcg (fun r hr q hq => hCa r hr q hq) (hΘ.trans hSb)
  
end AVRegularity.EntryTerminal.Ingredients.Recon.Setting
end
end

section
/-! # The core of the lift-setting step (`TermReconSettingCoreStatement`)

The constants of the window: `C_G, C_w` from `terminal_level_lift`, `C_a` the sum of the jet
constants `C_j r q` over `r ≤ q_s`, `q ≤ q_f`, `S_b = max(C_χ, 0)` and `C_g` from
`cycle_lift_grading`. At a context the settings come from `setting_of_native` and the
grading from `cycle_lift_grading` with `ReconSeqAt`.

Special cases:
- `C_χ < 0`: `S_b = 0`.
- A weak stage without edges: `C_j` can be taken zero. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Setting

theorem termReconSettingCore : TermReconSettingCoreStatement := by
  intro X
  obtain ⟨Λn, h128, hn⟩ := native_setting X
  refine ⟨Λn, h128, fun A hΛ hV ℓ => ?_⟩
  obtain ⟨CG, Cw, Cj, hCj, hn⟩ := hn A hΛ hV ℓ
  have hΛ128 : 128 ≤ A.Λ := h128.trans hΛ
  obtain ⟨-, -, -, ⟨-, hτ, hτT, -, -, -, hχw, -, -⟩, -, -⟩ := hV
  set qs := rKlift A ℓ + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2 with hqs
  set qf := max (rLlift A ℓ) (rLlift A ℓ + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt with hqf
  set Ca : ℝ := ∑ r ∈ Finset.range (qs + 1), ∑ q ∈ Finset.range (qf + 1), Cj r q with hCa
  have hCa0 : ∀ r, r ≤ qs → ∀ q, q ≤ qf → Cj r q ≤ Ca := by
    intro r hr q hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (qf + 1), Cj r q)
      (fun r _ => Finset.sum_nonneg fun q _ => hCj r q) (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
    exact Finset.single_le_sum (f := fun q => Cj r q) (fun q _ => hCj r q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hq))
  obtain ⟨Cg, hCg0, hgrad⟩ := Providers.cycle_lift_grading.{0, 0} A.NT (rKlift A ℓ) (rLlift A ℓ)
    (rLlift A ℓ) A.Dt A.dW CG Cw (fun _ _ => Ca)
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ hcr0 hcr1 hcre _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW hcK hkW hall
    cP CP cHP Cw' Ce cker hcP
  refine ⟨⟨(CG, Cw, Ca, max Cχ 0, Cg), le_max_right _ _, hCg0⟩, 1, 1, le_rfl, one_pos,
    fun j₀ _ => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hn nW cr cK CL Cχ kW hcr0 hcr1 hcK hkW j₀
  refine ⟨max M₀ 1, fun M hM c x => ?_⟩
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMn : M₀ ≤ M := (le_max_left _ _).trans hM
  have hΛ1 : 1 ≤ A.Λ := by omega
  intro hseq
  obtain ⟨hα, hq, hΛD, -, -, -, -⟩ := c.data
  have hq1 : 1 < c.D.q := hq ▸ X.hq.1
  have hε := Scales.epsilon_basic (m := M) hq1 (hΛD ▸ hΛ128)
  have hε1 : c.D.eps M ≤ 1 := by
    have := hε.2.1
    simpa only [OCData.eps] using this
  have hε0 : 0 ≤ c.D.eps M := by
    have := hε.1
    simpa only [OCData.eps] using this.le
  have hSb : Cχ * c.D.eps M ^ A.χw ≤ max Cχ 0 := by
    have h1 : c.D.eps M ^ A.χw ≤ 1 := Real.rpow_le_one hε0 hε1 hχw.le
    have h0 : 0 ≤ c.D.eps M ^ A.χw := Real.rpow_nonneg hε0 _
    rcases le_total 0 Cχ with h | h
    · exact (mul_le_of_le_one_right h h1).trans (le_max_left _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg h h0).trans (le_max_right _ _)
  have hset : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
      IsLiftSetting (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
        (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c)
        (ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M))
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
        (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (pulseParallel k)
        (pulseShearProfile c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.κ M) k) A.dW A.NT (rKlift A ℓ)
        (rLlift A ℓ) (rLlift A ℓ) qs qf CG Cw (fun _ _ => Ca)
        (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) (max Cχ 0) := fun k hk =>
    setting_of_native c hcre hΛ1 hM1 ℓ hCa0 hSb hk
      (hM₀ M hMn c.D c.data c.a c.lawW c.PW c.Gw c.aM c.weak x.reserve k
        (CycleComparison.LiftSetting.obsPulse_odd hk))
  refine ⟨qs, qf, fun k => pulseParallel k,
    fun k => pulseShearProfile c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.κ M) k,
    recordMajorant (c.Gw.mass c.lawW) c.Gw.fam, hset, ?_⟩
  intro k hk hh hhH n hn1 hnN m'' hm1 hmn j hj
  have hg := (hgrad (rLiftData c k) (c.Gw.mass c.lawW) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hset k hk) (c.CcT k) (hseq k hk) hh hhH n hn1 hnN m'' hm1 hmn j (by
      simp only [rAcl, rKmax, rKlift] at hj ⊢; omega)).1
  exact hg

end AVRegularity.EntryTerminal.Ingredients.Recon.Setting
end
end

section
/-! # `termReconSetting`

The lift settings and the grading of the terminal reconstruction window, from the core
(`termReconSettingCore`) and the lift sequences (`termReconSeq`). -/

@[expose] public section

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The lift settings and the grading of the terminal reconstruction window.** -/
theorem termReconSetting : TermReconSettingStatement :=
  termReconSetting_of Setting.termReconSettingCore termReconSeq

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
