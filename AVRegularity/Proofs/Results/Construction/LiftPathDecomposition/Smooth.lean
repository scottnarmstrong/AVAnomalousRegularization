-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Decomp
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import Mathlib.Data.Int.Star

section
@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! The ingredients of the uniqueness step supplied by the lift setting: the window data of the cell
equation, the regularity of the metric and the drift, and the regularity of the stage step data
(from `coeff_smooth` on the fiber edges and `flux_zero`). -/

section
section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} {Q : LiftOperatorData ι h Dm} {π : ι → ℝ}
  {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bb : ι → ι → ℝ} {Θ : ℝ}

/-- The window data of the cell equation. -/
theorem setting_window
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ) :
    ∀ X, ∃ lo A Mv : ℝ, AVRegularity.Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v
      t₀ t₁ lo A Mv := by
  have hη : 0 < Q.η := by rw [hS.η_eq]; exact div_pos hS.ν_pos hS.B_pos
  have hsq : 0 < Real.sqrt Q.η := Real.sqrt_pos.mpr hη
  have hbd : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, ‖Q.v t z‖ ≤ max (Cw 0) 0 / Real.sqrt Q.η := by
    intro t ht z
    have h0 := hS.w_jets 0 (Nat.zero_le _)
    have h1 : ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ ≤
        ENNReal.ofReal (Cw 0) :=
      le_trans (le_trans (le_iSup (fun z => ‖iteratedFDeriv ℝ 0
          (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ) z)
        (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) => ⨆ z : Vec 2,
          ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ) t ht)) h0
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [toReal_enorm, norm_iteratedFDeriv_zero, ENNReal.toReal_ofReal'] at h2
    rw [norm_smul, Real.norm_of_nonneg hsq.le] at h2
    rw [le_div_iff₀ hsq]
    linarith
  intro X
  exact ⟨3 / 4, 5 / 4, max (Cw 0) 0 / Real.sqrt Q.η,
    AVRegularity.Uniqueness.windowData_of_elliptic (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁
      (3 / 4) (5 / 4) _ (fun t => hS.G_symm t X 0 1) (by norm_num)
      (fun t ht ξ => hS.G_ellip t ht X ξ) hbd⟩

/-- The metric is `C^s` on the window for `s ≤ qs`. -/
theorem setting_G
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {s : ℕ} (hs : s ≤ qs) : ∀ t ∈ Icc t₀ t₁, ∀ a b, ContDiff ℝ (s : ℕ∞) (fun X => Q.G t X a b) :=
  fun t ht a b => (hS.G_smooth t ht a b).of_le (by exact_mod_cast hs)

/-- The drift components are good fields of order `s ≤ qf`. -/
theorem setting_v
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {s : ℕ} (hs : s ≤ qf) :
    ∀ t ∈ Icc t₀ t₁, ∀ κ, GoodField s (fun (_ z : Vec 2) => Q.v t z κ) := by
  intro t ht κ
  have e1 : (fun (_ z : Vec 2) => Q.v t z κ) = fun _ z => V t (z par.rev) * basisVec par κ := by
    funext X z; rw [hS.v_shear]; simp [smul_eq_mul]
  rw [e1]
  refine ⟨?_, fun X n x => ?_⟩
  · have hp : ContDiff ℝ (s : ℕ∞) (fun p : Vec 2 × Vec 2 => p.2 par.rev) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) par.rev).comp
        (ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2))).contDiff
    exact (((hS.V_smooth t ht).of_le (by exact_mod_cast hs)).comp hp).mul contDiff_const
  · simp only
    congr 1
    have hper := (hS.V_per t ht).int_mul (n par.rev)
    have := hper (x par.rev)
    simp only [mul_one] at this
    simp only [Pi.add_apply, AVenhance.latticeShift]
    exact this

/-- The coefficients of the edges are good fields of order `s ≤ qs, qf`. -/
theorem setting_coeff
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {s : ℕ} (hsX : s ≤ qs) (hsZ : s ≤ qf) {v u : ι} {d : Finset.Icc 2 Dm}
    {γ : Constituent d.1 (h u) (h v)} (hγ : γ ∈ Q.edge v u d) (α : DerivativeWord2 (d.1 - 1))
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) (κ : Fin 2) :
    GoodField s (fun X z => γ.coeff α t X z κ) := by
  refine ⟨?_, fun X n x => ?_⟩
  · have hb := (hS.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hsX hsZ
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ).contDiff.comp hb
  · simp only
    rw [γ.periodic α t X n x]

theorem setting_bounds
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ) :
    N + 2 + Dm ≤ qs ∧ N + 2 + Dm ≤ qf := by
  have hN := hS.N_ge
  have hD := hS.D_ge
  constructor
  · rw [hS.qs_eq]
    have h1 : N + Dm ≤ (N + Dm) ^ 2 := by nlinarith
    have h2 : (N + Dm) ^ 2 ≤ (H + 1) * (N + Dm) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 4 * (H + 1) * (N + Dm) ^ 2 = 4 * ((H + 1) * (N + Dm) ^ 2) := by ring
    omega
  · rw [hS.qf_eq]
    omega

end Setting

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The stage step data are good** under the lift setting of the fiber. -/
theorem stage_goodDat [∀ r, FiniteDimensional ℝ (hr r)] (G : GenStage D hr Dm b j₀) (m : ℕ)
    (k : ℤ) (A : RealChain) (ρ : ℝ) (p : OddSlot) (c : StageCtx D b j₀ G.level p)
    {π : CompIn G.comps → ℝ} {t₀ t₁ e ν B ρ' E ℓ dstar εc lam : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {H N K kk L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {bb : CompIn G.comps → CompIn G.comps → ℝ} {Θ : ℝ}
    (hS : IsLiftSetting (familyLiftData D m k A ρ (G.fam.fiber p c)) π t₀ t₁ e ν B ρ' E ℓ dstar
      εc lam par V H N K kk L qs qf CG Cw Cj bb Θ)
    {s : ℕ} (hsX : s ≤ qs) (hsZ : s ≤ qf) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    ∀ t ∈ Icc t₀ t₁, GoodDat s t (stageDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c v u γ) := by
  classical
  intro t ht d α κ
  by_cases hd : 2 ≤ d ∧ d ≤ (G.fam.identity v u γ).maxOrder ∧ d ≤ Dm
  · let γ' : Constituent (⟨d, Finset.mem_Icc.mpr ⟨hd.1, hd.2.2⟩⟩ : Finset.Icc 2 Dm).1
        (hr u.1.root) (hr v.1.root) :=
      { map := (G.fam.identity v u γ).map,
        coeff := fun α t X z => G.fam.flux p c v u γ d α (D.cellScaleSq m * t)
          ((ρ / D.eps (m - 1)) • X) z,
        periodic := fun α t X => G.fam.flux_periodic p c v u γ d α (D.cellScaleSq m * t)
          ((ρ / D.eps (m - 1)) • X),
        record := (G.fam.identity v u γ).record,
        birthExcess_ge := le_trans hd.2.1 (G.fam.identity v u γ).le_birth }
    have hmem : γ' ∈ (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).edge v u
        ⟨d, Finset.mem_Icc.mpr ⟨hd.1, hd.2.2⟩⟩ := by
      exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨γ, Finset.mem_toList.mpr
        (Finset.mem_univ _), dite_eq_left_of_eq_true (eq_true hd.2.1)⟩, rfl⟩
    exact (setting_coeff hS hsX hsZ hmem α ht κ).congr fun X z => by
      simp only [stageDat]; rw [ite_eq_left hd.2.2]
  · refine GoodField.zero.congr fun X z => ?_
    simp only [stageDat]
    split_ifs with hdD
    · have h0 := G.fam.flux_zero p c v u γ d α (by tauto)
      simp [h0]
    · rfl
end

/-! The uniqueness-step hypotheses for the stage and its path families. The arising step data are
those of the stage paths of at most `h` edges; their chain lifts are the path lifts of chosen
paths, with the path-family operator data. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The step data of the stage paths of at most `h` edges. -/
def stArise (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (h : ℕ) : ∀ g, (Fin g → StepDat) → Prop :=
  fun g cd => g ≤ h ∧ ∃ σ : StagePath G g, pathDat G c₀ lam p c σ = cd

open Classical in
/-- The chain lift of arising step data: the path lift of a chosen path. -/
def stLift (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (h : ℕ)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) :
    ∀ g, (Fin g → StepDat) → ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ) :=
  fun g cd => if hA : stArise G c₀ lam p c h g cd then Ccπ g (Classical.choose hA.2) else 0

open Classical in
/-- The chain operator data of arising step data: the path family of a chosen path. -/
def stQc (G : GenStage D hr Dm b j₀) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (h : ℕ) :
    ∀ g, (Fin g → StepDat) → LiftOperatorData (Fin (g + 1)) (fun _ => ℝ) Dm :=
  fun g cd => familyLiftData D m k A ρ
    (if hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd then
      pathEdges G (Classical.choose hA.2) p c else fun _ _ _ => [])

/-- The common hypotheses: the lift setting of the fiber, the path lifts, and the regularity
indices. -/
structure StageSetting (G : GenStage D hr Dm b j₀) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (p : OddSlot) (c : StageCtx D b j₀ G.level p) (t₀ t₁ : ℝ) (h N sX sZ : ℕ)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) : Prop where
  hS : ∃ (π : CompIn G.comps → ℝ) (e ν B ρ' E ℓ dstar εc lam : ℝ) (par : Fin 2)
    (V : ℝ → ℝ → ℝ) (K kk L qs qf : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (bb : CompIn G.comps → CompIn G.comps → ℝ) (Θ : ℝ),
    IsLiftSetting (familyLiftData D m k A ρ (G.fam.fiber p c)) π t₀ t₁ e ν B ρ' E ℓ dstar
      εc lam par V h N K kk L qs qf CG Cw Cj bb Θ
  hπ : ∀ h' ≤ h, ∀ σ : StagePath G h', IsLiftSequence
    (familyLiftData D m k A ρ (pathEdges G σ p c)) sX sZ t₀ t₁ N h' (Ccπ h' σ)
  hsX : N + 1 + Dm ≤ sX
  hsZ : N + 1 + Dm ≤ sZ

namespace StageSetting

variable {G : GenStage D hr Dm b j₀} {m : ℕ} {k : ℤ} {A : RealChain} {ρ : ℝ} {p : OddSlot}
  {c : StageCtx D b j₀ G.level p} {t₀ t₁ : ℝ} {h N sX sZ : ℕ}
  {Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)}

theorem window (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) : t₀ ≤ t₁ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  exact hS.window

theorem D2 (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) : 2 ≤ Dm := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  exact hS.D_ge

theorem windowData (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (X : Vec 2) :
    ∃ lo A' Mv : ℝ, AVRegularity.Uniqueness.WindowData
      (fun t => Matrix.of ((familyLiftData (ι := CompIn G.comps) D m k A ρ
        (G.fam.fiber p c)).G t X))
      (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).v t₀ t₁ lo A' Mv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  exact setting_window hS X

theorem metric (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) :
    ∀ t ∈ Icc t₀ t₁, ∀ a b', ContDiff ℝ ((N + 2 : ℕ) : ℕ∞) (fun X =>
      (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).G t X a b') := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  exact setting_G hS (by have := (setting_bounds hS).1; omega)

theorem drift (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) :
    ∀ t ∈ Icc t₀ t₁, ∀ κ, GoodField (N + 2) (fun (_ z : Vec 2) =>
      (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).v t z κ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  exact setting_v hS (by have := (setting_bounds hS).2; omega)

theorem goodDat [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) : ∀ t ∈ Icc t₀ t₁,
      GoodDat (N + 1 + Dm) t (stageDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c v u γ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS⟩ := H.hS
  have hb := setting_bounds hS
  exact stage_goodDat G m k A ρ p c hS (by omega) (by omega) v u γ

theorem goodDat_path [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    (σ : StagePath G g) (i : Fin g) : ∀ t ∈ Icc t₀ t₁,
      GoodDat (N + 1 + Dm) t (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ i) :=
  H.goodDat _ _ _

/-- The arising step data are good. -/
theorem goodDat_arise [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    {cd : Fin g → StepDat} (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd)
    (i : Fin g) : ∀ t ∈ Icc t₀ t₁, GoodDat (N + 1 + Dm) t (cd i) := by
  obtain ⟨_, σ, rfl⟩ := hA
  exact H.goodDat_path σ i

theorem qc_flux [∀ r, FiniteDimensional ℝ (hr r)] {g : ℕ} {cd : Fin g → StepDat}
    (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd) :
    HasFamFlux (stQc G m k A ρ p c h g cd) (chainFam cd) := by
  classical
  have e := Classical.choose_spec hA.2
  have hf := hasFamFlux_pathEdges G m k A ρ p c (Classical.choose hA.2)
  rw [e] at hf
  simp only [stQc, dite_eq_left_of_eq_true (eq_true hA)]
  exact hf

theorem lift_seq (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    {cd : Fin g → StepDat} (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd) :
    IsLiftSequence (stQc G m k A ρ p c h g cd) sX sZ t₀ t₁ N g
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ g cd) := by
  classical
  simp only [stQc, stLift, dite_eq_left_of_eq_true (eq_true hA)]
  exact H.hπ g hA.1 _

/-- Segments of arising data arise. -/
theorem arise_chain [∀ r, FiniteDimensional ℝ (hr r)] {L : ℕ} {cd : Fin L → StepDat}
    (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h L cd) {g : ℕ}
    {w v : Fin (L + 1)} (τ : (chainFam cd).Walk g w v) (hg : g ≤ L) :
    stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g ((chainFam cd).walkDat τ) := by
  obtain ⟨hL, σ, rfl⟩ := hA
  refine ⟨hg.trans hL, ?_⟩
  have ht := chain_walk_target _ τ
  obtain ⟨σ', hσ'⟩ := stage_path_segment (G := G) (c₀ := D.cellScaleSq m) (lam := ρ / D.eps (m - 1)) (p := p)
    (c := c) σ w.val g
    (by have := v.isLt; omega)
  exact ⟨σ', by rw [hσ', chain_walkDat]⟩

/-- **The step hypotheses of a path family.** -/
theorem chainHyp [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {L : ℕ} (hL : L ≤ h)
    (σ : StagePath G L) {cd : Fin L → StepDat}
    (hcd : pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ = cd) :
    StepHyp (chainFam cd) (familyLiftData D m k A ρ (pathEdges G σ p c))
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
      (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N L where
  hQ := hcd ▸ hasFamFlux_pathEdges G m k A ρ p c σ
  hab := H.window
  hW := H.windowData
  hQc _ _ hA := qc_flux hA
  hη _ _ := rfl
  hG _ _ := rfl
  hv _ _ := rfl
  hLs _ _ hA := H.lift_seq hA
  hcd _ _ hA := H.goodDat_arise hA
  hdat _ i _ := by subst hcd; exact H.goodDat_path σ _
  hGr := H.metric
  hvr := H.drift
  hD2 := H.D2
  hsX := H.hsX
  hsZ := H.hsZ
  hNr := le_rfl
  hArise _ _ _ τ hg := arise_chain (hcd ▸ ⟨hL, σ, rfl⟩) τ hg

/-- **The step hypotheses of the stage.** -/
theorem stageHyp [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) :
    StepHyp (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c)
      (familyLiftData D m k A ρ (G.fam.fiber p c))
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
      (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N h where
  hQ := hasFamFlux_fiber G m k A ρ p c
  hab := H.window
  hW := H.windowData
  hQc _ _ hA := qc_flux hA
  hη _ _ := rfl
  hG _ _ := rfl
  hv _ _ := rfl
  hLs _ _ hA := H.lift_seq hA
  hcd _ _ hA := H.goodDat_arise hA
  hdat v u γ := H.goodDat v u γ
  hGr := H.metric
  hvr := H.drift
  hD2 := H.D2
  hsX := H.hsX
  hsZ := H.hsZ
  hNr := le_rfl
  hArise _ _ _ q hg := ⟨hg, stage_walk_path q⟩

/-- The arising chain families satisfy the step hypotheses. -/
theorem chainHyps [∀ r, FiniteDimensional ℝ (hr r)] (H : StageSetting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) :
    ∀ L (cd : Fin L → StepDat), stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h L cd →
      StepHyp (chainFam cd) (stQc G m k A ρ p c h L cd)
        (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
        (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N L := by
  classical
  intro L cd hA
  have := H.chainHyp hA.1 (Classical.choose hA.2) (Classical.choose_spec hA.2)
  simp only [stQc, dite_eq_left_of_eq_true (eq_true hA)]
  exact this

end StageSetting
end

end AVRegularity.Providers.PathDecomp
end
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! **Path decomposition of the full lift** (conditional form). The full lift of the fiber and the
path lifts agree on the window with the path-candidate arrays built from the top entries of the
chosen path lifts (`decomp`); their slow fluxes are the walk sums of `formX`, and the walks of the
stage are its paths (`sum_stageWalk_eq`).

Two premises are added to the statement `lift_path_decomposition`:
* `hf : ContDiff ℝ ⊤ f`: the test fields `f(ℓ·) e` enter the lift equations through their
  derivatives; for a non-smooth `f` the junk derivatives make the candidate arrays fail the cell
  equations.
* `hsXN, hsZN : N + Dm + 1 ≤ sX, sZ`: the cell sources of degree `n ≤ N` differentiate the lower
  means up to order `n - 2` and the source coefficients up to `Dm`, beyond the statement's
  `Dm + 2 ≤ sX, sZ`. -/

open AVRegularity.Providers.PathDecomp AVRegularity.Uniqueness

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

open scoped Classical in
/-- **Path decomposition of the full lift**, for a smooth test profile `f` and regularity indices
`N + Dm + 1 ≤ sX, sZ` (conditional form of `lift_path_decomposition`: the two extra
premises `hf`, `hsXN`, `hsZN` are not in the statement). -/
theorem lift_path_decomposition_of_smooth {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm b j₀) (m : ℕ) (hm : G.level = m) (k : ℤ) (hk : Odd k)
    (hnat : (G.actual ⟨k, hk⟩).1 = nativeChain m k) (sX sZ N : ℕ)
    (h : ℕ)
    (π : CompIn G.comps → ℝ) (e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ)
    (K kk L qs qf : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (bb : CompIn G.comps → CompIn G.comps → ℝ)
    (Θ : ℝ)
    (hS : IsLiftSetting (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) π (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)
        e ν B ρ E ℓ dstar εc lam par V h N K kk L qs qf CG Cw Cj bb Θ)
    (hsX : sX ≤ qs) (hsZ : sZ ≤ qf) (hsX₂ : Dm + 2 ≤ sX) (hsZ₂ : Dm + 2 ≤ sZ)
    (CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hT : IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h CcT)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : ∀ h' ≤ h, ∀ σ : StagePath G h', IsLiftSequence
      (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (pathEdges G σ ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h' (Ccπ h' σ))
    (u v : CompIn G.comps) (f : Vec 2 → ℝ) (ev : hr u.1.root) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m))
    (X : Vec 2) (j : Fin 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsXN : N + Dm + 1 ≤ sX) (hsZN : N + Dm + 1 ≤ sZ) :
    ∀ h' : ℕ, 1 ≤ h' → h' ≤ h →
    fieldCellMean (fun z => liftFluxX (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) CcT
        (fun _ Y => Pi.single u (f (liftLength D m • Y) • ev)) h' n t X z j v) =
      ∑ st : Fin h' → (Σ (v' u' : CompIn G.comps), G.fam.Γ v' u'),
        if hj : ∀ (i : ℕ) (hi : i + 1 < h'), (st ⟨i + 1, hi⟩).2.1 = (st ⟨i, by omega⟩).1 then
          if (StagePath.src ⟨st, hj⟩ = u.1 ∧ StagePath.tgt ⟨st, hj⟩ = v.1) then
            fieldCellMean (fun z => liftFluxX (familyLiftData D m k (nativeChain m k)
                (liftLength D m) (pathEdges G ⟨st, hj⟩ ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
                (Ccπ h' ⟨st, hj⟩)
                (fun _ Y => Pi.single (0 : Fin (h' + 1)) (f (liftLength D m • Y))) h' n t X z j
                (Fin.last h')) •
              rootPathMap hr u.1.root (StagePath.mapList ⟨st, hj⟩) v.1.root ev
          else 0
        else 0 :=
by
  classical
  have _ := hm
  have _ := hnat
  have _ := hsX
  have _ := hsZ
  have _ := hsX₂
  have _ := hsZ₂
  intro h' h1 hh'
  have H : StageSetting G m k (nativeChain m k) (liftLength D m) ⟨k, hk⟩ (G.actual ⟨k, hk⟩)
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) h N sX sZ Ccπ :=
    ⟨⟨π, e, ν, B, ρ, E, ℓ, dstar, εc, lam, par, V, K, kk, L, qs, qf, CG, Cw, Cj, bb, Θ, hS⟩, hπ,
      by omega, by omega⟩
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => f (liftLength D m • Y)) :=
    hf.comp (contDiff_const_smul _)
  have hSt := H.stageHyp
  set C := ctxOf (familyLiftData (ι := CompIn G.comps) D m k (nativeChain m k) (liftLength D m)
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (fun Y : Vec 2 => f (liftLength D m • Y))
      (topOf (stLift G (D.cellScaleSq m) (liftLength D m / D.eps (m - 1)) ⟨k, hk⟩
        (G.actual ⟨k, hk⟩) h Ccπ)
        (stArise G (D.cellScaleSq m) (liftLength D m / D.eps (m - 1)) ⟨k, hk⟩
          (G.actual ⟨k, hk⟩) h)) t with hC
  have hT' : C.GoodT (N + 1 + Dm) := hSt.goodT _ ht
  have hGv : C.GoodGv (N + 2) := hSt.goodGv _ _ ht
  have hdat := fun v u γ => H.goodDat v u γ t ht
  -- the full lift on the window is the path-candidate array
  have hdS := decomp hSt (fun L cd hA _ => H.chainHyps L cd hA) hT
  have eL : liftFluxX (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) CcT
        (fun _ Y => Pi.single u (f (liftLength D m • Y) • ev)) h' n t =
      liftFluxX (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (cand _ C.T)
        (fun _ Y => Pi.single u (C.g₀ Y • ev)) h' n t :=
    liftFluxX_congr _ _ _ _ h' n t fun hh'' hle n' m' α =>
      hdS hh'' (le_trans hle hh') n' t ht m' α
  -- each path lift on the window is the candidate array of its chain family
  have key : ∀ σ : StagePath G h',
      fieldCellMean (fun z => liftFluxX (familyLiftData D m k (nativeChain m k)
          (liftLength D m) (pathEdges G σ ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
          (Ccπ h' σ)
          (fun _ Y => Pi.single (0 : Fin (h' + 1)) (f (liftLength D m • Y))) h' n t X z j
          (Fin.last h')) =
        fieldCellMean (C.formX n h'
          (pathDat G (D.cellScaleSq m) (liftLength D m / D.eps (m - 1)) ⟨k, hk⟩
            (G.actual ⟨k, hk⟩) σ) j X) := by
    intro σ
    have hdσ := decomp (H.chainHyp hh' σ rfl) (fun L cd hA _ => H.chainHyps L cd hA)
      (H.hπ h' hh' σ)
    have eσ := liftFluxX_congr (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (pathEdges G σ ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (Ccπ h' σ) (cand _ C.T)
      (fun _ Y => Pi.single (0 : Fin (h' + 1)) (C.g₀ Y)) h' n t fun hh'' hle n' m' α =>
        hdσ hh'' hle n' t ht m' α
    congr 1
    funext z
    have := congrFun (congrFun (congrFun eσ X) z) j
    simp only [hC, ctxOf] at this
    rw [this]
    exact chain_liftFluxX_last _ _ (hasFamFlux_pathEdges G m k _ _ _ _ σ) C rfl rfl rfl rfl
      hT' hg₀ (fun i => H.goodDat_path σ i t ht) n X z j
  -- the full side as a sum over walks
  have eF : ∀ z, liftFluxX (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) CcT
        (fun _ Y => Pi.single u (f (liftLength D m • Y) • ev)) h' n t X z j v =
      ∑ q : (stageFam G (D.cellScaleSq m) (liftLength D m / D.eps (m - 1)) ⟨k, hk⟩
          (G.actual ⟨k, hk⟩)).Walk h' u v,
        C.formX n h' ((stageFam G _ _ _ _).walkDat q) j X z •
          (stageFam G _ _ _ _).compMap q ev := by
    intro z
    rw [eL]
    exact (congrFun (liftFluxX_cand _ _ (hasFamFlux_fiber G m k _ _ _ _) C rfl rfl rfl rfl hT' hg₀
      hdat ev h' n X z j) v).trans (by rw [sum_walkVec_apply])
  simp only [eF]
  have hc : ∀ q ∈ (Finset.univ : Finset ((stageFam G (D.cellScaleSq m)
      (liftLength D m / D.eps (m - 1)) ⟨k, hk⟩ (G.actual ⟨k, hk⟩)).Walk h' u v)),
      Continuous (C.formX n h' ((stageFam G _ _ _ _).walkDat q) j X) := fun q _ =>
    (C.goodField_formX (r := N) hT' hg₀ hGv n h' _
      (goodDat_walkDat _ hdat q) j).continuous_slice X
  have hsum := fieldCellMean_clm_sum Finset.univ
    (fun q => (ContinuousLinearMap.id ℝ ℝ).smulRight ((stageFam G _ _ _ _).compMap q ev)) hc
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hsum
  rw [hsum]
  rw [sum_stageWalk_eq h1 u v ev
    (fun cd => fieldCellMean (C.formX n h' cd j X))]
  refine Finset.sum_congr rfl fun st _ => ?_
  split_ifs with hj hc'
  · rw [key ⟨st, hj⟩]
  · rfl
  · rfl

end AVRegularity.Providers
end
end
