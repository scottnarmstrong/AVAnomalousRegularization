-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.CoarseFlux.Time
public import AVRegularity.CycleComparison.Residual.LiftStatements
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.BoundPointwise

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxBound

/-! Coarse flux bound: the Schur cell-`L²` jets of the lift coefficient arrays from the grading
statement, and the vanishing of the zeroth-order coefficients from the structure statement. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eLpNorm_iteratedFDeriv_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Vec 2 → G) (μ : Measure (Vec 2)) :
    eLpNorm (fun z => iteratedFDeriv ℝ 0 g z) 2 μ = eLpNorm g 2 μ := by
  have hL : ∀ z, iteratedFDeriv ℝ 0 g z =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) G).symm (g z) := fun z => by
    rw [iteratedFDeriv_zero_eq_comp]; rfl
  by_cases hm : AEStronglyMeasurable g μ
  · have hm' : AEStronglyMeasurable (fun z => iteratedFDeriv ℝ 0 g z) μ := by
      simp_rw [hL]
      exact (continuousMultilinearCurryFin0 ℝ (Vec 2) G).symm.continuous.comp_aestronglyMeasurable hm
    exact eLpNorm_congr_norm_ae hm' hm (Filter.Eventually.of_forall fun z => by
      simp [norm_iteratedFDeriv_zero])
  · have hm' : ¬ AEStronglyMeasurable (fun z => iteratedFDeriv ℝ 0 g z) μ := fun h' => hm (by
      have := (continuousMultilinearCurryFin0 ℝ (Vec 2) G).continuous.comp_aestronglyMeasurable h'
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [hL])
    rw [eLpNorm_of_not_aestronglyMeasurable hm, eLpNorm_of_not_aestronglyMeasurable hm']

/-- The cell `L²` slow jet is at most the cell energy jet (the fast order zero term). -/
theorem cellL2Jet_le_cellEnergyJet (I : Set ℝ) (k j : ℕ) (f : ℝ → Vec 2 → Vec 2 → E) :
    cellL2Jet I j f ≤ cellEnergyJet I k j f := by
  unfold cellL2Jet cellEnergyJet
  refine le_trans ?_ (Finset.single_le_sum (f := fun q => ⨆ X : Vec 2, fieldEnergyNorm I
    (fun t z => iteratedFDeriv ℝ q (fun z' => iteratedFDeriv ℝ j (fun X' => f t X' z') X) z))
    (fun _ _ => bot_le) (Finset.mem_range.2 (Nat.succ_pos k)))
  refine iSup₂_le fun t ht => iSup_le fun X => ?_
  refine le_trans ?_ (le_iSup _ X)
  unfold fieldEnergyNorm
  refine le_trans ?_ le_self_add
  refine le_trans ?_ (le_iSup₂ (f := fun t (_ : t ∈ I) => cellL2Norm (fun z =>
    iteratedFDeriv ℝ 0 (fun z' => iteratedFDeriv ℝ j (fun X' => f t X' z') X) z)) t ht)
  unfold cellL2Norm
  exact (eLpNorm_iteratedFDeriv_zero _ _).ge

theorem schurCellL2Jet_le_schurEnergyJet {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (k j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) :
    schurCellL2Jet π I j c ≤ schurEnergyJet π I k j c := by
  unfold schurCellL2Jet schurEnergyJet
  exact schurSums_mono π fun v u => Finset.sum_le_sum fun a _ =>
    cellL2Jet_le_cellEnergyJet I k j _

theorem cellL2Jet_eq_zero_of_forall {I : Set ℝ} (j : ℕ) {f : ℝ → Vec 2 → Vec 2 → E}
    (hf : ∀ t ∈ I, ∀ X z, f t X z = 0) : cellL2Jet I j f = 0 := by
  unfold cellL2Jet
  refine le_antisymm (iSup₂_le fun t ht => iSup_le fun X => ?_) bot_le
  have h0 : (fun z : Vec 2 => iteratedFDeriv ℝ j (fun X' => f t X' z) X) = 0 := by
    funext z
    have : (fun X' => f t X' z) = fun _ => (0 : E) := funext fun X' => hf t ht X' z
    rw [this]; simp [iteratedFDeriv_fun_zero]
  rw [h0]
  exact le_of_eq (eLpNorm_zero (ε := ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E))

theorem schurCellL2Jet_eq_zero_of_forall {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a, ∀ t ∈ I, ∀ X z v u, c a t X z v u = 0) : schurCellL2Jet π I j c = 0 := by
  unfold schurCellL2Jet schurSums
  have h0 : ∀ v u, ∑ a : κ, cellL2Jet I j (fun t X z => c a t X z v u) = 0 := fun v u =>
    Finset.sum_eq_zero fun a _ => cellL2Jet_eq_zero_of_forall j fun t ht X z => hc a t ht X z v u
  simp [h0]

/-- A product of a nonpositive-or-bounded coefficient with a factor in `[0,1]`. -/
theorem ofReal_mul_le_of_le_one (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ENNReal.ofReal (a * b) ≤ ENNReal.ofReal a := by
  rcases le_or_gt 0 a with ha | ha
  · exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right ha hb1)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha.le hb0)]
    exact zero_le
end

/-! Coarse flux bound: the zeroth-order lift coefficients vanish when the lift action annihilates
constant coarse fields. -/

theorem orderedDerivative_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (β : DerivativeWord2 j) (c0 : E) :
    orderedDerivative β (fun _ : Vec 2 => c0) = fun _ => if j = 0 then c0 else 0 := by
  induction j with
  | zero => rw [orderedDerivative_zero]; simp
  | succ j ih =>
    rw [orderedDerivative_succ, ih]
    funext x
    simp

theorem coeff_zero_of_const {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (c : LiftCoeff ι h) (n : ℕ)
    (t : ℝ) (X z : Vec 2)
    (H : ∀ c0 : ∀ i, h i, liftApply n c (fun _ _ => c0) t X z = 0) (α : DerivativeWord2 0)
    (v u : ι) : c 0 α t X z v u = 0 := by
  classical
  ext w
  have h1 := congrFun (H (Pi.single u w)) v
  simp only [liftApply, Pi.zero_apply] at h1
  have hm0 : ∀ m ∈ Finset.range (n + 1), m ≠ 0 → ∑ α' : DerivativeWord2 m, ∑ u' : ι,
      c m α' t X z v u' (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u')
        = 0 := by
    intro m _ hm
    refine Finset.sum_eq_zero fun α' _ => Finset.sum_eq_zero fun u' _ => ?_
    simp [orderedDerivative_const, hm]
  rw [Finset.sum_eq_single 0 hm0 (fun h0 => absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0)] at h1
  have hα : ∀ α' ∈ (Finset.univ : Finset (DerivativeWord2 0)), α' ≠ α → ∑ u' : ι,
      c 0 α' t X z v u' (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u')
        = 0 := fun α' _ hα' => absurd (funext fun i => i.elim0) hα'
  rw [Finset.sum_eq_single α hα (fun h0 => absurd (Finset.mem_univ _) h0)] at h1
  rw [Finset.sum_eq_single u] at h1
  · simpa [orderedDerivative_const] using h1
  · intro u' _ hu'
    simp [orderedDerivative_const, Pi.single_eq_of_ne hu']
  · simp

end AVRegularity.CoarseFluxBound
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The bound of the coarse flux presentation, conditional on the lift grading and structure
statements: when `cycle_lift_grading` and `cycle_lift_structure` hold, so does
`cycle_residual_coarse_flux`. -/

open CoarseFluxBound

universe u v

theorem cycle_residual_coarse_flux_of_lift (Acl N D H kl Ll : ℕ) (hA : 1 ≤ Acl)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (hgrad : CycleLiftGradingStatement.{u, v} N (Acl + 2) kl Ll D H CG Cw Cj)
    (hstruct : CycleLiftStructureStatement.{u, v} N (Acl + 2) kl Ll D H CG Cw Cj) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N s0 kl Ll qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
          IsLiftSequence Q (s0 + D + 2) (max (kl + 1) (Ll + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H →
        ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ t, ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
          (∀ t, ∀ k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
        ∀ Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain s0 (max (kl + 1) (Ll + 2)) Acl (liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) τ) (fun _ _ _ => 0)
              (fun j => Vn n j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => (if hh = 0 then Fc t x k else 0)
                + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x k)
              (fun t x => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
                εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x)
            ≤ ENNReal.ofReal (C * ((if hh = 0 then Real.sqrt (B / ν) else 0)
                + Θ ^ hh * εc ^ 2 * (1 + Z)) * (Real.sqrt B)⁻¹) *
              classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres Fc := by
  obtain ⟨C₀, hC₀, Hg⟩ := hgrad
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = ∑ n ∈ Finset.Icc 1 N, fluxChainConst n Acl := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ : ∃ Cr : ℝ, Cr = ∑ n ∈ Finset.Icc 1 N, remChainConst n Acl := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := hCf ▸ Finset.sum_nonneg fun n _ => fluxChainConst_nonneg n Acl
  have hCr0 : 0 ≤ Cr := hCr ▸ Finset.sum_nonneg fun n _ => remChainConst_nonneg n Acl
  refine ⟨max (Real.sqrt 2) (max (C₀ * Real.sqrt (2 * N * Cf)) (C₀ * Real.sqrt (N * Cr))),
    le_max_of_le_left (Real.sqrt_nonneg _), ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ kres s0 hkres hs0 hset
    hM Cc hseq hh hhH Fc hFc hFcper Vn hVn Z hZ
  subst hs0
  have hS := hstruct Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq
  have hG0 := Hg Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq
  have hℓ : 0 < ℓ := by
    rw [hset.ℓ_eq]; exact div_pos hset.e_pos (Real.sqrt_pos.2 hset.ν_pos)
  have hρ := hset.ρ_pos
  have he := hset.e_pos
  have hν := hset.ν_pos
  have hB := hset.B_pos
  have hε : εc = ℓ * Real.sqrt B / ρ := by rw [hset.εc_eq, hset.dstar_eq]
  have hε0 : 0 ≤ εc := by rw [hε]; positivity
  have hε1 := hset.εc_le
  have hηB : ν ≤ B := by
    have := hset.η_le
    rw [hset.η_eq, div_le_one hB] at this
    exact this
  have heρ : e ≤ ρ := by
    have h1 : ℓ * Real.sqrt B = ρ * εc := by rw [hε]; field_simp
    have h2 : e = ℓ * Real.sqrt ν := by
      rw [hset.ℓ_eq]; field_simp
    have h3 : Real.sqrt ν ≤ Real.sqrt B := Real.sqrt_le_sqrt hηB
    calc e = ℓ * Real.sqrt ν := h2
      _ ≤ ℓ * Real.sqrt B := by gcongr
      _ = ρ * εc := h1
      _ ≤ ρ * 1 := by gcongr
      _ = ρ := mul_one ρ
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hρ.le hset.E_pos.le
  have hlam1 := hset.lam_le
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = max (C₀ * Θ ^ hh) 0 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := hθdef ▸ le_max_right _ _
  have hsθ : ENNReal.ofReal (C₀ * Θ ^ hh) = ENNReal.ofReal θ := by
    rcases le_total 0 (C₀ * Θ ^ hh) with h0 | h0
    · rw [hθdef, max_eq_left h0]
    · rw [hθdef, max_eq_right h0, ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_zero]
  have hjet0 : ∀ n, 1 ≤ n → n ≤ N → ∀ i,
      schurCellL2Jet π (Set.Icc t₀ t₁) i (Cc hh n 0) = 0 := by
    intro n h1 h2 i
    refine schurCellL2Jet_eq_zero_of_forall π _ i _ (fun α t ht X z v u => ?_)
    exact coeff_zero_of_const (Cc hh n) n t X z (fun c0 =>
      (hS.1 c0 hh hhH t ht X z).1 n h1 h2) α v u
  have hjets : ∀ n, 1 ≤ n → n ≤ N → ∀ i, i ≤ Acl + 2 → ∀ m,
      schurCellL2Jet π (Set.Icc t₀ t₁) i (Cc hh n m) ≤ ENNReal.ofReal θ := by
    intro n h1 h2 i hi m
    rw [← hsθ]
    by_cases hm0 : m = 0
    · subst hm0; rw [hjet0 n h1 h2 i]; exact zero_le
    by_cases hmn : m ≤ n
    · have hg := (hG0 hh hhH n h1 h2 m (by omega) hmn i hi).1
      refine (schurCellL2Jet_le_schurEnergyJet π _ kl i _).trans (hg.trans ?_)
      have hlp : 0 ≤ lam ^ (n - m + i) := pow_nonneg hlam0 _
      have hlq : lam ^ (n - m + i) ≤ 1 := pow_le_one₀ hlam0 hlam1
      have := ofReal_mul_le_of_le_one (C₀ * Θ ^ hh) _ hlp hlq
      exact this
    · have hz := hseq.2.2.2.1 hh hhH n m (by omega)
      rw [schurCellL2Jet_eq_zero_of_forall π _ i _ (fun α t _ X z v u => hz α t X z v u)]
      exact zero_le
  have hbox : ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
      IsBoxSmooth (Acl + 2) 0 (fun X y => Cc hh n m α t X y v u) := fun n m α v u t ht =>
    BoundTail.isBoxSmooth_slow_zero (hseq.2.2.2.2.2.1 hh hhH n m α v u t ht).1 (by omega)
  have hTime : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      TimeData π (Set.Icc t₀ t₁) Acl (max (kl + 1) (Ll + 2)) N kres (fun n => Cc hh n) Fc ℓ ρ e εc
        ((ℓ ^ 2)⁻¹ * t) (ENNReal.ofReal θ) (fun n j => Vn n j ((ℓ ^ 2)⁻¹ * t)) := by
    intro t ht
    have hℓ2 : 0 < ℓ ^ 2 := by positivity
    have hτ : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc t₀ t₁ := by
      constructor
      · rw [le_inv_mul_iff₀ hℓ2]; linarith [ht.1]
      · rw [inv_mul_le_iff₀ hℓ2]; linarith [ht.2]
    refine ⟨fun n hn => ?_, hε0, hε1, fun k => hFc _ k⟩
    have hn1 := (Finset.mem_Icc.1 hn).1
    have hn2 := (Finset.mem_Icc.1 hn).2
    exact ⟨hset.mass_pos, hτ, hρ, he, heρ, hM, hA, by omega, by omega,
      fun m α v u => hbox n m α v u _ hτ, hjet0 n hn1 hn2,
      fun i hi m => hjets n hn1 hn2 i hi m, fun k => hFc _ k,
      hVn n hn1 hn2 _ hτ⟩
  have hmeasI : MeasurableSet (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) := measurableSet_Icc
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hLnn : 0 ≤ ℓ ^ 2 * (t₁ - t₀) := mul_nonneg hℓ2.le (sub_nonneg.2 hset.window)
  have hℓτ : ∀ t : ℝ, ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * t) = t := fun t => by field_simp
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = Real.sqrt ((if hh = 0 then 2 else 0) +
      2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 * Cf) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = Real.sqrt (N * (ρ⁻¹ * (e / ρ) ^ Acl) ^ 2 * εc ^ 2 * θ ^ 2 *
      Cr) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := hK₁ ▸ Real.sqrt_nonneg _
  have hK₂0 : 0 ≤ K₂ := hK₂ ▸ Real.sqrt_nonneg _
  have hK₁sq : K₁ ^ 2 = (if hh = 0 then 2 else 0) + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 * Cf := by
    rw [hK₁, Real.sq_sqrt]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    split_ifs <;> positivity
  have hK₂sq : K₂ ^ 2 = N * (ρ⁻¹ * (e / ρ) ^ Acl) ^ 2 * εc ^ 2 * θ ^ 2 * Cr := by
    rw [hK₂, Real.sq_sqrt]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    positivity
  have hres := residualNorm_le_of_pointwise ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
    (fun t x k => (if hh = 0 then Fc t x k else 0)
      + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x k)
    (fun t x => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
      εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x)
    (fun t => fluxDensity ρ kres π Fc t) hK₁0 hK₂0 hmeasI
    (fun t ht => by
      rw [hK₁sq]
      have := flux_time_bound (hTime t ht) hh t rfl (hℓτ t) θ rfl hθ0
      rw [← hCf] at this
      exact this)
    (fun t ht => by
      rw [hK₂sq]
      have := rem_time_bound (hTime t ht) t rfl (hℓτ t) θ rfl hθ0
      rw [← hCr] at this
      exact this)
  have hF : classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres Fc =
      (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), fluxDensity ρ kres π Fc t) ^ (1 / 2 : ℝ) := rfl
  have hvol : volume (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) := by
    rw [Real.volume_Icc, show ℓ ^ 2 * t₁ - ℓ ^ 2 * t₀ = ℓ ^ 2 * (t₁ - t₀) by ring,
      ENNReal.ofReal_rpow_of_nonneg hLnn (by norm_num), Real.sqrt_eq_rpow]
  rw [hvol] at hres
  rw [hF]
  generalize (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), fluxDensity ρ kres π Fc t) ^ (1 / 2 : ℝ)
    = F at hres ⊢
  by_cases hgood : hh = 0 ∨ 0 ≤ Θ ^ hh
  · have hΘnn : 0 ≤ Θ ^ hh := by
      rcases hgood with h0 | h0
      · subst h0; simp
      · exact h0
    have hθeq : θ = C₀ * Θ ^ hh := by rw [hθdef, max_eq_left (mul_nonneg hC₀ hΘnn)]
    have hind : (if hh = 0 then (1 : ℝ) else 0) = 0 ∨ (if hh = 0 then (1 : ℝ) else 0) = 1 := by
      split_ifs <;> simp
    have hfin := final_real (ν := ν) (B := B) (ρ := ρ) (e := e) (ℓ := ℓ) (εc := εc)
      (L := ℓ ^ 2 * (t₁ - t₀)) (C₀ := C₀) (Θh := Θ ^ hh) (N := (N : ℝ)) (cf := Cf) (cr := Cr)
      (indr := if hh = 0 then 1 else 0) (A := Acl) hν hB hρ he hset.ℓ_eq hε hC₀ hΘnn
      (Nat.cast_nonneg N) hCf0 hind
    have e1 : (if hh = 0 then (2 : ℝ) else 0) = 2 * (if hh = 0 then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have e2 : (if hh = 0 then (1 : ℝ) else 0) * Real.sqrt (B / ν) =
        if hh = 0 then Real.sqrt (B / ν) else 0 := by split_ifs <;> simp
    refine hres.trans ?_
    rw [hZ]
    have hsum : ENNReal.ofReal (Real.sqrt ν)⁻¹ * ENNReal.ofReal K₁ * F +
        ENNReal.ofReal K₂ * ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) * F =
        ENNReal.ofReal ((Real.sqrt ν)⁻¹ * K₁ + K₂ * Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) * F := by
      rw [← add_mul, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK₂0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [hsum]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    rw [hK₁, hK₂, hθeq, e1]
    rw [e2] at hfin
    exact hfin
  · have hbad := not_or.1 hgood
    have hneg : Θ ^ hh < 0 := not_le.1 hbad.2
    have hθ00 : θ = 0 := by
      rw [hθdef]
      exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hC₀ hneg.le)
    have hK₁z : K₁ = 0 := by
      rw [hK₁, hθ00]; simp [hbad.1]
    have hK₂z : K₂ = 0 := by
      rw [hK₂, hθ00]; simp
    refine hres.trans ?_
    rw [hK₁z, hK₂z]
    simp

end AVRegularity
end
