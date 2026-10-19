-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Assembly
public import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleReference.ChartTestTransport
import Mathlib.Data.Int.Star

section
section
/-! **The window of a weighted pulse** (glued mean, step (i)).

At a context with `1 ≤ Λ`, a pulse whose cutoff weight is nonzero at a time `t` of the observed
window has the cell time `c⁻¹ t` (`c = cellScaleSq`) in the clipped lift window
`[rSeqStart, rSeqEnd]` on which `ReconSeqAt` gives the lift sequence. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

theorem cellScaleSq_pos (hΛ : 1 ≤ A.Λ) : 0 < c.D.cellScaleSq M := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  unfold OCData.cellScaleSq OCData.eps
  rw [hkap]
  exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM

theorem ocEll_sq_eq' (hΛ : 1 ≤ A.Λ) :
    ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 = c.D.cellScaleSq M := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]

theorem ocTau_pos' (hΛ : 1 ≤ A.Λ) : 0 < ocTau c.D.α c.D.q c.D.Λ M := by
  obtain ⟨-, -, hΛD, -⟩ := c.data
  exact Construction.Stream.ocTau_pos (hΛD ▸ hΛ)

theorem window_mem (hΛ : 1 ≤ A.Λ) (k : ℤ) {t : ℝ} (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c))
    (hw : ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0) :
    (c.D.cellScaleSq M)⁻¹ * t ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k) := by
  have hcs := cellScaleSq_pos c hΛ
  have hwin : t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ M k := by
    by_contra hn
    exact hw (WeakEntryProofs.ocCutoff_zero_off_output _ _ _ _ (ocTau_pos' c hΛ) k t hn)
  have hc := ocEll_sq_eq' c hΛ
  unfold rSeqStart rSeqEnd
  rw [hc]
  have e : (c.D.cellScaleSq M)⁻¹ * t * c.D.cellScaleSq M = t := by field_simp
  refine ⟨(div_le_iff₀ hcs).2 ?_, (le_div_iff₀ hcs).2 ?_⟩
  · rw [e]; exact max_le hwin.1 ht.1
  · rw [e]; exact le_min hwin.2 ht.2

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The grade-zero tail** (glued mean, step (i)).

`gradeZeroTailFix`: with the lift sequence of the window (`ReconSeqAt`) and `1 ≤ N_T`,
`1 ≤ Λ`, the degrees `N_T + 2..N_T + D_t` of the grade-zero glued mean flux vanish: each weighted
pulse has `C_n = 0` for `n > N_T`, and the degree `N_T + 2` flux is `-η G ∂_X (C_{N_T} a)` of cell
mean zero (`gradeZero_meanFluxX_zero`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftFluxX_congr_input (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a a' : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (hat : a t = a' t) :
    liftFluxX Q Cc a hh n t = liftFluxX Q Cc a' hh n t := by
  have hl : ∀ m c, liftApply m c a t = liftApply m c a' t := fun m c => by
    unfold liftApply
    rw [hat]
  funext X z k
  simp only [liftFluxX, hl]

/-- The grade-zero pulse flux of degree `≥ N + 2` vanishes. -/
theorem pulseMeanFluxEuler_zero (Q Q' : LiftOperatorData ι h D) (sX sZ : ℕ)
    (t₀ t₁ : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q' sX sZ t₀ t₁ N H Cc) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (hN : 1 ≤ N)
    (c ρ εc : ℝ) (hc : c ≠ 0) (n : ℕ) (hn : N + 2 ≤ n)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (hchart : ContDiff ℝ (⊤ : ℕ∞) (chart t))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) (v : ι) :
    pulseMeanFluxEuler c ρ εc n 0 Q Cc chart label a t x v = 0 := by
  have hdate : c * (c⁻¹ * t) = t := mul_inv_cancel_left₀ hc t
  have ha₀ : ContDiff ℝ (⊤ : ℕ∞) (fun X' => a t (chart t (ρ • X'))) :=
    ha.comp (hchart.comp (contDiff_const_smul ρ))
  funext j
  simp only [pulseMeanFluxEuler]
  refine Finset.sum_eq_zero fun k' _ => ?_
  have hcongr := liftFluxX_congr_input Q Cc
    (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
    (fun _ X' => a t (chart t (ρ • X'))) 0 n (c⁻¹ * t) (by funext X'; simp only [hdate])
  have hz := gradeZero_meanFluxX_zero Q Q' sX sZ t₀ t₁ N H Cc hseq hX hZ hN n hn _ ha₀
    (c⁻¹ * t) ht (ρ⁻¹ • label t x) k'
  rw [hcongr, hz]
  simp

end Generic

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The grade-zero tail** (step (i)) from the lift sequence. -/
theorem gradeZeroTailFix (hΛ : 1 ≤ A.Λ) (x : TermResAux c) (ℓ : ℕ) (CGl Cw' : ℕ → ℝ)
    (Ca Sb Cg : ℝ) : ReconGradeZeroTailFix c x ℓ CGl Cw' Ca Sb Cg := by
  classical
  intro hseq _ hN a ha hper t ht z v
  have hD2 : 2 ≤ A.Dt := le_max_left _ _
  have hcs := cellScaleSq_pos c hΛ
  have hτ := ocTau_pos' c hΛ
  simp only [menuGluedMeanFlux, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkobs := obsPulses_time_subset c.D.α c.D.q c.D.Λ M hτ ht hk
  have hsub : Finset.Icc 2 (A.NT + 1) ⊆ Finset.Icc 2 (A.NT + A.Dt) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  refine (Finset.sum_subset hsub fun n hn hnn => ?_).symm
  simp only [Finset.mem_Icc, not_and, not_le] at hn hnn
  have hnA : A.NT + 2 ≤ n := by omega
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hw : ocCutoff c.D.α c.D.q c.D.Λ M k t = 0
    · simp [hw]
    · have hmem := window_mem c hΛ k ht hw
      have hsk := hseq k hkobs
      rw [pulseMeanFluxEuler_zero _ _ _ _ _ _ _ _ _ hsk (by omega) (by omega) hN _ _ _
        hcs.ne' n hnA _ _ _ _ _ ?_ ?_ hmem v]
      · simp
      · exact ha t
      · exact Providers.QuietAtlas.flowOf_contDiff c.D (M - 1) t (c.D.slotAnchor M k)
  · simp [hodd]

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **One pulse and one degree of the mean flux in chart form** (glued mean, step (i)).

For a flux coefficient `C` with vanishing zero-order term, the applied flux at `z = 0` on the
dilated field `g(ρ ·)` equals, up to the factor `ρ`, the sum over `d ∈ [2, n]` of
`ρ^d` times the chart-frame word terms (`chartFluxTerm`) of the mean coefficient
`b d α t X k = C k (d-1) α t X 0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.ActualMeans
open AVRegularity.CycleComparison.Lift

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The mean coefficient of a family of flux coefficients (fast variable fixed at `0`). -/
def meanOf (C : Fin 2 → LiftCoeff ι h) : MeanCoeff ι h :=
  fun d α t X k₀ => C k₀ (d - 1) α t X 0

theorem liftApply_eq_sum_Icc (n : ℕ) (hn : 2 ≤ n) (C : LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (τ : ℝ) (X : Vec 2)
    (hzero : ∀ (α : DerivativeWord2 0) v u, C 0 α τ X 0 v u = 0) (v : ι) :
    liftApply (n - 1) C (fun _ => f) τ X 0 v =
      ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
        C (d - 1) α τ X 0 v u (orderedDerivative α f X u) := by
  classical
  have hn' : n - 1 + 1 = n := by omega
  have hz : (∑ α : DerivativeWord2 0, ∑ u : ι,
      C 0 α τ X 0 v u (orderedDerivative α f X u)) = 0 := by
    simp [hzero]
  have hs := sum_range_zero_order_shift n (by omega)
    (fun m => ∑ α : DerivativeWord2 m, ∑ u : ι, C m α τ X 0 v u (orderedDerivative α f X u)) hz
  simpa only [liftApply, hn'] using hs

/-- The applied flux on the dilated field, in chart form. -/
theorem dilated_flux_sum (ρ : ℝ) (hρ : ρ ≠ 0) (n : ℕ) (hn : 2 ≤ n)
    (C : Fin 2 → LiftCoeff ι h) (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (τ : ℝ)
    (X : Vec 2) (hzero : ∀ l (α : DerivativeWord2 0) v u, C l 0 α τ X 0 v u = 0) (l : Fin 2)
    (v : ι) :
    ρ • liftApply (n - 1) (C l) (fun _ => fun X' => g (ρ • X')) τ X 0 v =
      ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chartFluxTerm ρ (meanOf C) g τ d α l (ρ • X) v := by
  rw [liftApply_eq_sum_Icc n hn (C l) _ τ X (hzero l) v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := by have := Finset.mem_Icc.1 hd; omega
  have hpow : ρ * ρ ^ (d - 1) = ρ ^ d := by rw [← pow_succ']; congr 1; omega
  have hterm : ∀ α : DerivativeWord2 (d - 1), ∑ u : ι, C l (d - 1) α τ X 0 v u
      (orderedDerivative α (fun X' => g (ρ • X')) X u) =
      ρ ^ (d - 1) • chartFluxTerm ρ (meanOf C) g τ d α l (ρ • X) v := fun α =>
    congrFun (congrFun (dilated_flux_eq ρ hρ (meanOf C) g hg τ d α l) X) v
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hterm α, smul_smul, hpow]

omit [Fintype ι] in
theorem liftFluxX_congr_data [Fintype ι] {D : ℕ} (Q Q' : LiftOperatorData ι h D)
    (hη : Q.η = Q'.η) (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ)
    {t : ℝ} (hag : Seq.SeqAgreeAt Q Q' t) :
    liftFluxX Q Cc a hh n t = liftFluxX Q' Cc a hh n t := by
  obtain ⟨η, G, v, e⟩ := Q
  obtain ⟨η', G', v', e'⟩ := Q'
  simp only at hη
  subst hη
  obtain ⟨hG, hv, he⟩ := hag
  dsimp only at hG hv he
  have hGf : ∀ X, G t X = G' t X := fun X => congrFun hG X
  have hvf : ∀ z, v t z = v' t z := fun z => congrFun hv z
  have he' : ∀ ε Φ k, sourceFlux e η ε t Φ k = sourceFlux e' η ε t Φ k := he
  funext X z k
  simp only [liftFluxX, he', hGf, hvf]

/-- **One pulse, one degree, one grade of the Eulerian mean flux in chart form.** -/
theorem pulseMeanFluxEuler_eq {D : ℕ} (Q Q' : LiftOperatorData ι h D)
    (hη : Q.η = Q'.η) (Cc : ℕ → ℕ → LiftCoeff ι h) (r n : ℕ) (hn : 2 ≤ n)
    (C : Fin 2 → LiftCoeff ι h) (c ρ εc : ℝ) (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (y : Vec 2)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (hchart : ContDiff ℝ (⊤ : ℕ∞) (chart t))
    (hag : Seq.SeqAgreeAt Q Q' (c⁻¹ * t))
    (hzero : ∀ l (α : DerivativeWord2 0) v u, C l 0 α (c⁻¹ * t) (ρ⁻¹ • label t y) 0 v u = 0)
    (hid : ∀ (l : Fin 2) (v : ι), liftApply (n - 1) (C l)
        (fun _ => fun X' => a t (chart t (ρ • X'))) (c⁻¹ * t) (ρ⁻¹ • label t y) 0 v =
      fieldCellMean (fun z => liftFluxX Q' Cc
        (fun _ => fun X' => a t (chart t (ρ • X'))) r n (c⁻¹ * t) (ρ⁻¹ • label t y) z l) v)
    (v : ι) (j : Fin 2) :
    pulseMeanFluxEuler c ρ εc n r Q Cc chart label a t y v j =
      -((c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix (chart t) (label t y) j l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          chartFluxTerm ρ (meanOf C) (fun y' => a t (chart t y')) (c⁻¹ * t) d α l
            (label t y) v) := by
  have hdate : c * (c⁻¹ * t) = t := mul_inv_cancel_left₀ hc t
  have hρX : ρ • (ρ⁻¹ • label t y) = label t y := smul_inv_smul₀ hρ _
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y' => a t (chart t y')) := ha.comp hchart
  simp only [pulseMeanFluxEuler]
  have hcongr := liftFluxX_congr_input Q' Cc
    (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
    (fun _ X' => a t (chart t (ρ • X'))) r n (c⁻¹ * t) (by funext X'; simp only [hdate])
  rw [liftFluxX_congr_data Q Q' hη Cc _ r n hag, hcongr]
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs := dilated_flux_sum ρ hρ n hn C (fun y' => a t (chart t y')) hg (c⁻¹ * t)
    (ρ⁻¹ • label t y) (hzero) l v
  rw [hρX] at hs
  rw [← hs, ← hid l v]
  module

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The mean-flux coefficients of a pulse at any grade** (glued mean, step (i)).

`coreMeanFluxCoeff Q Cc r n` is the diagonal mean-flux coefficient at grade `0` and the positive one at
grades `r ≥ 1`. At a lift setting with a lift sequence it has vanishing zero-order term, a `C¹`
mean coefficient, presents the lift mean in divergence form, and applied at `z = 0` is the cell mean
of the slow lift flux. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι (fun _ => ℝ) D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

/-- The mean-flux coefficients of grade `r` and degree `n`. -/
def coreMeanFluxCoeff (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (r n : ℕ) : Fin 2 → LiftCoeff ι (fun _ => ℝ) :=
  fun l => if r = 0 then diagonalMeanFluxCoefficient Q Cc n l
    else positiveMeanFluxCoefficient Q Cc r n l

theorem Cfl_zero_eq (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (n : ℕ) :
    coreMeanFluxCoeff Q Cc 0 n = diagonalMeanFluxCoefficient Q Cc n := by
  funext l; simp [coreMeanFluxCoeff]

theorem Cfl_pos_eq (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (r n : ℕ) (hr : r ≠ 0) :
    coreMeanFluxCoeff Q Cc r n = positiveMeanFluxCoefficient Q Cc r n := by
  funext l; simp [coreMeanFluxCoeff, hr]

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem Cfl_zero_order (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (l : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (α : DerivativeWord2 0)
    (X z : Vec 2) (v u : ι) : coreMeanFluxCoeff Q Cc r n l 0 α t X z v u = 0 := by
  by_cases hr : r = 0
  · simp only [coreMeanFluxCoeff, hr, ite_true]
    exact setting_diagonal_mean_flux_coefficient_zero_order P sX sZ Cc hseq n hn l t ht α X z v u
  · simp only [coreMeanFluxCoeff, hr, ite_false]
    exact setting_positive_mean_flux_coefficient_zero_order P sX sZ hsZ Cc hseq 0
      (by have := P.qs_eq; nlinarith [P.N_ge, P.D_ge]) r (Nat.pos_of_ne_zero hr) hrH n hn hnR
      l t ht α X z v u

include P in
theorem Cfl_pres (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) r n t X =
      meanApply n (meanOf (coreMeanFluxCoeff Q Cc r n)) (fun _ => f) t X := by
  have hres : 0 + (N + D) ≤ qs := by
    rw [P.qs_eq]
    nlinarith [P.N_ge, P.D_ge, Nat.zero_le K, Nat.zero_le H, sq_nonneg (N + D)]
  by_cases hr : r = 0
  · subst hr
    have := setting_diagonal_mean_flux_meanApply P sX sZ hX hZ Cc hseq 0 hres n hn hnR f hf t ht X
    rw [Cfl_zero_eq]; exact this
  · have := setting_positive_mean_flux_meanApply P sX sZ hX hZ Cc hseq 0 hres r
      (Nat.pos_of_ne_zero hr) hrH n hn hnR f hf t ht X
    rw [Cfl_pos_eq _ _ _ hr]; exact this

include P in
theorem Cfl_contDiff (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n) (α : DerivativeWord2 (d - 1))
    (l : Fin 2) (v u : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ 1 (fun X => meanOf (coreMeanFluxCoeff Q Cc r n) d α t X l v u) := by
  have hres : 0 + (N + D) ≤ qs := by
    rw [P.qs_eq]
    nlinarith [P.N_ge, P.D_ge, Nat.zero_le K, Nat.zero_le H, sq_nonneg (N + D)]
  by_cases hr : r = 0
  · have := setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq 0 hres n hn
      hnR l t ht (d - 1) (by omega) α 0 v u
    rw [hr, Cfl_zero_eq]
    have h1 := this
    simp only [Nat.zero_add, Nat.cast_one] at h1
    exact h1
  · have := setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq 0 hres r
      (Nat.pos_of_ne_zero hr) hrH n hn hnR l t ht (d - 1) (by omega) α 0 v u
    rw [Cfl_pos_eq _ _ _ hr]
    have h1 := this
    simp only [Nat.zero_add, Nat.cast_one] at h1
    exact h1

include P in
theorem Cfl_hid (sX sZ : ℕ) (hX : D ≤ sX) (hZ : D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) (v : ι) :
    liftApply (n - 1) (coreMeanFluxCoeff Q Cc r n l) (fun _ => f) t X 0 v =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) r n t X z l) v := by
  have hD2 := P.D_ge
  by_cases hr : r = 0
  · subst hr
    simp only [coreMeanFluxCoeff, ite_true]
    exact congrFun (diag_cellMean_liftFluxX_eq P sX sZ (by omega) (by omega) Cc hseq n hn f
      hf l t ht X 0) v
  · simp only [coreMeanFluxCoeff, hr, ite_false]
    exact cellMean_liftFluxX_eq P sX sZ hX hZ Cc hseq r (Nat.pos_of_ne_zero hr) hrH n hn
      f hf l t ht X 0 v

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! **The pulse flux of the menu is minus the Piola transport of the chart flux** (glued mean, step (i)).

For an observed pulse `k` with nonzero weight at a time `t` of the window, the pulse term of the
menu's glued mean flux (grade `r ≤ d_W`, degrees `2..N_T + D_t`) is minus `eulerFlux` of the mean
coefficients `meanOf (coreMeanFluxCoeff …)`, the lift data of the menu being those of the window
(`seq_agree`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.ActualMeans

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- The chart of the pulse `k` in the form of the menu. -/
abbrev chart' (k : ℤ) : ℝ → Vec 2 → Vec 2 :=
  fun s' y => c.D.flowOf (M - 1) s' y (c.D.slotAnchor M k)

/-- The label of the pulse `k` in the form of the menu. -/
abbrev label' (k : ℤ) : ℝ → Vec 2 → Vec 2 :=
  fun s' y => c.D.flowOf (M - 1) (c.D.slotAnchor M k) y s'

/-- The pulse term of the menu's glued mean flux of grade `r` (without its weight). -/
def corePulseFlux (r : ℕ) (a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (k : ℤ) (t : ℝ)
    (z : Vec 2) (v : CompIn c.Gw.comps) : Fin 2 → ScalarH v.1.root :=
  ∑ n ∈ Finset.Icc 2 (A.NT + A.Dt),
    if hk : Odd k then
      pulseMeanFluxEuler (c.D.cellScaleSq M) (liftLength c.D M)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M) n r
        (familyLiftData c.D M k (nativeChain M k) (liftLength c.D M)
          (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))) (c.CcT k)
        (chart' c k) (label' c k) a t z v
    else 0

theorem liftLength_ne_zero (hΛ : 1 ≤ A.Λ) : liftLength c.D M ≠ 0 := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM1 : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch (Nat.sub_le M 1)
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  exact (Real.sqrt_pos.2 (mul_pos hκM1 hτ'')).ne'

theorem mem_pulseWindow (hΛ : 1 ≤ A.Λ) (k : ℤ) {t : ℝ}
    (hw : ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0) :
    t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ M k := by
  by_contra hn
  exact hw (WeakEntryProofs.ocCutoff_zero_off_output _ _ _ _ (ocTau_pos' c hΛ) k t hn)

/-- **The pulse flux of the menu is minus the Piola transport of the chart flux.** -/
theorem pulse_PF_eq (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hcr : cr = 1) (hN : 1 ≤ A.NT)
    (ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ)
    (hbody : ReconSettingBody c ℓ CGl Cw' Ca Sb Cg qs qf par V bM) (hseq : ReconSeqAt c ℓ)
    (r : ℕ) (hr : r ≤ A.dW) (a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root)
    (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) {t : ℝ} (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c))
    {k : ℤ} (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (hw : ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0) (v : CompIn c.Gw.comps) (y : Vec 2) (j : Fin 2) :
    corePulseFlux c r a k t y v j =
      -eulerFlux (c.D.cellScaleSq M) (liftLength c.D M)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M) (A.NT + A.Dt)
        (chart' c k t) (label' c k t)
        (fun n => meanOf (coreMeanFluxCoeff (rLiftData c k) (c.CcT k) r n))
        (fun y' => a t (chart' c k t y')) ((c.D.cellScaleSq M)⁻¹ * t) v y j := by
  classical
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  have hcs := cellScaleSq_pos c hΛ
  have hmem := window_mem c hΛ k ht hw
  have hwin := mem_pulseWindow c hΛ k hw
  have hρ0 := liftLength_ne_zero c hΛ
  have hP := hbody.1 k hk
  have hsk := hseq k hk
  obtain ⟨hη, hag⟩ := Seq.seq_agree c hcr hΛ hM hodd
  have hag' := hag ((c.D.cellScaleSq M)⁻¹ * t) (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hQ : familyLiftData c.D M k (nativeChain M k) (liftLength c.D M)
      (c.Gw.fam.fiber ⟨k, hodd⟩ (c.Gw.actual ⟨k, hodd⟩)) = Seq.seqQ c k hodd := by
    simp only [Seq.seqQ, hcr, one_mul]
  have hD : A.Dt ≤ rKlift A ℓ + A.Dt + 2 := by omega
  have hD' : A.Dt ≤ max (rLlift A ℓ + 1) (rLlift A ℓ + 2) := by
    have h1 : A.Dt * 1 * 1 ≤ A.Dt * (A.dW + 1) * A.NT := by gcongr; omega
    refine le_trans ?_ (le_max_right _ _)
    unfold rLlift
    omega
  have h2X : 2 ≤ rKlift A ℓ + A.Dt + 2 := by omega
  have h2Z : 2 ≤ max (rLlift A ℓ + 1) (rLlift A ℓ + 2) :=
    le_trans (by unfold rLlift; omega) (le_max_right _ _)
  unfold corePulseFlux
  simp only [hodd, dite_true]
  rw [Finset.sum_apply, eulerFlux_eq, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.1 hn
  rw [hQ]
  rw [pulseMeanFluxEuler_eq (Seq.seqQ c k hodd) (rLiftData c k) hη (c.CcT k) r n hn'.1
    (coreMeanFluxCoeff (rLiftData c k) (c.CcT k) r n) (c.D.cellScaleSq M) (liftLength c.D M)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M) hcs.ne' hρ0
    (chart' c k) (label' c k) a t y (ha t)
    (Providers.QuietAtlas.flowOf_contDiff c.D (M - 1) t (c.D.slotAnchor M k)) ?_ ?_ ?_ v j]
  · rfl
  · exact hag'
  · intro l α v' u
    exact Cfl_zero_order hP _ _ (by omega) (c.CcT k) hsk r hr n hn'.1 (by omega) l _ hmem
      α _ _ v' u
  · intro l v'
    exact Cfl_hid hP _ _ hD hD' (c.CcT k) hsk r hr n hn'.1 _
      ((ha t).comp ((Providers.QuietAtlas.flowOf_contDiff c.D (M - 1) t
        (c.D.slotAnchor M k)).comp (contDiff_const_smul (liftLength c.D M)))) l _ hmem _ v'

/-- The weights of the family are the cutoffs on the odd slots, at the stage of a context. -/
theorem weight_eq' (k : ℤ) (hk : Odd k) (t : ℝ) :
    c.Gw.actualFamily.weight (oddSlotOf k) t = ocCutoff c.D.α c.D.q c.D.Λ M k t := by
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hnat : c.Gw.IsNatural (M + A.Jw) := c.weak.2.2.2.2.2.2.2.2.2.1
  rw [oddSlotOf_of_odd hk]
  have h1 := hnat.2.1 ⟨k, hk⟩ t
  exact h1.trans (by rw [hlev])

/-- **The glued mean flux of the menu as a weighted sum of pulse fluxes.** -/
theorem gluedMeanFlux_eq (hΛ : 1 ≤ A.Λ) (r : ℕ)
    (a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) {t : ℝ}
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (z : Vec 2) (v : CompIn c.Gw.comps) :
    gluedMeanFlux c.Gw M {r} (Finset.Icc 2 (A.NT + A.Dt)) c.CcT a t z v =
      ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
        c.Gw.actualFamily.weight (oddSlotOf k) t • corePulseFlux c r a k t z v := by
  classical
  have hτ := ocTau_pos' c hΛ
  unfold gluedMeanFlux
  simp only [Finset.sum_singleton]
  have h1 : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M t t,
      (∑ n ∈ Finset.Icc 2 (A.NT + A.Dt),
        if hk : Odd k then
          ocCutoff c.D.α c.D.q c.D.Λ M k t • pulseMeanFluxEuler (c.D.cellScaleSq M)
            (liftLength c.D M)
            (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M) n r
            (familyLiftData c.D M k (nativeChain M k) (liftLength c.D M)
              (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))) (c.CcT k)
            (chart' c k) (label' c k) a t z v
        else 0) =
      ocCutoff c.D.α c.D.q c.D.Λ M k t • corePulseFlux c r a k t z v := by
    intro k _
    unfold corePulseFlux
    by_cases hodd : Odd k
    · simp only [hodd, dite_true, Finset.smul_sum]
    · simp [hodd]
  rw [Finset.sum_congr rfl h1]
  have hsub := obsPulses_time_subset c.D.α c.D.q c.D.Λ M hτ ht
  rw [Finset.sum_subset hsub fun k hk hnk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [weight_eq' c k (CycleComparison.LiftSetting.obsPulse_odd hk) t]
  · have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
    have hout : t ∉ ocPulseWindow c.D.α c.D.q c.D.Λ M k := fun hin =>
      hnk (mem_obsPulses_time c.D.α c.D.q c.D.Λ M hτ hodd hin)
    rw [WeakEntryProofs.ocCutoff_zero_off_output c.D.α c.D.q c.D.Λ M hτ k t hout, zero_smul]

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The glued mean core** (step (i)).

`gluedMeanCoreFix`: at a context with `1 ≤ Λ`, `1 ≤ M`, `1 ≤ N_T`, from the lift sequences of
the window and the lift settings, for every grade `r ≤ d_W`, the glued mean of the
window's pulse lifts is minus the Eulerian divergence of the glued mean flux of the menu. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.ActualMeans

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

theorem gluedMeanCoreFix (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT) (x : TermResAux c)
    (ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ) (r : ℕ) (hr : r ≤ A.dW) :
    ReconGluedMeanCoreFix c x ℓ CGl Cw' Ca Sb Cg r := by
  classical
  intro hseq hset hcr a ha hper t ht y v
  obtain ⟨qs, qf, par, V, bM, hbody⟩ := hset
  have hcs := cellScaleSq_pos c hΛ
  have hc := ocEll_sq_eq' c hΛ
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := by
    obtain ⟨-, -, hΛD, -⟩ := c.data
    exact Construction.Stream.ocTauPP_pos (hΛD ▸ hΛ)
  have hlen : (A.Mt M sXT sZT c.tp cr).lenFactor = 1 := hcr
  have hchart : ∀ k : ℤ, ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) = chart' c k := by
    intro k
    funext s' y
    show _ = c.D.flowOf (M - 1) s' y (c.D.slotAnchor M k)
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ'']
  have hinv : ∀ k : ℤ, ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) = label' c k := by
    intro k
    funext s' y
    show _ = c.D.flowOf (M - 1) (c.D.slotAnchor M k) y s'
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ'']
  have hrhs : (fun z => menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {r}
      (Finset.Icc 2 (A.NT + A.Dt)) c.CcT a t z v) = fun z =>
      ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
        c.Gw.actualFamily.weight (oddSlotOf k) t • corePulseFlux c r a k t z v := by
    funext z
    rw [menuGluedMeanFlux_cascade _ hlen]
    exact gluedMeanFlux_eq c hΛ r a ht z v
  have h2X : 2 ≤ rKlift A ℓ + A.Dt + 2 := by omega
  have h2Z : 2 ≤ max (rLlift A ℓ + 1) (rLlift A ℓ + 2) :=
    le_trans (by unfold rLlift; omega) (le_max_right _ _)
  rw [hrhs]
  simp only [hchart, hinv, hc]
  refine gluedMean_eq_neg_div _ _ (c.D.cellScaleSq M) (rRho c) _ hcs.ne'
    (liftLength_ne_zero c hΛ) A.NT r (fun k => rLiftData c k) c.CcT (chart' c)
    (label' c) (fun k => rSeqStart c k) (fun k => rSeqEnd c k)
    (fun k r' n => meanOf (coreMeanFluxCoeff (rLiftData c k) (c.CcT k) r' n)) a t (ha t)
    (fun k t z v => corePulseFlux c r a k t z v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y v
  · intro k hk hne
    refine window_mem c hΛ k ht ?_
    rwa [weight_eq' c k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hne
  · intro k _ y'
    exact Construction.Preservation.Residual.FluxCancellation.flowOf_inv c.D (M - 1) _ _ y'
  · intro k _ x'
    exact Construction.Preservation.Residual.FluxCancellation.flowOf_inv c.D (M - 1) _ _ x'
  · intro k _ y'
    exact Providers.QuietAtlas.flowOf_det c.D (M - 1) t _ y'
  · intro k _
    exact Providers.QuietAtlas.flowOf_contDiff c.D (M - 1) t _
  · intro k _
    exact (Providers.QuietAtlas.flowOf_contDiff c.D (M - 1) _ t).differentiable (by simp)
  · intro k hk n hn hnM a₀ ha₀ s hs X'
    exact Cfl_pres (hbody.1 k hk) _ _ h2X h2Z (c.CcT k) (hseq k hk) r hr n hn hnM a₀ ha₀ s
      hs X'
  · intro k hk n hn hnM d hd hdn α k₀ v' u s hs
    exact Cfl_contDiff (hbody.1 k hk) _ _ (le_trans (by omega) h2Z) (c.CcT k) (hseq k hk)
      r hr n hn hnM d hd hdn α k₀ v' u s hs
  · intro k hk hne v' y' j
    refine pulse_PF_eq c hΛ hM hcr hN ℓ CGl Cw' Ca Sb Cg qs qf par V bM hbody hseq r hr a ha
      ht hk ?_ v' y' j
    rwa [weight_eq' c k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hne

/-- **Step (i) of the conversion at a context**, from the lift sequences and the lift settings:
`ReconGluedMeanAt c r` for every grade `r ≤ d_W`. -/
theorem reconGluedMeanAt_all (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (x : TermResAux c) (ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ) (hseq : ReconSeqAt c ℓ)
    (hset : ReconSettingAt c x ℓ CGl Cw' Ca Sb Cg) :
    ∀ r ∈ Finset.range (A.dW + 1), ReconGluedMeanAt c r := fun r hr =>
  reconGluedMeanFix_of_core c r
    (gluedMeanCoreFix c hΛ hM hN x ℓ CGl Cw' Ca Sb Cg r (by
      have := Finset.mem_range.1 hr; omega) hseq hset)
    (gradeZeroTailFix c hΛ x ℓ CGl Cw' Ca Sb Cg hseq hset) x.one hN

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii), split**.

`ReconMacroSwapAt` follows from three named statements and the torus integration by parts
(`torus_ibp`):
- `ReconMacroFluxReg`: the menu's macro flux on `aRep` is `C¹` and `ℤ²`-periodic in the position;
- `ReconLettersFluxRegCl`: the same for the classical letters' flux;
- `ReconMacroDivEqCl`: the divergences agree at every point, from `IsMeanPresentation` and (i) (the
  divergences at `x` depend on finitely many derivatives of the field at `x`; replace the
  field by a smooth one with the same jets, `smoothJetRealization`, and use the smooth
  presentation).

Degenerate cases:
- `a = 0`: both fluxes vanish.
- Equal fluxes: the divergence statement is trivial. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section MacroSwap

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **Regularity of the macro flux**: `C¹` and periodic in the position at every
time of the window (`aRep` is `C^{K̂ - 2p_T}`, `menuGluedMeanFlux_contDiff`). -/
def ReconMacroFluxReg : Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c),
    (∀ k : Fin 2, ContDiff ℝ 1 (fun y => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW
      c.CcT c.aRep v s y k)) ∧
    (∀ k : Fin 2, IsZ2Periodic (fun y => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW
      c.CcT c.aRep v s y k))

end MacroSwap

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii): classical letters flux**.

`AVRegularity.coarseDefectFlux` reads the jets of `reconW` through `torusJetOrder`, an arbitrary
representative of the Sobolev jet: it equals the derivatives of `aRep` only almost everywhere on
the cell (`ReconJetsAt`), so the regularity of the letters' flux and the equality of the
divergences cannot hold pointwise for it. They are stated for the same flux with the classical
jets of `aRep` (`ClassicalDefectFlux`, the shape of `IsMeanPresentation`'s `classicalGradeFlux`):
`ReconLettersFluxRegCl`, `ReconMacroDivEqCl`, with the almost-everywhere congruence of the
pairings (`pairing_ae_eq`); `reconMacroSwapAt_of_classical_steps` is the assembly.

Degenerate cases: `a = 0` (the classical flux vanishes); a smooth `a` (the jets agree
everywhere). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The coarse defect flux with the classical jets of a field `a` in place of the torus jets of a
Sobolev field (the same formula as `AVRegularity.coarseDefectFlux`). -/
def ClassicalDefectFlux (B : ℝ) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i)
    (v : ι) (s : ℝ) (x : Vec 2) (k : Fin 2) : h v :=
  (∑ l : Fin 2, (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) •
      orderedDerivative (fun _ : Fin 1 => l) (fun y => a s y v) x)
    + (∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
          orderedDerivative α (fun y => a s y v) x)
    + (∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a s y u) x)) k)

/-- Pointwise: where the torus jets of `W` at time `s` are the classical jets of `a`, the two
fluxes agree. -/
theorem coarseFlux_eq_classical (B : ℝ) (D H : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ) (x : Vec 2)
    (hj : ∀ u : ι, ∀ m : ℕ, ∀ w : DerivativeWord2 m, m ≤ D →
      torusJetOrder (W u s) m w x = orderedDerivative w (fun y => a s y u) x) (k : Fin 2) :
    AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k =
      ClassicalDefectFlux B D H AD CE Jm a v s x k := by
  unfold AVRegularity.coarseDefectFlux ClassicalDefectFlux
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun l _ => by rw [hj v 1 (fun _ => l) hD]
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
    rw [hj v (d.1 - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega)]
  · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun d _ => ?_
    have : (fun α : DerivativeWord2 (d.1 - 1) => torusJetOrder (W u s) (d.1 - 1) α x) =
        fun α => orderedDerivative α (fun y => a s y u) x :=
      funext fun α => hj u (d.1 - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega)
    rw [this]

/-- Almost everywhere on the cell: if the torus jets of `W` at time `s` are a.e. the classical
jets of `a` up to order `D`, the pairings of the two fluxes against any test agree a.e. -/
theorem pairing_ae_eq (B : ℝ) (D H : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ) (φ : Vec 2 → h v)
    (hj : ∀ u : ι, ∀ m : ℕ, ∀ w : DerivativeWord2 m, m ≤ D →
      torusJetOrder (W u s) m w =ᵐ[volume.restrict unitCube]
        fun x => orderedDerivative w (fun y => a s y u) x) :
    (fun y => ∑ k : Fin 2, inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s y k)
        (gradE φ y k)) =ᵐ[volume.restrict unitCube]
      fun y => ∑ k : Fin 2, inner ℝ (ClassicalDefectFlux B D H AD CE Jm a v s y k)
        (gradE φ y k) := by
  have hall : ∀ᵐ x ∂(volume.restrict unitCube), ∀ u : ι, ∀ m : ℕ, ∀ w : DerivativeWord2 m,
      m ≤ D → torusJetOrder (W u s) m w x = orderedDerivative w (fun y => a s y u) x := by
    refine ae_all_iff.2 fun u => ae_all_iff.2 fun m => ae_all_iff.2 fun w => ?_
    by_cases hm : m ≤ D
    · exact (hj u m w hm).mono fun x hx _ => hx
    · exact ae_of_all _ fun x hmm => absurd hmm hm
  refine hall.mono fun x hx => ?_
  exact Finset.sum_congr rfl fun k _ => by
    rw [coarseFlux_eq_classical B D H hD AD CE Jm W a v s x hx k]

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **Regularity of the classical letters' flux**: `C¹` and
periodic in the position, for the jets of `aRep`. -/
def ReconLettersFluxRegCl
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) : Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c),
    (∀ k : Fin 2, ContDiff ℝ 1 (fun y => ClassicalDefectFlux (c.D.κ (M - 1))
      (A.NT + A.Dt) A.dW AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) c.aRep v s y k)) ∧
    (∀ k : Fin 2, IsZ2Periodic (fun y => ClassicalDefectFlux (c.D.κ (M - 1))
      (A.NT + A.Dt) A.dW AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) c.aRep v s y k))

/-- **The divergences agree, classical form**. -/
def ReconMacroDivEqCl (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT) : Prop :=
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc →
    (∀ r ∈ Finset.range (A.dW + 1), ReconGluedMeanAt c r) → ReconJetsAt c kc hW hf →
    ∀ v : CompIn c.Gw.comps, ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ x : Vec 2,
      divE (fun y k => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep v s y k)
          x =
        divE (fun y k => ClassicalDefectFlux (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW AD CE
          (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) c.aRep v s y k) x

/-- **(ii) from the classical steps.** -/
theorem reconMacroSwapAt_of_classical_steps (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (hM : ReconMacroFluxReg c)
    (hL : ∀ (aC B₀C lamC : ℝ)
      (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
      (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
      ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc → ReconLettersFluxRegCl c AD CE)
    (hDiv : ReconMacroDivEqCl c kc hW hf) :
    ReconMacroSwapAt c kc hW hf := by
  intro aC B₀C lamC AD CE Aedge Cstar Θc hlet hG hJ v s hs φ hφ hper
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hs' : s ∈ Set.Icc c.tp (c.a + A.T₀) := by
    rwa [show c.tp + rTobs c = c.a + A.T₀ by simp [rTobs]] at hs
  have hD : 1 ≤ A.NT + A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  obtain ⟨hMc, hMp⟩ := hM v s hs
  obtain ⟨hLc, hLp⟩ := hL aC B₀C lamC AD CE Aedge Cstar Θc hlet v s hs
  have hd := funext (hDiv aC B₀C lamC AD CE Aedge Cstar Θc hlet hG hJ v s hs)
  have e1 := torus_ibp _ φ hMc hMp hφ1 hper
  have e2 := torus_ibp _ φ hLc hLp hφ1 hper
  rw [hd] at e1
  have hae := pairing_ae_eq (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW hD AD CE
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (reconW c kc hW) c.aRep v s φ
    (fun u m w hm => (hJ.1 u s hs').2.2.2 m hm w)
  exact ⟨pairing_integrable _ φ hMc hφ1,
    (integrable_congr hae).2 (pairing_integrable _ φ hLc hφ1),
    (e1.trans e2.symm).trans (integral_congr_ae hae).symm⟩

end Terminal

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii): regularity of the classical letters' flux**
(`ReconLettersFluxRegCl`).

`ClassicalDefectFlux` is a finite sum of terms `coefficient(y) · jet(a)(y)` where the
coefficients `AD`, `CE` are smooth and periodic (`IsCoarseSetting`) and the jets of the periodic
`C^D` field `a` have order at most `D - 1`, `D = N_T + D_t`.

Degenerate cases: `a = 0`; `AD = CE = 0` (only the `(J - B)∇a` term). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The classical flux is `C¹` in the position.** -/
theorem classicalFlux_contDiff (B : ℝ) (D H : ℕ) (hD : 2 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ)
    (ha : ∀ u, ContDiff ℝ (D : ℕ∞) (fun y => a s y u))
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s)) (k : Fin 2) :
    ContDiff ℝ 1 (fun y => ClassicalDefectFlux B D H AD CE Jm a v s y k) := by
  unfold ClassicalDefectFlux
  refine ((ContDiff.sum fun l _ => ContDiff.smul contDiff_const ?_).add
    (ContDiff.sum fun d _ => ContDiff.sum fun α _ => ContDiff.smul ?_ ?_)).add
    (ContDiff.sum fun r hr => ContDiff.sum fun u _ => ContDiff.sum fun d _ => ?_)
  · exact AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff _ 1 _
      ((ha v).of_le (by exact_mod_cast (by omega : 1 + 1 ≤ D)))
  · exact ((contDiff_piLp 2).1 (((hAD d).clm_apply contDiff_const : ContDiff ℝ 1 fun x =>
      AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ)))))) k
  · exact AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff _ 1 _
      ((ha v).of_le (by have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega :
        1 + (d.1 - 1) ≤ D)))
  · refine (contDiff_piLp 2).1 ((hCE r hr v u d).clm_apply ?_) k
    refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun α => ?_)
    exact AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff _ 1 _
      ((ha u).of_le (by have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega :
        1 + (d.1 - 1) ≤ D)))

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The classical flux is periodic in the position.** -/
theorem classicalFlux_periodic (B : ℝ) (D H : ℕ) (hD : 2 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ)
    (ha : ∀ u, ContDiff ℝ (D : ℕ∞) (fun y => a s y u))
    (hap : ∀ u, IsZ2Periodic (fun y => a s y u))
    (hAD : ∀ d, IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, IsZ2Periodic (CE r v u d s)) (k : Fin 2) :
    IsZ2Periodic (fun y => ClassicalDefectFlux B D H AD CE Jm a v s y k) := by
  have hper : ∀ u (m : ℕ) (w : DerivativeWord2 m), m ≤ D →
      IsZ2Periodic (orderedDerivative w (fun y => a s y u)) := fun u m w hm =>
    AVRegularity.CycleComparison.Lift.orderedDerivative_periodic w _
      ((ha u).of_le (by exact_mod_cast hm)) (hap u)
  intro n x
  unfold ClassicalDefectFlux
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun l _ => by rw [hper v 1 _ (by omega) n x]
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
    rw [hAD d n x, hper v (d.1 - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega) n x]
  · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun d _ => ?_
    have : (fun α : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative α (fun y => a s y u) (x + latticeShift n)) =
        fun α => orderedDerivative α (fun y => a s y u) x :=
      funext fun α => hper u (d.1 - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega) n x
    rw [hCE r hr v u d n x, this]

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **`ReconLettersFluxRegCl` at a terminal context**, from the coarse setting of the letters
(`AD`, `CE` smooth and periodic) and the regularity of `aRep`. -/
theorem reconLettersFluxRegCl (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc) :
    ReconLettersFluxRegCl c AD CE := by
  have hset := hlet.1
  have hD : 2 ≤ A.NT + A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  have hN : 1 ≤ kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4) := by
    have : 0 < (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4) := by positivity
    omega
  intro v s hs
  have hs' : s ∈ Set.Icc c.tp (c.a + A.T₀) := by
    rwa [show c.tp + rTobs c = c.a + A.T₀ by simp [rTobs]] at hs
  have hrep : ∀ w, ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (fun y => c.aRep s y w) ∧
      IsZ2Periodic (fun y => c.aRep s y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (c.lift.2.1 w s hs').2
    exact ⟨(by exact_mod_cast hd : ContDiff ℝ ((A.Khat Kout - 2 * A.pT : ℕ) : ℕ∞) _).of_le
      (by exact_mod_cast (by omega : A.NT + A.Dt ≤ A.Khat Kout - 2 * A.pT)), hp⟩
  have hADs : ∀ d, ContDiff ℝ 1 (AD d s) := fun d =>
    (hset.AD_smooth d s hs).of_le (by exact_mod_cast hN)
  have hCEs : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, ContDiff ℝ 1 (CE r v u d s) := fun r hr v u d =>
    (hset.CE_smooth r hr v u d s hs).of_le (by exact_mod_cast hN)
  exact ⟨fun k => classicalFlux_contDiff _ _ _ hD AD CE _ c.aRep v s
      (fun u => (hrep u).1) hADs hCEs k,
    fun k => classicalFlux_periodic _ _ _ hD AD CE _ c.aRep v s (fun u => (hrep u).1)
      (fun u => (hrep u).2) (fun d => hset.AD_per d s hs)
      (fun r hr v u d => hset.CE_per r hr v u d s hs) k⟩

end Terminal

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
