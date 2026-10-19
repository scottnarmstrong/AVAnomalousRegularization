-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredConstantsWindow
import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching
public import AVRegularity.Proofs.GenSem.First.Identity
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.Pieces
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.WeakGen.WeakStageHistory

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The first-source-flux step, the per-pulse identity: the grade-zero label flux under a change of chain.

The grade-zero lifts `Cc0 k A` (`IsDiagLifts`) are global lift sequences of the edgeless scalar
family on `A`, so both statements hold at every label, not only as germs:

* `fsd_diagLabelFlux_eq_of_histEq`: two admissible chains with the same history geometry on the
  availability interval have the same grade-zero label flux at the times of the pulse window
  (the global form of `diagLabelHistoryInvariant_of_diagLifts`, whose statement is a germ at the
  label `0`: the lift data agree on the window, `familyLift_cross_unique` on `univ`);
* `fsd_pathMeanFlux_recenter`, `fsd_diagLabelFlux_recenter`: the label flux of the recentred
  chain `A^{[y]}` on `f(y + ·)` at the label `w` is the label flux of `A` on `f` at `y + w`
  (`liftSequence_shift_covariant` on `Ω = univ`, `liftFluxX_shiftRel`; the copy of
  `ccov_pathMeanFlux_recenter` for the edgeless family, without admissibility of the labels).

For `y = 0` one has `A^{[0]} = A`. -/

section
open CycleComparison.LiftMeanEntrywise Uniqueness Providers.GenSem Providers.QuietAtlas

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Equal history geometry gives the same grade-zero label flux**, at every label. -/
theorem fsd_diagLabelFlux_eq_of_histEq (hζ : IsFastProfile D.ζ) {Mn : SuccMenu} {m : ℕ}
    (hc2 : 0 < D.cellScaleSq m) {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) (Mtop : ℕ) {k : ℤ} (hk : Odd k) {A A' : RealChain}
    (hA : IsAdmissibleChain D b j₀ m k A) (hA' : IsAdmissibleChain D b j₀ m k A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop m k)) (n : ℕ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) :
    diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k A n t =
      diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k A' n t := by
  funext f y
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hav := ocPulseWindow_subset_availInterval D Mtop m k
  have hts : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) :=
    Providers.WeakGen.inv_mul_mem_liftWindowOf hc2 ht
  have hG : ∀ s ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m), ∀ X : Vec 2,
      (diagQ D Dm m k A' (Mn.lenFactor * liftLength D m)).G s X =
        (diagQ D Dm m k A (Mn.lenFactor * liftLength D m)).G s X :=
    fun s hs X => Providers.WeakGen.familyLiftData_G_eq_of_histEq hζ hl hl' hh m k _ _ _
      (hav (Providers.WeakGen.mul_mem_ocPulseWindow hc2 hs)) X
  have hcoef := Providers.WeakGen.familyLift_cross_unique D hζ m k hk A A'
    (Mn.lenFactor * liftLength D m) (fun _ _ _ => []) (fun _ _ _ => []) isOpen_univ
    (Set.subset_univ _) (Set.subset_univ _) _ _ (hts.1.trans hts.2) Mn.N 0 Mn.sX Mn.sZ Mn.sX Mn.sZ
    (Cc0 k A) (Cc0 k A')
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ Mn.sX Mn.sZ _ _ Mn.N 0 _ (hDL k A hk hA))
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ Mn.sX Mn.sZ _ _ Mn.N 0 _
      (hDL k A' hk hA'))
    (fun s hs X _ => hG s hs X) (fun s _ v u d => by simp [familyLiftData, liftEdges])
  have hP : ∀ hh' ≤ 0, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ (Set.univ : Set (Vec 2)),
      Cc0 k A hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X =
        Cc0 k A' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X :=
    fun hh' hh'h n' m' α X hX => funext fun z => funext fun v => funext fun u =>
      hcoef hh' hh'h n' m' α _ hts X hX z v u
  unfold diagLabelFlux
  rw [Uniqueness.pathMeanFlux_eq_of_agreeOn D m _ _ _ _ n t isOpen_univ hP f y (Set.mem_univ _)]
  exact pathMeanFlux_data_point_congr m _ (diagQ D Dm m k A (Mn.lenFactor * liftLength D m))
    (diagQ D Dm m k A' (Mn.lenFactor * liftLength D m)) rfl rfl rfl _ n t f y
    (hG _ hts ((Mn.lenFactor * liftLength D m)⁻¹ • y)).symm

/-- **Recentring covariance of the path mean flux of the edgeless scalar family**, at every
label. -/
theorem fsd_pathMeanFlux_recenter (hζ : IsFastProfile D.ζ) {m : ℕ} (hc : 0 < D.cellScaleSq m)
    {k : ℤ} (hk : Odd k) (A : RealChain) (y : Vec 2) {ρ : ℝ} (hρ : ρ ≠ 0) (sX sZ N : ℕ)
    (Cc' Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hC' : IsLiftSequence (diagQ D Dm m k (A.recenter D y) ρ) sX sZ
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 Cc')
    (hC : IsLiftSequence (diagQ D Dm m k A ρ) sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 Cc)
    (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (f : Vec 2 → ℝ) (w : Vec 2) :
    pathMeanFlux (h := 0) D m ρ (diagQ D Dm m k (A.recenter D y) ρ) Cc' n t
        (fun h' => f (y + h')) w =
      pathMeanFlux (h := 0) D m ρ (diagQ D Dm m k A ρ) Cc n t f (y + w) := by
  have hts := ccov_inv_mul_mem_window hc ht
  have hre : ∀ X : Vec 2,
      (A.recenter D y).recenter D (ρ • X) = A.recenter D (ρ • (X + ρ⁻¹ • y)) := fun X => by
    rw [recenter_recenter D hζ, smul_add, smul_inv_smul₀ hρ, add_comm]
  have hG : ∀ τ X i j, (diagQ D Dm m k (A.recenter D y) ρ).G τ X i j =
      (diagQ D Dm m k A ρ).G τ (X + ρ⁻¹ • y) i j := by
    intro τ X i j
    show ((A.recenter D y).recenter D (ρ • X)).famMetric D (D.cellScaleSq m * τ) i j =
      (A.recenter D (ρ • (X + ρ⁻¹ • y))).famMetric D (D.cellScaleSq m * τ) i j
    rw [hre X]
  have he : ∀ τ, EdgesShiftAt (ρ⁻¹ • y) τ (diagQ D Dm m k (A.recenter D y) ρ).edge
      (diagQ D Dm m k A ρ).edge := fun τ v u d => by
    simp [familyLiftData, liftEdges]
  have hcoef : ∀ hh ≤ 0, ∀ n' m' (α : DerivativeWord2 m'),
      ∀ τ ∈ Icc (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
      ∀ X, X + ρ⁻¹ • y ∈ (Set.univ : Set (Vec 2)) → ∀ z v u,
        Cc' hh n' m' α τ X z v u = Cc hh n' m' α τ (X + ρ⁻¹ • y) z v u := by
    refine liftSequence_shift_covariant (diagQ D Dm m k (A.recenter D y) ρ) (diagQ D Dm m k A ρ)
      (ρ⁻¹ • y) _ _ (hts.1.trans hts.2) isOpen_univ rfl rfl hG (fun τ _ => he τ) ?_ sX sZ N 0
      Cc' Cc (WeakEntryProofs.liftSequenceOn_of_global _ _ sX sZ _ _ N 0 _ hC')
      (WeakEntryProofs.liftSequenceOn_of_global _ _ sX sZ _ _ N 0 _ hC)
    intro X _
    obtain ⟨lo, hi, hlo, hel⟩ := familyLiftData_pos_window D hζ m k (A.recenter D y) ρ
      (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) X
    obtain ⟨Mv, hMv⟩ := familyLiftData_v_bounded D hζ m hk (A.recenter D y) ρ
      (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))
    exact ⟨lo, hi, Mv, windowData_of_elliptic _ _ _ _ lo hi Mv
      (fun t => familyLiftData_symm D m k (A.recenter D y) ρ
        (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ)) t X 0 1) hlo hel
      (fun t _ z => hMv t z)⟩
  have hP : ∀ hh' ≤ 0, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ (Set.univ : Set (Vec 2)),
      Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X =
        slowShiftSequence (ρ⁻¹ • y) Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X :=
    fun hh' hh'h n' m' α X _ => funext fun z => funext fun v => funext fun u =>
      hcoef hh' hh'h n' m' α _ hts X (Set.mem_univ _) z v u
  have hab : ∀ Y : Vec 2, (fun (_ : ℝ) (X : Vec 2) =>
      (Pi.single (0 : Fin (0 + 1)) (f (y + ρ • X)) : Fin (0 + 1) → ℝ))
        ((D.cellScaleSq m)⁻¹ * t) Y =
      (fun (_ : ℝ) (X : Vec 2) => (Pi.single (0 : Fin (0 + 1)) (f (ρ • X)) : Fin (0 + 1) → ℝ))
        ((D.cellScaleSq m)⁻¹ * t) (Y + ρ⁻¹ • y) := by
    intro Y
    show (Pi.single (0 : Fin (0 + 1)) (f (y + ρ • Y)) : Fin (0 + 1) → ℝ) =
      Pi.single (0 : Fin (0 + 1)) (f (ρ • (Y + ρ⁻¹ • y)))
    rw [smul_add, smul_inv_smul₀ hρ, add_comm (ρ • Y) y]
  have hz : ∀ z κ, liftFluxX (ι := Fin (0 + 1)) (diagQ D Dm m k (A.recenter D y) ρ) Cc'
        (fun _ X => Pi.single (0 : Fin (0 + 1)) (f (y + ρ • X))) 0 n
        ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • w) z κ =
      liftFluxX (ι := Fin (0 + 1)) (diagQ D Dm m k A ρ) Cc
        (fun _ X => Pi.single (0 : Fin (0 + 1)) (f (ρ • X))) 0 n
        ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • (y + w)) z κ := by
    intro z κ
    refine (liftFluxX_locEq _ _ 0 n _ isOpen_univ hP κ _ (Set.mem_univ _) z).trans ?_
    rw [show ρ⁻¹ • (y + w) = ρ⁻¹ • w + ρ⁻¹ • y from by rw [smul_add, add_comm]]
    exact liftFluxX_shiftRel (diagQ D Dm m k (A.recenter D y) ρ) (diagQ D Dm m k A ρ) Cc
      (fun _ X => (Pi.single (0 : Fin (0 + 1)) (f (ρ • X)) : Fin (0 + 1) → ℝ))
      (fun _ X => (Pi.single (0 : Fin (0 + 1)) (f (y + ρ • X)) : Fin (0 + 1) → ℝ))
      (ρ⁻¹ • y) ((D.cellScaleSq m)⁻¹ * t) rfl rfl (hG _) (he _) hab 0 n (ρ⁻¹ • w) z κ
  funext κ
  unfold pathMeanFlux
  simp only [hz]

/-- **Recentring covariance of the grade-zero label flux**, at every label. -/
theorem fsd_diagLabelFlux_recenter (hζ : IsFastProfile D.ζ) {Mn : SuccMenu} {m : ℕ}
    (hc : 0 < D.cellScaleSq m) {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) {k : ℤ} (hk : Odd k) {A : RealChain}
    (hA : IsAdmissibleChain D b j₀ m k A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ m k (A.recenter D y))
    (hρ : Mn.lenFactor * liftLength D m ≠ 0) (n : ℕ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (f : Vec 2 → ℝ) (w : Vec 2) :
    diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k (A.recenter D y) n t
        (fun h' => f (y + h')) w =
      diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k A n t f (y + w) :=
  fsd_pathMeanFlux_recenter hζ hc hk A y hρ Mn.sX Mn.sZ Mn.N _ _ (hDL k _ hk hAy)
    (hDL k A hk hA) n ht f w
end

/-! The finer-output step of the flux cancellation, clause (ii) at the label `0`: **the finer output of a
source is, on smooth fields, the differential operator of its symmetric coefficients**, of the
orders `1 ≤ d ≤` the order of the source (`FiniteOrderAt`; the order `d = 1` is the zeroth-order
term, which the transfer to the coarser chart never reads).

* `ccfo_directFlux`: the direct transport, from `fluxCoeff_directFlux` and the symmetry of the
  ordered derivatives.
* `ccfo_exists_cutoff`: near the label `0` the path mean of a localized lift sequence is the path
  mean of cut-off data and lifts which are `LiftRegular` (`exists_cutoff_lift_data`; the source
  edges are regular on the admissible offsets by holomorphy, `contDiffOn_liftedPathEdge`).
* `ccfo_pathMeanFlux`, `ccfo_covLetterFlux`: the array forms `pathMeanFlux_applyArr`,
  `covLetterFlux_applyArr` of the cut-off data, with the sharp order `n - 1 + 2a + 2a'` of the
  covariance letter (`ccfo_arrSupp_covFin`).
* `ccfo_fluxOp_finiteOrder`: the four cases of `SuccSource.fluxOp`, with the order
  `centeredOrder s` (the recorded order of the source, `centeredOrder_eq_tags`). -/

section
open CycleComparison.LiftMeanEntrywise Uniqueness Providers.GenSem

/-! ### Finite order at the label `0` -/

/-- A flux operator is, at the label `0` and on smooth fields, the differential operator of its
symmetric coefficients of the orders `1 ≤ d ≤ K`. -/
def FiniteOrderAt (K : ℕ) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) : Prop :=
  ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
    L g 0 = ∑ d ∈ Finset.Icc 1 K, ∑ I : DerivativeWord2 (d - 1),
      orderedDerivative I g 0 • fluxCoeff L d I 0

theorem finiteOrderAt_of_arr {K : ℕ} (hK : 1 ≤ K) (Arr : Fin 2 → CArr)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hL : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
      L g 0 c = applyArr (K - 1) (Arr c) g 0 0) : FiniteOrderAt K L := by
  intro g hg
  have h := Providers.QuietAtlas.arrOp_eq_sum_fluxCoeff (K - 1) Arr L hL hg
  rw [Nat.sub_add_cancel hK] at h
  rw [h]
  exact (Providers.QuietAtlas.sum_Icc_one_eq_sum_range (fun d =>
    ∑ I : DerivativeWord2 (d - 1), orderedDerivative I g 0 • fluxCoeff L d I 0) K).symm

theorem finiteOrderAt_of_zero {K : ℕ} {L : (Vec 2 → ℝ) → Vec 2 → Vec 2}
    (hL : ∀ g, L g 0 = 0) : FiniteOrderAt K L := by
  intro g _
  rw [hL g]
  simp [fluxCoeff, hL]

theorem FiniteOrderAt.sub {K : ℕ} {L₁ L₂ : (Vec 2 → ℝ) → Vec 2 → Vec 2}
    (h₁ : FiniteOrderAt K L₁) (h₂ : FiniteOrderAt K L₂) :
    FiniteOrderAt K (fun g y => L₁ g y - L₂ g y) := by
  intro g hg
  have e : ∀ d (I : DerivativeWord2 (d - 1)),
      fluxCoeff (fun g y => L₁ g y - L₂ g y) d I 0 = fluxCoeff L₁ d I 0 - fluxCoeff L₂ d I 0 :=
    fun d I => by simp only [fluxCoeff, smul_sub]
  simp only [e, smul_sub, Finset.sum_sub_distrib]
  rw [← h₁ g hg, ← h₂ g hg]

/-- Symmetrized coefficients against permutation-invariant weights. -/
theorem ccfo_sum_symm {r : ℕ} (F : DerivativeWord2 r → Vec 2) (w : DerivativeWord2 r → ℝ)
    (hw : ∀ A (σ : Equiv.Perm (Fin r)), w (A ∘ σ) = w A) :
    ∑ I, w I • (((r.factorial : ℝ))⁻¹ • ∑ σ : Equiv.Perm (Fin r), F (I ∘ σ)) =
      ∑ α, w α • F α := by
  have hp : ∀ σ : Equiv.Perm (Fin r), ∑ I, w I • F (I ∘ σ) = ∑ α, w α • F α := by
    intro σ
    have he := Equiv.sum_comp (CycleComparison.Lift.wordPermutationEquiv σ) (fun A => w A • F A)
    simp only [CycleComparison.Lift.wordPermutationEquiv, Equiv.coe_fn_mk, hw] at he
    exact he
  have h1 : ∀ I, w I • (((r.factorial : ℝ))⁻¹ • ∑ σ : Equiv.Perm (Fin r), F (I ∘ σ)) =
      ∑ σ : Equiv.Perm (Fin r), ((r.factorial : ℝ))⁻¹ • (w I • F (I ∘ σ)) := fun I => by
    rw [smul_comm, Finset.smul_sum, Finset.smul_sum]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, hp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)), one_smul]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The direct transport has finite order**: its coefficients above `K` vanish. -/
theorem ccfo_directFlux {G : GenStage D hr Dm b j₀} (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ)
    (t : ℝ) (K : ℕ) (hords : ∀ d ∈ ords, 1 ≤ d)
    (hK : ∀ d ∈ ords, K < d → ∀ α : DerivativeWord2 (d - 1),
      G.fam.flux p c v u γ d α = fun _ _ _ => 0) :
    FiniteOrderAt K (directFlux G p c γ ords t) := by
  classical
  intro g hg
  have hw : ∀ {r : ℕ} (A : DerivativeWord2 r) (σ : Equiv.Perm (Fin r)),
      orderedDerivative (A ∘ σ) g 0 = orderedDerivative A g 0 := fun A σ =>
    congrFun (CycleComparison.Lift.orderedDerivative_comp_perm A σ g hg) 0
  have hT : ∀ d ∈ Finset.Icc 1 K, (∑ I : DerivativeWord2 (d - 1),
      orderedDerivative I g 0 • fluxCoeff (directFlux G p c γ ords t) d I 0) =
      if d ∈ ords then ∑ α : DerivativeWord2 (d - 1),
        (D.kap G.level * D.eps G.level ^ (d - 2) * orderedDerivative α g 0) •
          fieldCellMean (fun z => G.fam.flux p c v u γ d α t
            ((D.eps (G.level - 1))⁻¹ • (0 : Vec 2)) z) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    simp only [fluxCoeff_directFlux G p c γ ords hords t hd1]
    by_cases hdo : d ∈ ords
    · simp only [hdo, ite_true]
      have h2 : ∀ I : DerivativeWord2 (d - 1),
          (D.kap G.level * D.eps G.level ^ (d - 2) * (((d - 1).factorial : ℝ))⁻¹) •
            ∑ σ : Equiv.Perm (Fin (d - 1)),
              fieldCellMean (fun z => G.fam.flux p c v u γ d (I ∘ σ) t 0 z) =
          (((d - 1).factorial : ℝ))⁻¹ • ∑ σ : Equiv.Perm (Fin (d - 1)),
            (fun α : DerivativeWord2 (d - 1) => (D.kap G.level * D.eps G.level ^ (d - 2)) •
              fieldCellMean (fun z => G.fam.flux p c v u γ d α t 0 z)) (I ∘ σ) := fun I => by
        rw [mul_comm, mul_smul, Finset.smul_sum]
      simp only [h2]
      refine (ccfo_sum_symm (fun α : DerivativeWord2 (d - 1) =>
        (D.kap G.level * D.eps G.level ^ (d - 2)) •
          fieldCellMean (fun z => G.fam.flux p c v u γ d α t 0 z))
        (fun A => orderedDerivative A g 0) (fun A σ => hw A σ)).trans ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [smul_zero, smul_smul, mul_comm]
    · simp only [hdo, ite_false, smul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hT, Finset.sum_ite_mem]
  unfold directFlux
  symm
  refine Finset.sum_subset Finset.inter_subset_right fun d hd hnd => ?_
  have hKd : K < d := by
    by_contra hle
    exact hnd (Finset.mem_inter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hords d hd, not_lt.mp hle⟩, hd⟩)
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [hK d hd hKd α]
  simp [fieldCellMean]

/-! ### The path means -/

/-- Near the label `0` the path mean of a localized lift sequence is the path mean of regular
cut-off data and lifts. -/
theorem ccfo_exists_cutoff (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {G : GenStage D hr Dm b j₀}
    {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ} (hcert : G.OldCert 𝒮 μ L Cθ) {h : ℕ}
    (π : StagePath G h) (k : ℤ) (hk : Odd k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ G.level k B) {ρ : ℝ} (hρ : ρ ≠ 0) {sX sZ N R : ℕ}
    (hRX : R ≤ sX) (hRZ : R ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) :
    ∃ (Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
      (Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)),
      (∀ (n : ℕ) (g : Vec 2 → ℝ), pathMeanFlux D G.level ρ
          (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc n t g =ᶠ[𝓝 0]
        pathMeanFlux D G.level ρ Q' Cc' n t g) ∧
      ∀ n R', R' ≤ R →
        LiftRegular Q' Cc' (0 : Fin (h + 1)) ((D.cellScaleSq G.level)⁻¹ * t) h n R' := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  obtain ⟨r, hr, -, e', C', hagree, hCeq, -, hreg⟩ := exists_cutoff_lift_data D G.level k
    hB.2.2.1 ρ (div_ne_zero hρ hε) (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)
    (isOpen_ladderOmega D b j₀ G.level k B ρ) (zero_mem_ladderOmega hζ hB ρ) hC hRX hRZ
    (fun τ hτ v u d γ hγ α c =>
      contDiffOn_liftedPathEdge hΛ hζ hκ hb G hcert π k hk ρ hB hτ v u d γ hγ α c R)
  refine ⟨familyLiftData D G.level k B ρ e', C', fun n g => ?_, fun n R' hR' =>
    hreg h le_rfl n R' hR' _ (ccov_inv_mul_mem_window hc ht) 0⟩
  have hO : IsOpen {y : Vec 2 | ρ⁻¹ • y ∈ Metric.ball (0 : Vec 2) r} :=
    Metric.isOpen_ball.preimage (continuous_const_smul _)
  have h0 : (0 : Vec 2) ∈ {y : Vec 2 | ρ⁻¹ • y ∈ Metric.ball (0 : Vec 2) r} := by
    show ρ⁻¹ • (0 : Vec 2) ∈ Metric.ball (0 : Vec 2) r
    rw [smul_zero]
    exact Metric.mem_ball_self hr
  filter_upwards [hO.mem_nhds h0] with y hy
  exact pathMeanFlux_eq_of_dataAgree D G.level ρ hagree Cc C' n t Metric.isOpen_ball
    (fun hh' _ n' m' α X hX => (hCeq hh' n' m' α _ X hX).symm) g y hy

/-- **The path mean of degree `n ≥ 1` has order `n`** at the label `0`. -/
theorem ccfo_pathMeanFlux (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {G : GenStage D hr Dm b j₀}
    {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ} (hcert : G.OldCert 𝒮 μ L Cθ) {h : ℕ}
    (π : StagePath G h) (k : ℤ) (hk : Odd k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ G.level k B) {ρ : ℝ} (hρ : ρ ≠ 0) {sX sZ N : ℕ}
    (hRX : Dm + 2 ≤ sX) (hRZ : Dm + 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {n : ℕ} (hn : 1 ≤ n) :
    FiniteOrderAt n (pathMeanFlux D G.level ρ
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc n t) := by
  obtain ⟨Q', Cc', hgerm, hreg⟩ := ccfo_exists_cutoff hΛ hζ hκ hb hcert π k hk hB hρ hRX hRZ
    Cc hC ht
  refine finiteOrderAt_of_arr hn (fun c => pmArr D G.level ρ Q' Cc' n t c) _ fun g hg c => ?_
  rw [(hgerm n g).eq_of_nhds, pathMeanFlux_applyArr D G.level hρ Q' Cc' n t
    (hreg n (Dm + 2) le_rfl) (hg.of_le (by exact_mod_cast le_top)) 0 c]
  exact congrFun (congrFun (applyArr_eq_of_supp (K := n - 1) (K' := n) (by omega)
    (arrSupp_pmArr D G.level ρ Q' Cc' n t c) g) 0) 0

/-! ### The covariance letters -/

theorem ccfo_arrSupp_chartArr {K₀ : ℕ} (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (N Ψ : Vec 2 → Vec 2) (K : ℕ) {A : Fin 2 → CArr} (hA : ∀ k, ArrSupp K₀ (A k)) (c : Fin 2) :
    ArrSupp K₀ (chartArr M N Ψ K A c) := by
  intro m' hm' γ
  funext p z
  simp only [chartArr, chartCoef, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => ?_, mul_zero]
  by_cases hmK : m ≤ K₀
  · rw [arrSupp_fdbArr Ψ α m' (by omega) γ]
    simp
  · rw [hA k m (by omega) α]
    simp

theorem ccfo_arrSupp_compArr {J' K : ℕ} (J : ℕ) {C B : CArr} (z0 : Vec 2) (hC : ArrSupp J' C)
    (hB : ArrSupp K B) : ArrSupp (J' + K) (compArr J C B z0) := by
  intro m' hm' β
  funext X z
  unfold compArr
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => ?_
  by_cases hmJ : m ≤ J'
  · have := arrSupp_iterSlow α hB m' (by omega) β
    simp [this]
  · rw [hC m (by omega) α]
    simp

/-- The arrays of the covariance letter have the order `2a + (n - 1) + 2a'`. -/
theorem ccfo_arrSupp_covFin (D : OCData) (m : ℕ) (ρ s₀ : ℝ) {h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : ArrSupp (2 * a + (n - 1 + 2 * a')) (covFin D m ρ s₀ Q Cc n a a' t A c) := by
  have h1 : ∀ c, ArrSupp (n - 1) (covB1 D m ρ Q Cc n t A c) := fun c =>
    ccfo_arrSupp_chartArr _ _ _ n (fun κ => arrSupp_pmArr D m ρ Q Cc n t κ) c
  have h2 : ∀ c, ArrSupp (n - 1 + 2 * a') (covB2 D m ρ s₀ Q Cc n a' t A c) := fun c =>
    ccfo_arrSupp_compArr n 0 (h1 c) (covArrPow_supp _ a')
  have h4 : ∀ c, ArrSupp (2 * a + (n - 1 + 2 * a')) (covB4 D m ρ s₀ Q Cc n a a' t A c) := by
    intro c m' hm' β
    have := arrSupp_compArr (2 * a) (covArrPow (covMat D m s₀ t) a) (0 : Vec 2) (h2 c) m' hm' β
    simp only [covB4, Pi.smul_apply, this, smul_zero]
  exact ccfo_arrSupp_chartArr _ _ _ _ h4 c

/-- The slow flux of degree `0` and grade `hh ≥ 1` vanishes. -/
theorem ccfo_liftFluxX_degree_zero {ι : Type*} [Fintype ι] {hv : ι → Type*}
    [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]
    (Q : LiftOperatorData ι hv Dm) (Cc : ℕ → ℕ → LiftCoeff ι hv) (a : ℝ → Vec 2 → ∀ i, hv i)
    {hh : ℕ} (hh1 : 1 ≤ hh) (hz : ∀ m α t X z v u, Cc hh 0 m α t X z v u = 0) (t : ℝ)
    (X z : Vec 2) (k : Fin 2) : liftFluxX Q Cc a hh 0 t X z k = 0 := by
  have hL : liftApply 0 (Cc hh 0) a t = fun _ _ => 0 := by
    funext X z v
    simp [liftApply, hz]
  have hne : hh ≠ 0 := by omega
  unfold liftFluxX
  simp only [Nat.zero_sub, hL]
  simp [fastPartial, hne]

theorem ccfo_covOperator_iterate_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 2) (Fin 2) ℝ) : ∀ a : ℕ, (covOperator H)^[a] (fun _ : Vec 2 => (0 : E)) =
      fun _ => 0
  | 0 => rfl
  | a + 1 => by
      have h0 : covOperator H (fun _ : Vec 2 => (0 : E)) = fun _ => 0 := by
        funext x
        simp [covOperator]
      rw [Function.iterate_succ_apply, h0, ccfo_covOperator_iterate_zero H a]

/-- **The covariance letter `𝖵_{n,h,a,a'}` has order `n + 2(a + a')`** at the label `0`. -/
theorem ccfo_covLetterFlux (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {G : GenStage D hr Dm b j₀}
    {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ} (hcert : G.OldCert 𝒮 μ L Cθ) {h : ℕ}
    (hh1 : 1 ≤ h) (π : StagePath G h) (k : ℤ) (hk : Odd k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ G.level k B) {ρ : ℝ} (hρ : ρ ≠ 0) {sX sZ N : ℕ} {n a a' : ℕ}
    (hRX : 2 * a + Dm + 2 ≤ sX) (hRZ : 2 * a + Dm + 2 ≤ sZ) (hK : 1 ≤ n + 2 * (a + a'))
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (s₀ : ℝ) :
    FiniteOrderAt (n + 2 * (a + a')) (covLetterFlux D G.level ρ s₀
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc n a a' t B) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- the path mean of degree `0` vanishes
    subst hn0
    have hpm : pathMeanFlux D G.level ρ
        (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc 0 t =
        fun _ _ => 0 := by
      funext f y κ
      unfold pathMeanFlux
      simp only [ccfo_liftFluxX_degree_zero _ Cc _ hh1
        (fun m α t X z v u => hC.2.1 h hh1 le_rfl m α t X z v u)]
      simp [fieldCellMean]
    refine finiteOrderAt_of_zero fun g => ?_
    unfold covLetterFlux pullFlux
    have hpush : ∀ f : Vec 2 → ℝ, pushFlux (B.famMap D t) (B.famMapInv D t)
        (fun _ _ => (0 : Vec 2)) f = fun _ => 0 := by
      intro f
      funext x
      simp [pushFlux]
    rw [hpm]
    simp only [hpush, SuccSource.covAtFlux, ccfo_covOperator_iterate_zero]
    simp
  · obtain ⟨Q', Cc', hgerm, hreg⟩ := ccfo_exists_cutoff hΛ hζ hκ hb hcert π k hk hB hρ hRX hRZ
      Cc hC ht
    refine finiteOrderAt_of_arr hK (fun c => covFin D G.level ρ s₀ Q' Cc' n a a' t B c) _
      fun g hg c => ?_
    have hEq : covLetterFlux D G.level ρ s₀
        (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc n a a' t B g 0 =
        covLetterFlux D G.level ρ s₀ Q' Cc' n a a' t B g 0 := by
      unfold covLetterFlux
      refine (Providers.QuietAtlas.pullFlux_germ (contDiff_famMap B t).continuous.continuousAt
        (famMap_zero B t) (fun g' => ?_) g).eq_of_nhds
      have hpush := pushFlux_germ (Ψ := B.famMap D t)
        (contDiff_famMapInv B t).continuous.continuousAt
        (famMapInv_zero hζ B t) (fun g'' => hgerm n g'')
        ((SuccSource.covAt D G.level s₀ t)^[a'] g')
      have hcg := covOperator_iterate_germ
        (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) s₀ t) a hpush
      filter_upwards [hcg] with x hx
      simp only [SuccSource.covAtFlux]
      rw [hx]
    rw [hEq, covLetterFlux_applyArr hζ hρ B (hreg n (2 * a + Dm + 2) le_rfl) hg 0 c]
    have hKe : n + 2 * (a + a') - 1 = 2 * a + (n - 1 + 2 * a') := by omega
    rw [hKe]
    exact congrFun (congrFun (applyArr_eq_of_supp (K := 2 * a + (n - 1 + 2 * a'))
      (K' := 2 * a + (n + 2 * a')) (by omega)
      (ccfo_arrSupp_covFin D G.level ρ s₀ Q' Cc' n a a' t B c) g) 0) 0

/-! ### The finer output of a source -/

/-- The order of the finer output of a source (`0` for the first source, whose output is fixed
by its own clause of `IsActualSuccessor`). -/
def centeredOrder {G : GenStage D hr Dm b j₀} : SuccSource G → ℕ
  | .copyDir _ v u γ => (G.fam.identity v u γ).maxOrder
  | .copyQuad .. => 2
  | .letterDiag .. => 0
  | .letterMean _ n _ _ => n
  | .letterCov _ n _ a a' _ => n + 2 * (a + a')

open scoped Classical in
/-- **The finer-output step, clause (ii) at the label `0`.** The finer output of a valid source other than the
first source, on an admissible family and at a time of the pulse window, is on smooth fields the
differential operator of its symmetric coefficients of the orders `1 ≤ d ≤ centeredOrder s`. -/
theorem ccfo_fluxOp_finiteOrder (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {G : GenStage D hr Dm b j₀}
    {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ} (hcert : G.OldCert 𝒮 μ L Cθ)
    (Mn : SuccMenu) (hρ : Mn.lenFactor * liftLength D G.level ≠ 0) (s₀ : ℝ) (s : SuccSource G)
    {A : Finset WordLetter} {J : ℕ} (hv : s.Valid A J) (hord : 1 ≤ centeredOrder s)
    (hres : CenteredReserve Mn s)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (k : ℤ) (hk : Odd k) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ G.level k B) :
    FiniteOrderAt (centeredOrder s)
      (s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t B) := by
  obtain ⟨hRX, hRZ, hcov⟩ := hres
  unfold SuccSource.fluxOp
  rw [dite_eq_left ⟨hB, hk⟩]
  cases s with
  | copyDir t' v u γ =>
    refine ccfo_directFlux ⟨k, hk⟩ ⟨B, hB⟩ γ (Finset.Icc 3 Dm) t _
      (fun d hd => by have := (Finset.mem_Icc.mp hd).1; omega) fun d _ hKd α => ?_
    exact G.fam.flux_zero ⟨k, hk⟩ ⟨B, hB⟩ v u γ d α (fun h => by
      have : d ≤ (G.fam.identity v u γ).maxOrder := h.2
      exact absurd hKd (not_lt.mpr this))
  | letterDiag t' u => exact absurd hord (by simp [centeredOrder])
  | copyQuad t' h π =>
    exact ccfo_pathMeanFlux hΛ hζ hκ hb hcert π k hk hB hρ hRX hRZ (Cc k B)
      (hLF k B ⟨hB, hk⟩) ht hord
  | letterMean t' n h π =>
    have hn : 1 ≤ n := hord
    have hpm := ccfo_pathMeanFlux hΛ hζ hκ hb hcert π k hk hB hρ hRX hRZ (Cc k B)
      (hLF k B ⟨hB, hk⟩) ht hn
    by_cases h1 : h = 1
    · subst h1
      have hd := ccfo_directFlux ⟨k, hk⟩ ⟨B, hB⟩ (π.step ⟨0, by omega⟩).2.2 {n} t n
        (fun d hd => by rw [Finset.mem_singleton.mp hd]; exact hn)
        (fun d hd hKd => absurd hKd (by rw [Finset.mem_singleton.mp hd]; exact lt_irrefl n))
      simp only [↓reduceDIte]
      exact hpm.sub hd
    · simp only [h1, ↓reduceDIte, sub_zero]
      exact hpm
  | letterCov t' n h a a' π =>
    exact ccfo_covLetterFlux hΛ hζ hκ hb hcert hv.2.2 π k hk hB hρ hcov.1 hcov.2 hord (Cc k B)
      (hLF k B ⟨hB, hk⟩) ht s₀
end

/-! The finer-output step of the flux cancellation: **the finer output of a source from its centred
coefficients**.

Clause (ii) cannot be stated for a field of class `C^{order}` or without reserves of the lifts
(the `ε`-coefficients of `dEpsWord` take more slow derivatives than the order, and `fderiv` of a
non-differentiable function is `0`; without reserves the output is not linear in the field). It is
stated for smooth fields under the reserves `CenteredReserve`.

* `centeredCoefficient_expansion` (proved): clause (i) for every field, and clause (ii) with the
  zeroth-order term kept (orders `1 ≤ d ≤ order`). This is all that the transfer step uses: the transfer
  to the coarser chart reads the orders `d ≥ 2` only.
* `CenteredConstantsStatement`: the finer output annihilates constants.
* `centeredCoefficientFiniteOrder_of_constants`: the statement of the finer-output step
  (`CenteredCoefficientFiniteOrderStatement`, orders `2 ≤ d ≤ order`) follows from
  `CenteredConstantsStatement`. -/

section
open Uniqueness Providers.GenSem

section Order
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The recorded order of a source other than the first source is the order of its finer
output. -/
theorem centeredOrder_eq_tags {P : ProvParams} {G : GenStage D hr Dm b j₀} (htag : G.HasTags P)
    (s : SuccSource G) (hnd : ¬ s.IsDiag) :
    ((s.prov G.level).tags P).order = centeredOrder s := by
  cases s with
  | copyDir t v u γ =>
    simp only [SuccSource.prov, Prov.tags, centeredOrder]
    exact (htag v u γ).2.symm
  | copyQuad t h π =>
    simp only [SuccSource.prov, Prov.tags, centeredOrder]
    split <;> rfl
  | letterDiag t u => exact absurd trivial hnd
  | letterMean t n h π => simp only [SuccSource.prov, Prov.tags, centeredOrder, letterOrder]
  | letterCov t n h a a' π => simp only [SuccSource.prov, Prov.tags, centeredOrder, letterOrder]

/-- The order of a valid source other than the first source is at least `1`. -/
theorem one_le_centeredOrder {P : ProvParams} {G : GenStage D hr Dm b j₀} {A : Finset WordLetter}
    {J : ℕ} (hlet : ∀ l ∈ A, 2 ≤ letterOrder P.N P.p l) (s : SuccSource G) (hv : s.Valid A J)
    (hnd : ¬ s.IsDiag) : 1 ≤ centeredOrder s := by
  cases s with
  | copyDir t v u γ =>
    have := (G.fam.identity v u γ).two_le
    show 1 ≤ (G.fam.identity v u γ).maxOrder
    omega
  | copyQuad t h π => show 1 ≤ 2; norm_num
  | letterDiag t u => exact absurd trivial hnd
  | letterMean t n h π =>
    have h2 : 2 ≤ n := hlet _ (hv.2.1 _ rfl).2
    show 1 ≤ n
    omega
  | letterCov t n h a a' π =>
    have h2 : 2 ≤ n + 2 * (a + a') := hlet _ (hv.2.1 _ rfl).2
    show 1 ≤ n + 2 * (a + a')
    omega

/-- The coefficient of a flux operator at a label is the coefficient at the label `0` of the
operator in the recentred field. -/
theorem fluxCoeff_recenter {L L' : (Vec 2 → ℝ) → Vec 2 → Vec 2} {y : Vec 2}
    (hL : ∀ f : Vec 2 → ℝ, L' (fun h' => f (y + h')) 0 = L f y) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) : fluxCoeff L' d I 0 = fluxCoeff L d I y := by
  unfold fluxCoeff
  rw [← hL]
  congr 2
  funext h'
  simp only [add_sub_cancel_left, sub_zero]

/-- **Finite order at a label from finite order at the label `0` of the recentred operator.** -/
theorem finiteOrder_of_recenter {K : ℕ} {L L' : (Vec 2 → ℝ) → Vec 2 → Vec 2} {y : Vec 2}
    (hL : ∀ f : Vec 2 → ℝ, L' (fun h' => f (y + h')) 0 = L f y) (hfo : FiniteOrderAt K L')
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    L f y = ∑ d ∈ Finset.Icc 1 K, ∑ I : DerivativeWord2 (d - 1),
      orderedDerivative I f y • fluxCoeff L d I y := by
  rw [← hL f, hfo (fun h' => f (y + h')) (hf.comp (contDiff_const.add contDiff_id))]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun I _ => ?_
  rw [ccov_orderedDerivative_add_left I f y 0, add_zero, fluxCoeff_recenter hL d I]

end Order

/-- **The finer-output step, proved part: recentring covariance and finite order of the finer output.** For a
valid source other than the first source, an odd slot `k`, a time of its window and an admissible
family `A` whose recentring at the label `y` is admissible:
(i) the output of the recentred family at its centre, on the shifted field, is the output of `A`
at `y`, for every field;
(ii) under the reserves `CenteredReserve`, on smooth fields the output is the differential
operator of its `fluxCoeff` at the point, of the orders `1 ≤ d ≤` the recorded order of the
source (`d = 1` is the zeroth-order term). -/
theorem centeredCoefficient_expansion
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hin : StageSuccessor.Input P Mn G) (s : SuccSource G) (hv : s.Valid Mn.A Mn.J)
    (hnd : ¬ s.IsDiag)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (k : ℤ) (hk : Odd k) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level k (A.recenter D y)) :
    (∀ f : Vec 2 → ℝ,
      s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t (A.recenter D y)
          (fun h => f (y + h)) 0 =
        s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t A f y) ∧
    (CenteredReserve Mn s → ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t A f y =
        ∑ d ∈ Finset.Icc 1 ((s.prov G.level).tags P).order, ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I f y •
            fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t A)
              d I y) := by
  obtain ⟨kI, hcert⟩ := hin.context
  have hΛ := hin.base
  have hζ := hin.profile
  have hκ := hin.band
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    have hκm : 0 < D.κ (G.level - 1) :=
      CycleReference.bandChain_pos hΛ hζ hκ (by have := hin.top; omega)
    exact (mul_pos hin.length_factor
      (Real.sqrt_pos.2 (mul_pos hκm (Construction.Stream.ocTauPP_pos hΛ)))).ne'
  have hcov : FluxRecenterShift G := fluxRecenterShift_of_oldCert hΛ hζ hcert.oldCert
  have hi : ∀ f : Vec 2 → ℝ,
      s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t (A.recenter D y)
          (fun h => f (y + h)) 0 =
        s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t A f y := fun f =>
    ccov_fluxOp_recenter hΛ hζ hcov hc Mn hρ Mn.anchor s Cc hLF k hk ht hA y hAy f
  refine ⟨hi, fun hres f hf => ?_⟩
  rw [centeredOrder_eq_tags hin.tags s hnd]
  have hlet : ∀ l ∈ Mn.A, 2 ≤ letterOrder P.N P.p l := fun l hl => (hin.letter_orders l hl).1
  exact finiteOrder_of_recenter hi
    (ccfo_fluxOp_finiteOrder hΛ hζ hκ hin.bandwidth hcert.oldCert Mn hρ Mn.anchor s hv
      (one_le_centeredOrder hlet s hv hnd) hres Cc hLF k hk ht hAy) hf

/-- **The finer outputs annihilate constants.** For a valid source other
than the first source, an odd slot, a time of its window and an admissible family, under the
reserves of the lifts, the finer output of the constant field `1` vanishes at the label `0`.
Proof route: by the cut-off array form (`ccfo_exists_cutoff`, `pathMeanFlux_applyArr`) the value
is the order-`0` entry of `pmArr`, a cell mean of the order-`0` entry of `fluxXArr`, which is
built from the order-`0` entries of the lifts `Cc hh n'`. These vanish on the ladder for
`(hh, n') ≠ (0, 0)`: induction on `(hh, n')` as in `lift_sequence_unique_window_on`; the cell source
of the constant field is the order-`0` entry of `srcArr` (`liftCellSource_monoField`, with the empty
word), which vanishes when the lower order-`0` entries do (`ℬ_1`, `ℬ_2` differentiate, and the
source edges have orders `d ≥ 2`), so the cell inverse is the one of the zero field
(`cellField_unique_window` against the lift relation at `a₀ = 0`). The direct transport has no order
below `3`, and the covariance letter is `𝒞^a ∘ Φ_* ℳ ∘ 𝒞^{a'}` with `𝒞 1 = 0`. It is not used by the
transfer step; the source-mean step needs it to pass from `fluxOpApply` (orders `d ≥ 2`) to the full
mean. -/
def CenteredConstantsStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G →
    ∀ (s : SuccSource G), s.Valid Mn.A Mn.J → ¬ s.IsDiag → CenteredReserve Mn s →
    ∀ (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)),
    s.IsLiftFamily Mn Cc →
    ∀ (k : ℤ), Odd k → ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level k,
    ∀ (B : RealChain), IsAdmissibleChain D b j₀ G.level k B →
      s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t B (fun _ => 1) 0 = 0

/-- **The finer-output step from the statement that the finer outputs annihilate constants.** -/
theorem centeredCoefficientFiniteOrder_of_constants (hconst : CenteredConstantsStatement) :
    CenteredCoefficientFiniteOrderStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' hin _ W s hv hnd k hk t ht A hA y hAy
  obtain ⟨hi, hii⟩ := centeredCoefficient_expansion P Mn G hin s hv hnd (W.Cc s) (W.lifts s) k hk
    t ht A hA y hAy
  refine ⟨hi, fun hres f hf => ?_⟩
  rw [hii hres f hf]
  have hK : 1 ≤ ((s.prov G.level).tags P).order := by
    rw [centeredOrder_eq_tags hin.tags s hnd]
    exact one_le_centeredOrder (fun l hl => (hin.letter_orders l hl).1) s hv hnd
  rw [← Finset.insert_Icc_succ_left_eq_Icc hK, Finset.sum_insert (by simp)]
  have h0 : ∀ I : DerivativeWord2 (1 - 1),
      fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.Cc s) k t A)
        1 I y = 0 := by
    intro I
    have hc := hconst P Mn G hin s hv hnd hres (W.Cc s) (W.lifts s) k hk t ht (A.recenter D y) hAy
    have hi1 := hi (fun _ => 1)
    unfold fluxCoeff
    have hone : (fun Y : Vec 2 => ∏ j : Fin (1 - 1), (Y - y) (I j)) = fun _ => 1 := by
      funext Y
      exact Finset.prod_empty
    rw [hone, ← hi1, hc, smul_zero]
  simp only [h0, smul_zero, Finset.sum_const_zero, zero_add]
  rfl
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
