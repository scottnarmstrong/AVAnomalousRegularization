-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.NativeContextKernelOperator
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.IncomingLedgerBudget
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.CycleComparison.Residual.FastJets.Sampling
public import AVRegularity.EntryWeak.FluxProductionArithmetic
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Families.TorusCompatible.WeakStage
import AVenhance.Infra.Construction.StreamAdmissible

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniformly assemble the actual native kernel operator at either effective mass. -/

theorem uniform_native_kernel_operator_of_certificates (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hb : 0 < bw) (n Dm : ℕ)
    (hDm : 2 ≤ Dm) (c : ℕ → ℝ) (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
        [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → G.IsShiftInvariant → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      ∀ (P : ProvParams) (seedK freshK : ℕ → KernelSpec),
      (∀ v u γ, (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width) →
      ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (a b ρ Sbound : ℝ) (π marker : CompIn G.comps → ℝ),
      a ≤ b → 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∀ v, 0 < π v) → (∀ v, 0 < marker v) → markedLedger π marker G.fam ≤ Sbound →
      A * Sbound ≤ 1 / 8 →
      (∀ v u γ, IsSpatialRegularizerTorus ρ 0 Dm a b c
        (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ)) →
      ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = marker →
      ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
          (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ (D.kap G.level) n Dm,
        R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
          (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
        R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
          ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
        R.S = G.sysS P seedK freshK φ₀ hφ₀ ∧ R.π = (fun v => π v / w v ^ 2) ∧
        R.r = (fun v u γ => (G.kernelOf P seedK freshK v u γ).width) ∧ R.c = c ∧ R.θ = A * Sbound := by
  obtain ⟨A, hA, m₀, hm₀, hschur⟩ := uniform_native_kernel_schur_of_certificates
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ bw hb n (n + Dm) Dm (le_refl _) c hc
  refine ⟨A, hA, m₀, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq j₀ M G k hG hnat hshift hlevel hi hj
    hE he hν hpar hm hm2 P seedK freshK hwidth φ₀ hφ₀ a b ρ Sbound π marker hab hρ hρE hρe
    hlength hπ hmarker hledger hsmall hSzero w hw
  have hwpos v : 0 < w v := by
    rcases hw with rfl | rfl
    · norm_num
    · exact hmarker v
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  let R := nativeContextKernelOperator P seedK freshK φ₀ hφ₀ G
    hG hpar hnat hshift hΛD hi hj hb hE hm hm2 a b ρ (D.kap G.level) n hab hρ hρE hν hDm
    (fun v => π v / w v ^ 2) (fun v => div_pos (hπ v) (sq_pos_of_pos (hwpos v)))
    c (fun v u γ => by rw [hwidth v u γ]; exact (G.fam.identity v u γ).record.width_pos)
    hSzero (A * Sbound) hsmall
    (hschur hr D hDα hDq hDΛ hDζ hseq j₀ M G k hG hnat hlevel hi hj hE he hν hpar hm hm2
      P seedK freshK hwidth a b ρ Sbound π marker hρ hρE hρe hlength hπ hmarker hledger w hw)
  exact ⟨R, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Construct on the measurable window extension at the true source degree,
then recover the literal ambient-cap recurrence on the original window. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D Ksrc H N K k L qs qf : ℕ} {hKD : Ksrc ≤ D} {Q : LiftOperatorData ι h D}
  {π : ι → ℝ} {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2}
  {V : ℝ → ℝ → ℝ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
  {price : ι → ι → ℝ} {Θ : ℝ}

/-- Retain the restricted sequence for ambient grading while promoting the same coefficients. -/
theorem effective_window_lift_exists_with_restricted
    (P : IsLiftSetting
      (EntryWeakProofs.restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge})
      π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj price Θ)
    (hz : ∀ v u d, Ksrc < d.1 → Q.edge v u d = []) :
    ∃ Cc : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequence
        (EntryWeakProofs.restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge})
        (K + Ksrc + 2) (max (k + 1) (L + 2)) a b N H Cc ∧
      IsLiftSequence Q (K + Ksrc + 2) (max (k + 1) (L + 2)) a b N H Cc := by
  obtain ⟨Cc, hc⟩ := Providers.cycle_lift_exists N K k L Ksrc H CG Cw Cj
    (EntryWeakProofs.restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge})
    π a b e ν B ρ E ℓ dstar εc lam par V qs qf price Θ P
  have hz' : ∀ v u d, Ksrc < d.1 → windowEdges a b Q.edge v u d = [] := by
    intro v u d hd
    simp only [windowEdges, hz v u d hd, List.map_nil]
  exact ⟨Cc, hc, windowEdges_liftSequence Q a b _ _ N H Cc
    (effective_liftSequence_promote P hz' _ _ (by omega) Cc hc)⟩
end

/-! A native setting and its constructed coefficients retain both effective and ambient recurrences. -/

section
open EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

structure NativeSlotLift (G : GenStage D hr Dm bw j₀) (slot : OddSlot)
    (π : CompIn G.comps → ℝ) (H N K k L : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S : ℝ) where
  cap : ℕ
  cap_le : cap ≤ Dm
  cap_ge : 2 ≤ cap
  empty : ∀ v u d, cap < d.1 →
    (familyLiftData D G.level slot.1 (nativeChain G.level slot.1) (liftLength D G.level)
      (G.fam.fiber slot (G.actual slot))).edge v u d = []
  setting :
    let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
    let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) (liftLength D G.level)
      (G.fam.fiber slot (G.actual slot))
    IsLiftSetting (restrictLiftData cap cap_le {Q with edge := windowEdges a b Q.edge})
      π a b (D.eps G.level) (D.kap G.level) (D.kap (G.level - 1)) (liftLength D G.level)
      (D.eps (G.level - 1)) (D.eps G.level / Real.sqrt (D.kap G.level))
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / liftLength D G.level)
      (liftLength D G.level / D.eps (G.level - 1)) (pulseParallel slot.1)
      (pulseShearProfile D.α D.q D.Λ G.level D.ζ (D.kap G.level) slot.1)
      H N K k L (K + 4 * (H + 1) * (N + cap) ^ 2)
      (max k (L + 2) + H * cap + 2 * N + 2 * cap) CG Cw Cj (recordMajorant π G.fam) S
  coeff : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)
  restricted :
    let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
    let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) (liftLength D G.level)
      (G.fam.fiber slot (G.actual slot))
    IsLiftSequence (restrictLiftData cap cap_le {Q with edge := windowEdges a b Q.edge})
      (K + cap + 2) (max (k + 1) (L + 2)) a b N H coeff
  ambient :
    let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
    let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) (liftLength D G.level)
      (G.fam.fiber slot (G.actual slot))
    IsLiftSequence Q (K + cap + 2) (max (k + 1) (L + 2)) a b N H coeff
end

/-! The native degree-zero physical lift is the coarse field at height zero. -/

section
open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_zero_degree_physical_action
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hh : ℕ) (hhh : hh ≤ H)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Φ Ψ : Vec 2 → Vec 2) (x : Vec 2) (hinv : Φ (Ψ x) = x) (e t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    liftApply 0 (slotLift.coeff hh 0) (fun _ Y => f (Φ (liftLength D G.level • Y))) t
      ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x) v =
        if hh = 0 then f x v else 0 := by
  classical
  by_cases hh0 : hh = 0
  · subst hh
    rw [ite_eq_left rfl]
    have heq := liftSequence_zero_degree_action _ _ _ _ _ _ _ _ slotLift.ambient
      (fun _ Y => f (Φ (liftLength D G.level • Y))) t ht
      ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x)
    have hv := congrArg (fun z => z v) heq
    simpa only [smul_smul, mul_inv_cancel₀ slotLift.setting.ρ_pos.ne', one_smul, hinv] using hv
  · rw [ite_eq_right hh0]
    have heq := liftApply_positive_grade_zero_degree _ _ _ _ _ _ _ _ slotLift.ambient hh
      (Nat.one_le_iff_ne_zero.mpr hh0) hhh
      (fun _ Y => f (Φ (liftLength D G.level • Y)))
    exact congrArg (fun z => z t ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x) v) heq
end

/-! The actual native slot lift supplies ambient grading and its fixed mass-conjugated matrix
budget. -/

section
open CycleComparison.Lift EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_coefficient_data
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N + slotLift.cap) :
    AmbientLiftCoefficientData (pulseParallel slot.1)
      (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      slotLift.setting.window (liftLength D G.level / D.eps (G.level - 1)) n
      (ambientDegreeSlowReserve P₀ (N + slotLift.cap) n)
      (ambientDegreeFastReserve (max k (L + 2)) slotLift.cap H (N + slotLift.cap) hh n)
      (slotLift.coeff hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) slotLift.cap H
        (N + slotLift.cap) N hh n CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) := by
  classical
  exact (setting_ambient_scalar_power_recurrence_data slotLift.setting
    (K + slotLift.cap + 2) (max (k + 1) (L + 2)) (by omega)
    slotLift.coeff slotLift.restricted P₀ hreserve hh hhh n hn).coefficient

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
theorem nativeSlotLift_zero_order_eq_zero
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (α : DerivativeWord2 0) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (v u : CompIn G.comps) :
    slotLift.coeff hh n 0 α t X z v u = 0 := by
  exact liftSequence_zero_order_coefficient_zero slotLift.setting (K + slotLift.cap + 2)
    (max (k + 1) (L + 2)) slotLift.coeff slotLift.restricted hh hhh n hn α t ht X z v u

/-- The matrix in this bound is independent of the slot's effective source cap. -/
theorem nativeSlotLift_uniform_coefficient_data
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N) :
    AmbientLiftCoefficientData (pulseParallel slot.1)
      (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      slotLift.setting.window (liftLength D G.level / D.eps (G.level - 1)) n
      (ambientDegreeSlowReserve P₀ (N + slotLift.cap) n)
      (ambientDegreeFastReserve (max k (L + 2)) slotLift.cap H (N + slotLift.cap) hh n)
      (slotLift.coeff hh n)
      (fun v u => nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) := by
  classical
  have hd := nativeSlotLift_coefficient_data slotLift P₀ hreserve hh hhh n (by omega)
  apply hd.enlarge (div_nonneg slotLift.setting.ρ_pos.le slotLift.setting.E_pos.le)
  intro v u
  apply mul_le_mul_of_nonneg_right
    (ambientCoefficientScalarBudget_le_native P₀ (max k (L + 2)) Dm H N CG Cw Cj
      slotLift.cap hh n slotLift.cap_le hhh hn)
  exact finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π (recordMajorant π G.fam) slotLift.setting.envelope.nonneg)
    hh v u

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
theorem nativeSlotLift_uniform_matrix_schur_budget
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S) (hS : 0 ≤ S)
    (P₀ hh : ℕ) :
    HasRealSchurBudget
      (massConjugatedMatrix π (fun v u =>
        nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u))
      (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj * S ^ hh) := by
  classical
  have he : HasRealSchurBudget (recordMajorant π G.fam) S :=
    ⟨slotLift.setting.envelope.nonneg, slotLift.setting.envelope.row_sum,
      slotLift.setting.envelope.col_sum⟩
  have hp := physicalEdgeEnvelopeMatrix_power_schur_budget π slotLift.setting.mass_pos
    (recordMajorant π G.fam) S hS he hh
  convert hp.const_mul (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj)
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _)) using 1
  funext v u
  simp only [massConjugatedMatrix]
  ring
end

/-! The native degree-zero physical lift is the coarse field at height zero. -/

section
open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_positive_degree_expansion
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Φ Ψ : Vec 2 → Vec 2) (x : Vec 2) (hinv : Φ (Ψ x) = x) (c e εc τ : ℝ)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ x v =
      f x v + ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        εc ^ (n + 1) • liftApply (n + 1) (slotLift.coeff hh (n + 1))
          (fun _ Y => f (Φ (liftLength D G.level • Y))) (c⁻¹ * τ)
          ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x) v := by
  rw [pulsePhysicalLift_static_expansion]
  have heq (hh : ℕ) (hhh : hh ∈ Finset.range (H + 1)) :
      (∑ n ∈ Finset.range (N + 1), εc ^ n • liftApply n (slotLift.coeff hh n)
        (fun _ Y => f (Φ (liftLength D G.level • Y))) (c⁻¹ * τ)
        ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x) v) =
      (if hh = 0 then f x v else 0) + ∑ n ∈ Finset.range N,
        εc ^ (n + 1) • liftApply (n + 1) (slotLift.coeff hh (n + 1))
          (fun _ Y => f (Φ (liftLength D G.level • Y))) (c⁻¹ * τ)
          ((liftLength D G.level)⁻¹ • Ψ x) (e⁻¹ • Ψ x) v := by
    rw [Finset.sum_range_succ']
    rw [pow_zero, one_smul, nativeSlotLift_zero_degree_physical_action slotLift hh
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) f Φ Ψ x hinv e (c⁻¹ * τ) ht v]
    exact add_comm _ _
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single 0]
  · exact ite_eq_left rfl
  · intro b _ hb
    exact ite_eq_right hb
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (Nat.zero_lt_succ H)))
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Sum the actual native height matrices before applying their component column budgets. -/

open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_height_matrix_schur_budget
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S) (hS : 0 ≤ S) (P₀ : ℕ) :
    HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => ∑ hh ∈ Finset.range (H + 1),
        nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u))
      (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        ∑ hh ∈ Finset.range (H + 1), S ^ hh) := by
  have hb := finite_sum_real_schur_budget (Finset.range (H + 1))
    (fun hh => massConjugatedMatrix π (fun v u =>
      nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u))
    (fun hh => nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj * S ^ hh)
    (fun hh _ => nativeSlotLift_uniform_matrix_schur_budget slotLift hS P₀ hh)
  have heq : (fun v u => ∑ hh ∈ Finset.range (H + 1),
      massConjugatedMatrix π (fun v u =>
        nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) v u) =
      massConjugatedMatrix π (fun v u => ∑ hh ∈ Finset.range (H + 1),
        nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) := by
    funext v u
    simp only [massConjugatedMatrix, Finset.mul_sum]
  rw [heq] at hb
  simpa only [Finset.mul_sum] using hb

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Extend the odd-slot witnesses to the literal integer-indexed lift, and identify any other witness. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

def nativeStageLiftFamily
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S) :
    ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root) := by
  classical
  exact fun j => if hj : Odd j then (slotLifts ⟨j, hj⟩).coeff else fun _ _ _ _ _ _ _ _ _ => 0

theorem nativeStageLiftFamily_sequence
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (sX sZ : ℕ) (hX : sX ≤ K + 2) (hZ : sZ ≤ max (k + 1) (L + 2))
    (j : ℤ) (hj : Odd j) :
    IsLiftSequence
      (familyLiftData D G.level j (nativeChain G.level j) (liftLength D G.level)
        (G.fam.fiber ⟨j, hj⟩ (G.actual ⟨j, hj⟩))) sX sZ
      (D.slotStart G.level j / D.cellScaleSq G.level)
      ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      N H (nativeStageLiftFamily slotLifts j) := by
  classical
  simp only [nativeStageLiftFamily, dite_eq_left hj]
  exact liftSequence_order_mono _ (by omega) hZ _ _ N H _ (slotLifts ⟨j, hj⟩).ambient

/-- The constructed smooth coefficients identify arbitrary stored orders, including zero. -/
theorem nativeStageLiftFamily_coefficients_unique
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hc : ∀ j : ℤ, ∀ hj : Odd j,
      IsLiftSequence
        (familyLiftData D G.level j (nativeChain G.level j) (liftLength D G.level)
          (G.fam.fiber ⟨j, hj⟩ (G.actual ⟨j, hj⟩))) sX sZ
        (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N H (CcT j))
    (j : ℤ) (hj : Odd j) (hh : ℕ) (hhh : hh ≤ H) (n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
      ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (v u : CompIn G.comps) :
    CcT j hh n m α t X z v u = nativeStageLiftFamily slotLifts j hh n m α t X z v u := by
  classical
  simp only [nativeStageLiftFamily, dite_eq_left hj]
  exact effective_liftSequence_coefficients_unique (slotLifts ⟨j, hj⟩).setting
    sX sZ (K + (slotLifts ⟨j, hj⟩).cap + 2) (max (k + 1) (L + 2))
    (CcT j) (slotLifts ⟨j, hj⟩).coeff (hc j hj) (slotLifts ⟨j, hj⟩).ambient
    hh hhh n m α t ht X z v u
end

/-! Enlarge the stage budget without changing the constructed lift coefficients. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ}
  {H N K k L : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S S' : ℝ}

def NativeSlotLift.raiseBudget
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S) (hSS' : S ≤ S') :
    NativeSlotLift G slot π H N K k L CG Cw Cj S' where
  cap := slotLift.cap
  cap_le := slotLift.cap_le
  cap_ge := slotLift.cap_ge
  empty := slotLift.empty
  setting := { slotLift.setting with
    envelope := { slotLift.setting.envelope with
      row_sum := fun v => (slotLift.setting.envelope.row_sum v).trans hSS'
      col_sum := fun u => (slotLift.setting.envelope.col_sum u).trans hSS' } }
  coeff := slotLift.coeff
  restricted := slotLift.restricted
  ambient := slotLift.ambient

theorem nativeStageLiftFamily_raiseBudget
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hSS' : S ≤ S') :
    nativeStageLiftFamily (fun slot => (slotLifts slot).raiseBudget hSS') =
      nativeStageLiftFamily slotLifts := rfl
end

/-! The actual native action on a chart pullback is bounded by physical jets at the original point. -/

section
open CycleComparison.Lift FastJets
section GeneralPositiveChart
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Ordinary chart action at arbitrary radii, from the actual coefficient data. -/
theorem chart_mixed_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (γ δ : List (Fin 2)) (hγ : γ.length ≤ P₀) (hδ : δ.length ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) (t : ℝ) (ht : t ∈ Set.Icc a b)

    (z : Vec 2) (v : ι) :
    ‖mixL γ δ (fun Y w => liftApply n cc (fun _ Y' => f (Φ (ρ • Y'))) t Y w v)
      (ρ⁻¹ • y) z‖ ≤
      (finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length)) * ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((γ.length + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hγ hn)
  have hb := norm_mixL_liftApply_le_local_jets γ δ (data.mono hγ hδ)
    hlam hlam1 g hg t ht (ρ⁻¹ • y) z v
  have hinput (u : ι) := chart_dilated_input_finite_density_bound (fun X => f X u)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := hv) u).contDiff.comp hf)
    Φ hΦ hC hρ hJ y x hΦy (γ.length + n) (Nat.add_le_add hγ hn)
  apply hb.trans
  calc
    _ ≤ (finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length)) *
        (∑ u, M v u * (ChartTransport.compConst C (P₀ + N) *
          ∑ j ∈ Finset.range (P₀ + N + 1), ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (finiteLiftWordCount_nonneg n) (pow_nonneg (by norm_num) _))
      exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hinput u) (data.nonneg v u)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Positive mixed chart action at an arbitrary slow radius, from the actual coefficient data. -/
theorem positive_chart_mixed_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (γ δ : List (Fin 2)) (hγ : γ.length ≤ P₀) (hδ : δ.length ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, cc 0 α t X z v u = 0)
    (z : Vec 2) (v : ι) :
    ‖mixL γ δ (fun Y w => liftApply n cc (fun _ Y' => f (Φ (ρ • Y'))) t Y w v)
      (ρ⁻¹ • y) z‖ ≤
      (finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length)) * ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((γ.length + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hγ hn)
  have hb := norm_mixL_positive_liftApply_le_local_jets γ δ (data.mono hγ hδ)
    hlam hlam1 g hg t ht hzero (ρ⁻¹ • y) z v
  have hinput (u : ι) := positive_chart_dilated_input_finite_density_bound (fun X => f X u)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := hv) u).contDiff.comp hf)
    Φ hΦ hC hρ hJ y x hΦy (γ.length + n) (Nat.add_le_add hγ hn)
  apply hb.trans
  calc
    _ ≤ (finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length)) *
        (∑ u, M v u * (ChartTransport.compConst C (P₀ + N) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (finiteLiftWordCount_nonneg n) (pow_nonneg (by norm_num) _))
      exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hinput u) (data.nonneg v u)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc, mul_left_comm]

end GeneralPositiveChart
end

/-! Pointwise diagonal words of the native chart action preserve the exact input reserve. -/

section
open CycleComparison.Lift FastJets
section GeneralPositiveDiagonal
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Ordinary chart action at arbitrary radii, from the actual coefficient data. -/
theorem chart_diagonal_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ r) (y x : Vec 2) (hΦy : Φ y = x)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
 (v : ι) :
    rs ^ l.length * ‖odL l (fun Y => liftApply n cc (fun _ Y' => f (Φ (ρ • Y')))
      t (ρ⁻¹ • Y) (e⁻¹ • Y) v) y‖ ≤
      (∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
        2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
        ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hrP hn)
  have hmono := data.mono hrP hrQ
  have hbox := liftApply_component_box_reserve n r r cc (fun _ => g) t v hg
    (fun m hm α u => hmono.box m hm α v u t ht)
  apply (norm_rs_odL_diagonal_le hbox hrs hrse heρ l
    (by simpa only [min_self] using hl) y).trans
  calc
    _ ≤ ∑ i : Fin (splitTerms l).length,
        (finiteLiftWordCount n *
          2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
        ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := splitTerms_length_sum l ((splitTerms l).get i) (List.get_mem _ _)
      exact chart_mixed_word_bound_of_data data hlam hlam1 hn
        ((splitTerms l).get i).1 ((splitTerms l).get i).2 (by omega) (by omega)
        f hf Φ hΦ hC (hrs.trans_le (hrse.trans heρ)) hJ y x hΦy t ht (e⁻¹ • y) v
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

/-- Radius-generic positive diagonal action with the fixed original coefficient matrix. -/
theorem positive_chart_diagonal_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ r) (y x : Vec 2) (hΦy : Φ y = x)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, cc 0 α t X z v u = 0) (v : ι) :
    rs ^ l.length * ‖odL l (fun Y => liftApply n cc (fun _ Y' => f (Φ (ρ • Y')))
      t (ρ⁻¹ • Y) (e⁻¹ • Y) v) y‖ ≤
      (∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
        2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
        ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hrP hn)
  have hmono := data.mono hrP hrQ
  have hbox := liftApply_component_box_reserve n r r cc (fun _ => g) t v hg
    (fun m hm α u => hmono.box m hm α v u t ht)
  apply (norm_rs_odL_diagonal_le hbox hrs hrse heρ l
    (by simpa only [min_self] using hl) y).trans
  calc
    _ ≤ ∑ i : Fin (splitTerms l).length,
        (finiteLiftWordCount n *
          2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
        ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := splitTerms_length_sum l ((splitTerms l).get i) (List.get_mem _ _)
      exact positive_chart_mixed_word_bound_of_data data hlam hlam1 hn
        ((splitTerms l).get i).1 ((splitTerms l).get i).2 (by omega) (by omega)
        f hf Φ hΦ hC (hrs.trans_le (hrse.trans heρ)) hJ y x hΦy t ht hzero (e⁻¹ • y) v
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end GeneralPositiveDiagonal

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_positive_chart_diagonal_word_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (l : List (Fin 2)) (hl : l.length ≤ r)
    (y x : Vec 2) (hΦy : Φ y = x) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    rs ^ l.length * ‖odL l (fun Y => liftApply n (slotLift.coeff hh n)
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
      ((liftLength D G.level)⁻¹ • Y) (e⁻¹ • Y) v) y‖ ≤
      (∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
        2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
      ChartTransport.compConst C (P₀ + N) *
        (∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else (liftLength D G.level) ^ j *
            ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  have hd := nativeSlotLift_uniform_coefficient_data slotLift P₀ hreserve hh hhh n hn
  have hmono := hd.mono
    (show P₀ ≤ ambientDegreeSlowReserve P₀ (N + slotLift.cap) n by
      unfold ambientDegreeSlowReserve; omega)
    (show max k (L + 2) ≤ ambientDegreeFastReserve (max k (L + 2)) slotLift.cap H
        (N + slotLift.cap) hh n by unfold ambientDegreeFastReserve; omega)
  exact positive_chart_diagonal_word_bound_of_data hmono
    (div_nonneg slotLift.setting.ρ_pos.le slotLift.setting.E_pos.le) slotLift.setting.lam_le hn
    r hrP hrQ f hf Φ hΦ hC hJ hrs hrse heρ l hl y x hΦy t ht
    (fun α X z v u => nativeSlotLift_zero_order_eq_zero slotLift hh hhh n hn0 α t ht X z v u) v
end

/-! A finite chart-transport constant contains no stage, slot, carrier or input data. -/

section
open FastJets CycleComparison.Lift

def nativeChartTransportConstant (C : ℝ) (U n r : ℕ) : ℝ :=
  ChartTransport.compConst C r *
    (∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
      ∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
        2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
          2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
    ChartTransport.compConst C U

theorem nativeChartTransportConstant_nonneg {C : ℝ} (hC : 1 ≤ C) (U n r : ℕ) :
    0 ≤ nativeChartTransportConstant C U n r := by
  exact mul_nonneg (mul_nonneg (ChartTransport.compConst_nonneg hC r)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => mul_nonneg (finiteLiftWordCount_nonneg n)
        (pow_nonneg (by norm_num) _)))))) (ChartTransport.compConst_nonneg hC U)
end

/-! Pointwise diagonal words of the native chart action preserve the exact input reserve. -/

section
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_positive_chart_diagonal_gradient_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (l : List (Fin 2)) (hl0 : 1 ≤ l.length) (hl : l.length ≤ r)
    (y x : Vec 2) (hΦy : Φ y = x) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    rs ^ (l.length - 1) * ‖odL l (fun Y => liftApply n (slotLift.coeff hh n)
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
      ((liftLength D G.level)⁻¹ • Y) (e⁻¹ • Y) v) y‖ ≤
      e⁻¹ * ((∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
        2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
      ChartTransport.compConst C (P₀ + N) *
        (∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else (liftLength D G.level) ^ j *
            ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
  have he : 0 < e := hrs.trans_le hrse
  have hb := nativeSlotLift_positive_chart_diagonal_word_bound slotLift P₀ hreserve
    hh hhh n hn0 hn r hrP hrQ f hf Φ hΦ hC hJ he le_rfl heρ l hl y x hΦy t ht v
  exact pred_weight_le_of_weight_le hrs hrse hl0 (norm_nonneg _) hb
end

/-! Pointwise diagonal words of the native chart action preserve the exact input reserve. -/

section
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_positive_chart_diagonal_dissipation_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B εc : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    (l : List (Fin 2)) (hl0 : 1 ≤ l.length) (hl : l.length ≤ r)
    (y x : Vec 2) (hΦy : Φ y = x) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * εc ^ n * (rs ^ (l.length - 1) * ‖odL l (fun Y => liftApply n (slotLift.coeff hh n)
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
      ((liftLength D G.level)⁻¹ • Y) (e⁻¹ • Y) v) y‖) ≤
      Real.sqrt B * ((∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
        2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
      ChartTransport.compConst C (P₀ + N) *
        (∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else (liftLength D G.level) ^ (j - 1) *
            ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
  have he : 0 < e := hrs.trans_le hrse
  have hρ := slotLift.setting.ρ_pos
  let Kprice : ℝ := (∑ i : Fin (splitTerms l).length, finiteLiftWordCount n *
    2 ^ (((splitTerms l).get i).1.length + 2 * ((splitTerms l).get i).2.length)) *
    ChartTransport.compConst C (P₀ + N)
  have hK : 0 ≤ Kprice := mul_nonneg
    (Finset.sum_nonneg fun _ _ => mul_nonneg (finiteLiftWordCount_nonneg n) (pow_nonneg (by norm_num) _))
    (ChartTransport.compConst_nonneg hC _)
  have hd := nativeSlotLift_uniform_coefficient_data slotLift P₀ hreserve hh hhh n hn
  have hp := matrix_positive_jet_density_fast_price_le hν hB he hρ hc hε0 hε1 hn0
    (P₀ + N) _ (hd.nonneg v) (fun u j => ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)
    (fun _ _ => norm_nonneg _)
  have hb := nativeSlotLift_positive_chart_diagonal_gradient_bound slotLift P₀ hreserve
    hh hhh n hn0 hn r hrP hrQ f hf Φ hΦ hC hJ hrs hrse heρ l hl0 hl y x hΦy t ht v
  have hb' := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Real.sqrt_nonneg ν) (pow_nonneg hε0 n))
  apply hb'.trans
  change Real.sqrt ν * εc ^ n * (e⁻¹ * (Kprice * _)) ≤ Real.sqrt B * (Kprice * _)
  calc
    _ = Kprice * (Real.sqrt ν * (εc ^ n / e) * _) := by ring
    _ ≤ Kprice * (Real.sqrt B * _) := mul_le_mul_of_nonneg_left hp hK
    _ = _ := by ring
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniqueness transfers the actual native metric and source lattice to every lift coefficient. -/

open CycleComparison.LiftMeanEntrywise EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_coefficient_slow_shift
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (p : Fin 2 → ℤ) (hh : ℕ) (hhh : hh ≤ H) (n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (v u : CompIn G.comps) :
    slotLift.coeff hh n m α t (X + (liftLength D G.level)⁻¹ • latticeShift p) z v u =
      slotLift.coeff hh n m α t X z v u := by
  apply setting_liftSequence_slowShift_invariant slotLift.setting
    (K + slotLift.cap + 2) (max (k + 1) (L + 2)) slotLift.coeff slotLift.restricted
    ((liftLength D G.level)⁻¹ • latticeShift p) ?_ ?_ hh hhh n m α t ht X z v u
  · intro s Y i j
    exact congrFun (congrFun (native_familyLiftData_metric_shift D G.level hi slot.1
      slotLift.setting.ρ_pos.ne' (G.fam.fiber slot (G.actual slot)) p s Y) i) j
  · intro v' u' d γ hγ β s Y w
    let d' : Finset.Icc 2 Dm := ⟨d.1, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.2).1, (Finset.mem_Icc.mp d.2).2.trans slotLift.cap_le⟩⟩
    change γ ∈ windowEdges
      (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      (familyLiftData D G.level slot.1 (nativeChain G.level slot.1) (liftLength D G.level)
        (G.fam.fiber slot (G.actual slot))).edge v' u' d' at hγ
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
    exact native_familyLiftData_edge_coeff_shift G htorus slot slotLift.setting.ρ_pos.ne'
      p v' u' _ δ hδ β _ Y w

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVenhance.Infra.Flow AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual native pulse maps periodic coarse data to periodic physical fields. -/

theorem native_flow_latticeShift (D : OCData) (i : ℕ) (s t : ℝ)
    (p : Fin 2 → ℤ) (x : Vec 2) :
    D.flowOf i s (x + latticeShift p) t = D.flowOf i s x t + latticeShift p := by
  have hφ := D.hΦ i
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hp : ∀ r, IsZ2Periodic (streamVel (D.Φ i) r) := by
    intro r k y
    simpa using hb.periodic 0 k r y
  exact flow_lattice_equivariant _ hφ.vel_lipschitz hp
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz) x t s p

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_periodic
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (c εc τ : ℝ) (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : IsZ2Periodic f)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    IsZ2Periodic (pulsePhysicalLift c (liftLength D G.level) (D.eps G.level) εc N H slotLift.coeff
      (fun _ y => D.flowOf (G.level - 1) τ y (D.slotAnchor G.level slot.1))
      (fun _ y => D.flowOf (G.level - 1) (D.slotAnchor G.level slot.1) y τ)
      (fun _ => f) τ) := by
  obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ G.level
  apply pulsePhysicalLift_static_periodic c (liftLength D G.level) (D.eps G.level) εc N H
    slotLift.coeff _ _ f τ slotLift.setting.ρ_pos.ne' hJ
    (fun p Y => native_flow_latticeShift D _ _ _ p Y)
    (fun p Y => native_flow_latticeShift D _ _ _ p Y) hf
  · intro hh hhh n _hn m _hm α p X z v u
    exact nativeSlotLift_coefficient_slow_shift slotLift hi htorus p hh hhh n m α
      (c⁻¹ * τ) ht X z v u
  · intro hh hhh n _hn m _hm α X v u
    exact (slotLift.ambient.2.2.2.2.2.1 hh hhh n m α v u (c⁻¹ * τ) ht).2 X

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Time-local native pulses glue to a periodic physical field on the original observation window. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_periodic
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (ha : IsZ2Periodic (a τ))
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    IsZ2Periodic (gluedLift kset ϖ c (liftLength D G.level) (D.eps G.level) εc N H
      (nativeStageLiftFamily slotLifts)
      (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
      (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a τ) := by
  classical
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  intro p x
  simp only [gluedLift]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hw : ϖ j τ = 0
  · simp only [hw, zero_smul]
  · apply congrArg (fun y => ϖ j τ • y)
    simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
    rw [pulsePhysicalLift_freeze_time, pulsePhysicalLift_freeze_time, hclock]
    exact nativeSlotLift_pulse_periodic (slotLifts ⟨j, hodd j hj⟩) hi htorus
      c εc τ (a τ) ha (ht j hj hw) p x

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Spatial regularity of the actual native chart action at its exact input reserve. -/

open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_chart_diagonal_contDiff
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    (e t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    ContDiff ℝ (r : ℕ∞) (fun Y => liftApply n (slotLift.coeff hh n)
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
      ((liftLength D G.level)⁻¹ • Y) (e⁻¹ • Y) v) := by
  let g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
    fun Y => f (Φ (liftLength D G.level • Y))
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hrP hn)
  have hd := nativeSlotLift_uniform_coefficient_data slotLift P₀ hreserve hh hhh n hn
  have hmono := hd.mono
    (show r ≤ ambientDegreeSlowReserve P₀ (N + slotLift.cap) n by
      unfold ambientDegreeSlowReserve; omega)
    (show r ≤ ambientDegreeFastReserve (max k (L + 2)) slotLift.cap H
        (N + slotLift.cap) hh n by unfold ambientDegreeFastReserve; omega)
  have hbox := liftApply_component_box_reserve n r r (slotLift.coeff hh n) (fun _ => g) t v hg
    (fun m hm α u => hmono.box m hm α v u t ht)
  exact CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl (liftLength D G.level) e

end AVRegularity.Construction.Preservation.FullLift
end
