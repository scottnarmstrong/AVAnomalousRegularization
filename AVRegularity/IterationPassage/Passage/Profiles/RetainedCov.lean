-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Passage.Profiles.RetainedLiftStage
import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The discarded lift profile at one stage** (step `DiscDeStep`).

* `discDe_profile_norm_le`: abstract packing. If the scaled jets of `F` are bounded pointwise by
  `C_P ε Y_in(x)` with `0 ≤ ε ≤ 1` (the positive bound of the lift, `ε = d_*/ρ_L`) and
  `Y_in ≤ B`, then `𝓘_{e,K;s}(F) ≤ #jets · C_P e^{-s} B` (`profile_jet_packing`).
* `discardedLift_at_stage`: for the slot lifts of a stage and a field `g t` whose positive jets
  at the lift radius are bounded by `B`,
  `𝓘_{e,K;s}(F[(T - I)g]) ≤ C e^{-s} B` (`passageLift_positive_partial_bound`).

No comparison of `e` with the radius is needed beyond `e ≤ ρ_L`, which the slot lifts give.

Special cases: `B = 0` (the input is constant, the profile vanishes); `K = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison.Lift
  AVRegularity.Finite AVRegularity.Finite.WeakLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The profile norm from the pointwise positive bound with a bounded input. -/
theorem discDe_profile_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e ε CP B s : ℝ} {K : ℕ} (F : Vec 2 → H) (Yin : Vec 2 → ℝ) (he : 0 < e) (hCP : 0 ≤ CP)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hP : ∀ β : Fin 2 → ℕ, β 0 + β 1 ≤ K → ∀ x,
      e ^ (β 0 + β 1) * ‖partialDerivative β F x‖ ≤ CP * ε * Yin x)
    (hY : ∀ x, Yin x ≤ B) :
    profileNorm e K s F ≤
      (profileJetCount K : ℝ≥0∞) * ENNReal.ofReal (CP * (e ^ (-s) * B)) := by
  have hes : 0 ≤ e ^ (-s) := Real.rpow_nonneg he.le _
  have hpoint : ∀ (b : ℕ) (n : ℝ) (x : Vec 2), e ^ b * n ≤ CP * ε * Yin x →
      ENNReal.ofReal (e ^ ((b : ℝ) - s)) * ENNReal.ofReal n ≤
        ENNReal.ofReal (CP * (e ^ (-s) * B)) := by
    intro b n x h
    have hsplit : e ^ ((b : ℝ) - s) = e ^ (-s) * e ^ b := by
      rw [sub_eq_add_neg, Real.rpow_add he, Real.rpow_natCast]
      ring
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg he.le _), hsplit, mul_assoc]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : CP * ε * Yin x ≤ CP * ε * B :=
      mul_le_mul_of_nonneg_left (hY x) (mul_nonneg hCP hε0)
    have h2 : CP * ε * B ≤ CP * 1 * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε1 hCP) hB
    calc e ^ (-s) * (e ^ b * n) ≤ e ^ (-s) * (CP * 1 * B) :=
          mul_le_mul_of_nonneg_left (h.trans (h1.trans h2)) hes
      _ = CP * (e ^ (-s) * B) := by ring
  refine profile_jet_packing (H := H) e s K K F _ he le_rfl ⟨?_, ?_⟩
  · refine retCov_sup_le _ _ _ fun x => ?_
    have h0 : partialDerivative (![0, 0] : Fin 2 → ℕ) F = F := by
      rw [← weakPositive_sorted_word_eq_partial 0 0 F]
      exact retCov_zero_word F _
    have hP0 : e ^ 0 * ‖F x‖ ≤ CP * ε * Yin x := by
      have h := hP ![0, 0] (Nat.zero_le K) x
      rw [h0] at h
      exact h
    have h := hpoint 0 ‖F x‖ x hP0
    simpa only [Nat.cast_zero, zero_sub] using h
  · intro a ha
    have hj : a 0 + a 1 ≤ K := (Finset.mem_filter.mp ha).2.2
    refine retCov_sup_le _ _ _ fun x => ?_
    exact hpoint (a 0 + a 1) _ x (hP a hj x)

/-- The constant of the discarded lift profile at a stage. -/
def discDeProfileConst (Cχ : ℝ) (K Q Dm H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Sb : ℝ) : ℝ :=
  (profileJetCount K : ℝ) * ((∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r) *
    liftPositiveCost K Q Dm H N CG Cw Cj Sb)

theorem discDeProfileConst_nonneg {Cχ : ℝ} (hCχ : 1 ≤ Cχ) (K Q Dm H N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) {Sb : ℝ} (hSb : 0 ≤ Sb) :
    0 ≤ discDeProfileConst Cχ K Q Dm H N CG Cw Cj Sb :=
  mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (Finset.sum_nonneg fun r _ => liftPositivePrice_nonneg hCχ K N r)
    (liftPositiveCost_nonneg _ _ _ _ _ _ _ _ hSb))

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N Kp k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- **The discarded lift profile at a stage**, with the bound of the input as a hypothesis. -/
theorem discardedLift_at_stage
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N Kp k L CG Cw Cj S)
    {Sb : ℝ} (hS : 0 ≤ S) (hSb : S ≤ Sb) (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hterm : G.level ≤ D.term)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (K : ℕ) (hreserve : ∀ slot : OddSlot, K + (N + (slotLifts slot).cap) ≤
      Kp + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hKQ : K ≤ max k (L + 2)) {Cχ : ℝ} (hCχ : 1 ≤ Cχ) (t : ℝ)
    (hJ : ∀ j : ℤ, Odd j → ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (K + N) Cχ (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (K + N) Cχ (liftLength D G.level))
    (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (hg : ContDiff ℝ ((K + N : ℕ) : ℕ∞) (g t)) (hgp : IsZ2Periodic (g t))
    {s B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x, ∑ γ ∈ multiIndicesBetween 1 (K + N),
        liftLength D G.level ^ (γ 0 + γ 1) * ‖partialDerivative γ (compField π (g t)) x‖ ≤ B) :
    profileNorm (D.eps G.level) K s (compField π
        (fun y => passageLift D G.level N H CcT g t y - g t y)) ≤
      ENNReal.ofReal (discDeProfileConst Cχ K (max k (L + 2)) Dm H N CG Cw Cj Sb *
        (D.eps G.level ^ (-s) * B)) := by
  have he : 0 < D.eps G.level := (slotLifts ⟨1, by decide⟩).setting.e_pos
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hkap : D.kap G.level = D.κ G.level := by
    simp only [OCData.kap, Nat.min_eq_left hterm]
  have hprev : D.kap (G.level - 1) = D.κ (G.level - 1) := by
    simp only [OCData.kap, Nat.min_eq_left ((Nat.sub_le G.level 1).trans hterm)]
  have hε1 : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1 := by
    simpa only [hkap, hprev] using (slotLifts ⟨1, by decide⟩).setting.εc_le
  have hε : 0 ≤ ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level := div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) hρ.le
  have hprice : 0 ≤ ∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r :=
    Finset.sum_nonneg fun r _ => liftPositivePrice_nonneg hCχ K N r
  have hcost := liftPositiveCost_mono K (max k (L + 2)) Dm H N CG Cw Cj hS hSb
  have hCP : 0 ≤ (∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r) *
      liftPositiveCost K (max k (L + 2)) Dm H N CG Cw Cj Sb :=
    mul_nonneg hprice (liftPositiveCost_nonneg _ _ _ _ _ _ _ _ (hS.trans hSb))
  have hmain := discDe_profile_norm_le (s := s) (K := K)
    (compField π (fun y => passageLift D G.level N H CcT g t y - g t y))
    (fun x => ∑ γ ∈ multiIndicesBetween 1 (K + N), liftLength D G.level ^ (γ 0 + γ 1) *
      ‖partialDerivative γ (compField π (g t)) x‖) he hCP hε hε1 hB
    (fun β hβ x => (passageLift_positive_partial_bound slotLifts hS hi hΛ hζ hband hterm htorus
      K hreserve hKQ hCχ t hJ sX sZ CcT hCcT g hg hgp β hβ x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcost hprice) hε)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hρ.le _) (norm_nonneg _))))
    hY
  refine hmain.trans_eq ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  unfold discDeProfileConst
  ring

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **Moment cancellation on a weighted family** (the first step of the discarded profiles).

`discMoment : DiscMomentStatement`: for each component the value jet of `Y_v` determines the
classical representative `a_v` (continuous, periodic, equal a.e. to the Sobolev representative of
order `k + L`); `kernelDefect` (components are `ℝ`) gives a realization of `a_v - S a_v` of norm
`C (r/ρ)^L |Y_v|_{ρ,k+L}`, and the masses are summed. The kernel commutes with the component
projection (`retCov_kernel_clm_comm`).

Special cases: empty family; `L = 0`; `Y = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Construction.KernelDefect
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.IterationPassage.Passage

/-- Weighted norm of a family of realizations from the componentwise bounds. -/
theorem discMoment_sum {S' : Finset Comp} {k M : ℕ} (π' : CompIn S' → ℝ) (ρ c : ℝ)
    (W : ∀ v : CompIn S', TorusHk k (ScalarH v.1.root))
    (Y : ∀ v : CompIn S', TorusHk M (ScalarH v.1.root)) (hπ : ∀ v, 0 < π' v) (hc : 0 ≤ c)
    (h : ∀ v, factorialNormSq ρ (W v).val ≤ c ^ 2 * factorialNormSq ρ (Y v).val) :
    weightedNorm ρ π' (fun _ => 1) W ≤ c * weightedNorm ρ π' (fun _ => 1) Y := by
  unfold weightedNorm massNormSq
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hp : 0 ≤ (π' v / 1 ^ 2)⁻¹ := by have := hπ v; positivity
  calc (π' v / 1 ^ 2)⁻¹ * factorialNormSq ρ (W v).val
      ≤ (π' v / 1 ^ 2)⁻¹ * (c ^ 2 * factorialNormSq ρ (Y v).val) :=
        mul_le_mul_of_nonneg_left (h v) hp
    _ = _ := by ring

/-- The classical representative of a component: the value jet and a continuous periodic function
determine it. -/
theorem discMoment_rep {M r : ℕ} (hr : r + 2 ≤ M) (Y : TorusHk M ℝ) (a : Vec 2 → ℝ)
    (hac : Continuous a) (hap : IsZ2Periodic a)
    (hY : Y.toFunction.jet (valueIndex2 M) =ᵐ[volume.restrict AVenhance.unitCube] a) :
    IsClassicalRep Y a r := by
  obtain ⟨a', ha'⟩ := hilbert_classicalRep_exists M r hr Y
  have hae : a' =ᵐ[volume.restrict AVenhance.unitCube] a :=
    (CycleComparison.Reconstruction.classicalRep_value_ae ha').trans
      ((KernelEnergy.torusHk_toFunction_jet_ae Y _).symm.trans hY)
  have heq : a' = a := CycleComparison.Lift.periodicContinuous_eq_of_cell_ae a' a
    ha'.2.1.continuous hac ha'.2.2.1 hap hae
  exact heq ▸ ha'

theorem discMoment : DiscMomentStatement := by
  intro φ₀ hφ₀ hφs hφpos hφint hφsupp k L n Γ
  obtain ⟨C, hC, hkd⟩ := kernelDefect (E := ℝ) φ₀ hφ₀ hφs hφpos hφint hφsupp k L n Γ
  refine ⟨C, hC, ?_⟩
  intro S' π' hπ' Sr t ρ hord hadm hw hwρ M hM Yn a hac hap hYn
  have hρ0 : 0 < ρ := lt_of_lt_of_le hw hwρ
  have hcomp : ∀ v : CompIn S', ∃ w : TorusHk k ℝ,
      IsClassicalRep w (fun x => (a x - Sr.applyClassical φ₀ t a x) v) k ∧
      factorialNormSq ρ w.val ≤ (C * (Sr.width / ρ) ^ L) ^ 2 * factorialNormSq ρ (Yn v).val := by
    intro v
    have hav : Continuous fun x => a x v := (continuous_apply v).comp hac
    have hapv : IsZ2Periodic fun x => a x v := fun n x => congrFun (hap n x) v
    have hrep := discMoment_rep (r := k + L) (by omega) (Yn v) _ hav hapv (hYn v)
    have hrep' := classicalRep_truncate (by omega : k + L ≤ M) le_rfl (Yn v) _ hrep
    obtain ⟨w, hw1, hw2⟩ := hkd Sr t ρ hord hadm hw hwρ _ (fun x => a x v) hrep'
    refine ⟨w, ?_, hw2.trans ?_⟩
    · convert hw1 using 2
      rename_i y
      have := retCov_kernel_clm_comm hφs hφsupp Sr t (ContinuousLinearMap.proj v) hac hap y
      simp only [ContinuousLinearMap.proj_apply] at this
      simp only [Pi.sub_apply]
      rw [this]
    · exact mul_le_mul_of_nonneg_left (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ _)
        (sq_nonneg _)
  choose W hW1 hW2 using hcomp
  refine ⟨W, hW1, ?_⟩
  exact discMoment_sum π' ρ _ W Yn hπ' (mul_nonneg hC (pow_nonneg (div_nonneg hw.le hρ0.le) _)) hW2

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **Regularity of the five profiles and the exact split**.

`passageProfilesRegular`: the prefix of `iteration_passage` through the carrier start, then the
level threshold `m_* = max m₀ j₀` (`m₀` from the native slot lifts). For the data of a passage
`m → m-1` and fields `aU t`, `aY t` of class `C^{K+N+2p+2}`, periodic, at a time `t`:

* `regularProfiles_regular`: the five fields are `C^K` and periodic; the lift is regular by
  `regularLift_contDiff_periodic`, whose native slot lifts of the incoming stage come from
  `uniform_native_weighted_slot_lifts`, with the stage geometry (reserves, record lengths, depth)
  from the stage invariant and `uniform_cascade_record_length`;
* `regularProfiles_split`: the exact split.

The hypotheses on `K, Pacc, L`, the widths and the thresholds `SX, SZ, Kneed` (taken `0`) are not
used. Special cases: empty family; `p = 0`; `aY t = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.Construction.Preservation

namespace AVRegularity.IterationPassage.Passage

/-- **Regularity of the profiles and the split identity**. -/
theorem passageProfilesRegular (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageProfilesRegularStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hlift⟩ := uniform_native_weighted_slot_lifts hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λa Λl, by omega, ?_⟩
  intro Λ hΛ
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hQb
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched
    hNaux hNout L hL hwid
  refine ⟨0, 0, 0, ?_⟩
  intro sX sZ _ _ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hN2, _, _⟩ := hsched
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := Buffer.preparation_schedule_order_ge_two D₀ N p H
  obtain ⟨CG, Cw', Cj, m₀, hm₀, hpk⟩ := hlift Λ (by omega) bw hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N ((K + 2) + N + succSchedD D₀ N p (H + 1)) K 0 hDm (by omega)
  refine ⟨max m₀ j₀, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hmol m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual CcT hCcT
    aU aY t hts htf haU haUp haY haYp
  subst hlevel
  have hm₀' : m₀ ≤ G.level := (le_max_left _ _).trans hm
  have hj₀ : j₀ ≤ G.level := (le_max_right _ _).trans hm
  have hi : 1 ≤ G.level := by omega
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hΛD : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hcr1 : kI.cr ≤ 1 := by
    rw [(Buffer.invariantAdmissible_molecular_parameters hkI).2.1]
    exact hcrupper
  have hprod : kI.Hprod = kI.G0 + H + 1 := (Buffer.invariantAdmissible_molecular_parameters hkI).2.2
  have hprod' : kI.Hprod =
      kI.G0 + (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)).H + 1 := hprod
  have hmG v : 0 ≤ compReserve kI (v : CompIn G.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcascade kI hprod' v).le
  have hm2G v : compReserve kI (v : CompIn G.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength ScalarH D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) Cw kI.cr σ₀
    (succEta0 α q s) N p hcr1 seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade hi
  have hdepth := Providers.CascadeInvariants.cascade_depth_of_generatedSeed hseed hcascade
  have hlt : G.level < D.term := by rw [hterm]; omega
  have hpk' := hpk ScalarH D hDα hDq hDΛ hDζ hseq hbandD j₀ G law _ seedK freshK φ₀ hφ₀ Mnat kI
    tA tf _ _ hG hm₀' hlt hj₀ hdepth hmG hm2G hlenG (fun _ => 1) (Or.inl rfl)
  have slotLifts := fun slot => Classical.choice (hpk' slot)
  have htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) := hG.isTorusCompatible
  have hT' : ∀ a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root,
      ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (a t) → IsZ2Periodic (a t) →
      ContDiff ℝ (K : ℕ∞) (passageLift D G.level N (succSchedR r₀ J H) CcT a t) ∧
        IsZ2Periodic (passageLift D G.level N (succSchedR r₀ J H) CcT a t) := by
    intro a ha hp
    refine regularLift_contDiff_periodic slotLifts hi hΛD hζD hbandD htorus (K + 2) ?_ K
      (by omega) (le_max_left _ _) sX sZ CcT hCcT a t ha hp
    intro slot
    have hcap := (slotLifts slot).cap_le
    exact le_trans (by omega : K + 2 + (N + (slotLifts slot).cap) ≤
      K + 2 + N + succSchedD D₀ N p (H + 1)) (Nat.le_add_right _ _)
  have hc : D.cellScaleSq G.level ≠ 0 :=
    (EntryWeakProofs.weakData_cellScaleSq_pos D hΛD hζD hbandD G.level).ne'
  have hπ' : ∀ v, 0 < (G'.retained G.level H J).mass law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have hS : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (fieldKernel φ₀ (freshK (G.level - 1)) aY t) ∧
      IsZ2Periodic (fieldKernel φ₀ (freshK (G.level - 1)) aY t) :=
    regularKernel_contDiff_periodic hφsmooth hφsupport _ t haY haYp
  have haY0 : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aY t) := haY
  have haY' : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) (aY t) :=
    haY0.of_le (by exact_mod_cast (by omega : N + 2 * p ≤ K + N + 2 * p + 2))
  have hS' : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) (fieldKernel φ₀ (freshK (G.level - 1)) aY t) :=
    hS.1.of_le (by exact_mod_cast (by omega : N + 2 * p ≤ K + N + 2 * p + 2))
  refine ⟨regularProfiles_regular hφsmooth hφsupport law G (G'.retained G.level H J) G.level p N
    (succSchedR r₀ J H) K (succEta0 α q s) (freshK (G.level - 1)) CcT aU aY t haU haUp haY haYp hT',
    regularProfiles_split law G (G'.retained G.level H J) G.level p N (succSchedR r₀ J H)
    (succEta0 α q s) (freshK (G.level - 1)) CcT aU aY t hc hπ' haY' hS'⟩

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The retained covariance profile as a field in `CompSpace`**

`retCov_profile_field_eq`: the normalized profile field
`x ↦ F(𝖱(P_p - I)S_r aY)(t)(x)` equals `(𝒫_p - I)(R ∘ g)` for `g = S_r (F' aY(t))` and
`R = readoutCLM`, and so its profile norm is bounded by `retCov_profile_norm`.

Special cases: `p = 0` (the field is `0`); `aY t = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Finite
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The profile field is `(𝒫_p - I)(R ∘ g)`. -/
theorem retCov_profile_field_eq (D : OCData) (m p : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ' : ∀ v', 0 < π' v')
    {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (Sr : KernelSpec)
    (aY : ℝ → Vec 2 → ∀ v : CompIn S', ScalarH v.1.root) (t : ℝ)
    (haY : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (aY t)) (hp : IsZ2Periodic (aY t)) :
    compField π (fieldReadout (S := S) m E η₀
        (fieldCov D m p (fieldKernel φ₀ Sr aY) - fieldKernel φ₀ Sr aY) t) =
      covPolyP (covPrimitive D m t) p
          (fun y => readoutCLM m E η₀ π π' (Sr.applyClassical φ₀ t (compField π' (aY t)) y)) -
        fun y => readoutCLM m E η₀ π π' (Sr.applyClassical φ₀ t (compField π' (aY t)) y) := by
  have hS := regularKernel_contDiff_periodic hφs hφsupp Sr t haY hp
  have hS2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fieldKernel φ₀ Sr aY t) := by
    have := regularKernel_contDiff_periodic hφs hφsupp Sr t haY hp
    exact this.1
  have hg : Sr.applyClassical φ₀ t (compField π' (aY t)) = compField π' (fieldKernel φ₀ Sr aY t) :=
    (retCov_compField_kernel hφs hφsupp Sr t π' haY.continuous hp).symm
  have hgc : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (compField π' (fieldKernel φ₀ Sr aY t)) :=
    (retCovNormCLM π').contDiff.comp hS2
  funext x
  have h1 := retCov_compField_readout (S := S) m E η₀ π π' hπ'
    (fieldCov D m p (fieldKernel φ₀ Sr aY) - fieldKernel φ₀ Sr aY) t x
  rw [h1]
  have h2 : compField π' ((fieldCov D m p (fieldKernel φ₀ Sr aY) - fieldKernel φ₀ Sr aY) t) x =
      covPolyP (covPrimitive D m t) p (compField π' (fieldKernel φ₀ Sr aY t)) x -
        compField π' (fieldKernel φ₀ Sr aY t) x := by
    have := retCov_compField_cov D m p π' (fieldKernel φ₀ Sr aY) t hS2
    change toCompSpace π' (fieldCov D m p (fieldKernel φ₀ Sr aY) t x -
      fieldKernel φ₀ Sr aY t x) = _
    rw [toCompSpace_sub]
    exact congrArg₂ (· - ·) (congrFun this x) rfl
  rw [h2, map_sub, hg]
  have h3 := ErrorJets.liftId_covPolyP_clm (covPrimitive D m t) (readoutCLM m E η₀ π π') p
    (compField π' (fieldKernel φ₀ Sr aY t)) hgc x
  rw [h3]
  rfl

/-- **The profile norm of the retained covariance profile**, in terms of abstract constants. -/
theorem retCov_profile_bound (D : OCData) (m p K : ℕ) (s E η₀ : ℝ) {S S' : Finset Comp}
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ' : ∀ v', 0 < π' v')
    {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (Sr : KernelSpec)
    (aY : ℝ → Vec 2 → ∀ v : CompIn S', ScalarH v.1.root) (t : ℝ)
    (haY : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) (aY t)) (hp : IsZ2Periodic (aY t))
    {ε Cc Cn Ck c₂ : ℝ} (hE : 0 < E) (hr : 0 < Sr.width) (hrE : Sr.width ≤ c₂ * E)
    (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck) (hK : 1 ≤ K)
    (hA : ∀ i j, |covPrimitive D m t i j| ≤ ε * Sr.width ^ 2)
    (hR : ‖readoutCLM m E η₀ π π'‖ ≤ Cn)
    (hkern : ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm
          (partialDerivative α (Sr.applyClassical φ₀ t (compField π' (aY t)))) ≤
        ENNReal.ofReal (Ck * Sr.width ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i),
            supNorm (partialDerivative β (compField π' (aY t)))) :
    profileNorm E K s (compField π (fieldReadout (S := S) m E η₀
        (fieldCov D m p (fieldKernel φ₀ Sr aY) - fieldKernel φ₀ Sr aY) t)) ≤
      (profileJetCount K : ℝ≥0∞) *
        (ENNReal.ofReal (retCovConst Cn Cc Ck c₂ K p * ε) *
          profileSeminorm E K s (compField π' (aY t))) := by
  have h2p : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (aY t) :=
    haY.of_le (by exact_mod_cast (by omega : 2 * p ≤ K + 2 * p))
  rw [retCov_profile_field_eq D m p E η₀ π π' hπ' hφs hφsupp Sr aY t h2p hp]
  have hW : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) (compField π' (aY t)) := (retCovNormCLM π').contDiff.comp haY
  have hWp : IsZ2Periodic (compField π' (aY t)) := fun n x => by
    change toCompSpace π' (aY t (x + latticeShift n)) = toCompSpace π' (aY t x)
    rw [hp n x]
  have hg := (regularKernel_contDiff_periodic hφs hφsupp Sr t hW hWp).1
  exact retCov_profile_norm (s := s) hE hr hrE hc₂ hε hεC hCn hCk hK (covPrimitive D m t) hA
    (readoutCLM m E η₀ π π') hR _ (compField π' (aY t)) hg hkern

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **The input of the retained lift at the lift radius**.

The positive bound of the lift (`passageLift_positive_partial_bound`) sees the input `P_p𝖱S_rY`
through its positive jets at the lift radius `ρ_L`. Here they are bounded by the profile seminorm
of `Y`:

`∑_{1≤|γ|≤K+N} ρ_L^{|γ|} |∂^γ F[P_p𝖱S_rY](x)| ≤ C ρ_L E^{s-1} [F'Y]_{E,K;s}`.

* `liftInput_word_le`: the word bound of the full polynomial `P_p(R ∘ g)`, degrees `0 ≤ n ≤ p`
  (`retCov_word_le` for `n ≥ 1`, plus the identity term);
* `liftInput_term_le`, `liftInput_bound`: the abstract bound, from the kernel bound at the orders
  `1 ≤ i ≤ K + N + 2p` (`retCov_jet_le`, `retCov_block_le`) and the real algebra
  `liftInput_term_alg`;
* `passageLiftInput_bound`: the passage. The fresh kernel born at `m - 1` has width
  `r = c_r ρ_L E^{σ₀}` exactly (`freshLength D c_r (m-1) = c_r · liftLength D m`), it is admissible
  (`retCov_fresh_admissible`), the covariance is `≤ ε r²` (`retCov_cov_scales`), `ρ_L ≤ C E^{1+c}`
  (`bandChain_uniform_ledger`) and `ρ_L ≤ E` (`native_lift_scale_bounds`). The exponent condition
  is the hypothesis `σ₀N ≤ c(K-1)`.

Special cases: `p = 0` (`P_0 = I`, only the identity term); `N = 0` (no order above `K`); a
constant `Y` (both sides vanish); `[Y] = ∞` (nothing to prove). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Finite.TerminalLift AVRegularity.Finite.WeakLift
  AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The constant of the input bound at the lift radius. -/
def liftInputConst (Cn Cc Ck Cρ cr : ℝ) (K N p : ℕ) : ℝ :=
  ((multiIndicesBetween 1 (K + N)).card : ℝ) * ((p + 1 : ℕ) : ℝ) *
    (4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) * cr⁻¹ ^ N *
      (K.factorial : ℝ))

section Abstract

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Pointwise word bound for `P_p(R ∘ g)` against the full jets of `g`, degrees `n ≤ p`. -/
theorem liftInput_word_le (A : Matrix (Fin 2) (Fin 2) ℝ) (B Cn : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (p j : ℕ) {g : Vec 2 → V}
    (hg : ContDiff ℝ ((j + 2 * p : ℕ) : ℕ∞) g) (β : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedDerivative β (covPolyP A p (fun y => R (g y))) x‖ ≤
      ∑ n ∈ Finset.range (p + 1), (4 * B) ^ n * (Cn * ‖iteratedFDeriv ℝ (j + 2 * n) g x‖) := by
  let F : Vec 2 → W := fun y => R (g y)
  have hgj : ContDiff ℝ (j : ℕ∞) g :=
    hg.of_le (by exact_mod_cast Nat.le_add_right j (2 * p))
  have hF : ContDiff ℝ (j : ℕ∞) F := R.contDiff.comp hgj
  have hP : ContDiff ℝ (j : ℕ∞) (covPolyP A p F) :=
    regularCov_contDiff A p j (R.contDiff.comp hg)
  have hdiff := congrFun (orderedDerivative_sub β hP hF) x
  change orderedDerivative β (covPolyP A p F - F) x =
    orderedDerivative β (covPolyP A p F) x - orderedDerivative β F x at hdiff
  have hcor := retCov_word_le A B Cn hB hA R hR p j hg β x
  have hnorm := R.norm_iteratedFDeriv_comp_left (n := j) (hgj.contDiffAt (x := x)) le_rfl
  have hbase : ‖orderedDerivative β F x‖ ≤ Cn * ‖iteratedFDeriv ℝ j g x‖ :=
    (norm_orderedDerivative_le hF β x).trans
      (hnorm.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _)))
  have hn : ‖orderedDerivative β (covPolyP A p F) x‖ ≤
      ‖orderedDerivative β (covPolyP A p F - F) x‖ + ‖orderedDerivative β F x‖ := by
    rw [hdiff]
    exact norm_le_norm_sub_add _ _
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.add_zero, pow_zero, one_mul]
  exact hn.trans (add_le_add hcor hbase)

/-- One term of the input bound, in `ℝ≥0∞`. -/
theorem liftInput_term_le {ρ E r cr θ ω Cρ εc Cc Cn Ck s : ℝ} {K N p : ℕ}
    (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : r = cr * ρ * θ)
    (hCρ : 1 ≤ Cρ) (hρω : ρ ≤ Cρ * (E * ω)) (hωθ : ω ^ (K - 1) ≤ θ ^ N)
    (hε : 0 ≤ εc) (hεC : εc ≤ Cc) (hCc : 1 ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck) (hK : 1 ≤ K)
    {j n : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K + N) (hn : n ≤ p) (g Wf : Vec 2 → V) (x : Vec 2)
    (hg : ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 1 ≤ i → i ≤ K + N + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf)) :
    ENNReal.ofReal (ρ ^ j) *
        (ENNReal.ofReal ((4 * (εc * r ^ 2)) ^ n * Cn) *
          ENNReal.ofReal ‖iteratedFDeriv ℝ (j + 2 * n) g x‖) ≤
      ENNReal.ofReal ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) *
        cr⁻¹ ^ N) * (ρ * E ^ (s - 1)) * (K.factorial : ℝ)) * profileSeminorm E K s Wf := by
  have hi1 : 1 ≤ j + 2 * n := by omega
  have hiM : j + 2 * n ≤ K + N + 2 * p := by omega
  have hgi : ContDiff ℝ ((j + 2 * n : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast hiM)
  have hjet := retCov_jet_le hgi x
  have hk := hker (j + 2 * n) hi1 hiM
  have hl1 : 1 ≤ min K (j + 2 * n) := by omega
  have hlK : min K (j + 2 * n) ≤ K := Nat.min_le_left _ _
  have hblock := retCov_block_le (s := s) hE hl1 hlK Wf
  have halg := liftInput_term_alg (s := s) (Cn := Cn) (Ck := Ck) (p := p) hρ hE hρE hcr hcr1
    hθ hθ1 hr hCρ hρω hωθ hε hεC hCc hCn hCk hK hj1 hj hn
  have hr0 : 0 < r := by rw [hr]; positivity
  have hCρ0 : 0 ≤ Cρ := zero_le_one.trans hCρ
  have hCc0 : 0 ≤ Cc := zero_le_one.trans hCc
  set SW := ∑ β ∈ multiIndicesBetween (min K (j + 2 * n)) (min K (j + 2 * n)),
    supNorm (partialDerivative β Wf) with hSW
  have hconst : 0 ≤ (4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) * cr⁻¹ ^ N) *
      (ρ * E ^ (s - 1)) := by positivity
  calc ENNReal.ofReal (ρ ^ j) * (ENNReal.ofReal ((4 * (εc * r ^ 2)) ^ n * Cn) *
        ENNReal.ofReal ‖iteratedFDeriv ℝ (j + 2 * n) g x‖)
      ≤ ENNReal.ofReal (ρ ^ j) * (ENNReal.ofReal ((4 * (εc * r ^ 2)) ^ n * Cn) *
        (ENNReal.ofReal ((2 : ℝ) ^ (j + 2 * n)) *
          (ENNReal.ofReal (Ck * r ^ (((min K (j + 2 * n) : ℕ) : ℝ) - ((j + 2 * n : ℕ) : ℝ))) *
            SW))) := by
        gcongr
        exact hjet.trans (mul_le_mul' le_rfl hk)
    _ = ENNReal.ofReal (ρ ^ j * ((4 * (εc * r ^ 2)) ^ n * Cn * 2 ^ (j + 2 * n) *
          (Ck * r ^ (((min K (j + 2 * n) : ℕ) : ℝ) - ((j + 2 * n : ℕ) : ℝ))))) * SW :=
        retCov_ofReal_comb (ρ ^ j) ((4 * (εc * r ^ 2)) ^ n * Cn) (2 ^ (j + 2 * n))
          (Ck * r ^ (((min K (j + 2 * n) : ℕ) : ℝ) - ((j + 2 * n : ℕ) : ℝ))) SW
          (by positivity) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) *
          cr⁻¹ ^ N) * (ρ * E ^ (s - 1)) * E ^ (((min K (j + 2 * n) : ℕ) : ℝ) - s)) * SW :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal halg) le_rfl
    _ = ENNReal.ofReal ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) *
          cr⁻¹ ^ N) * (ρ * E ^ (s - 1))) *
          (ENNReal.ofReal (E ^ (((min K (j + 2 * n) : ℕ) : ℝ) - s)) * SW) := by
        rw [ENNReal.ofReal_mul hconst, mul_assoc]
    _ ≤ ENNReal.ofReal ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) *
          cr⁻¹ ^ N) * (ρ * E ^ (s - 1))) *
          (ENNReal.ofReal (K.factorial : ℝ) * profileSeminorm E K s Wf) := by
        gcongr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hconst]

/-- **The input bound at the lift radius**, abstract form. -/
theorem liftInput_bound {ρ E r cr θ ω Cρ εc Cc Cn Ck s : ℝ} {K N p : ℕ}
    (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : r = cr * ρ * θ)
    (hCρ : 1 ≤ Cρ) (hρω : ρ ≤ Cρ * (E * ω)) (hωθ : ω ^ (K - 1) ≤ θ ^ N)
    (hε : 0 ≤ εc) (hεC : εc ≤ Cc) (hCc : 1 ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck) (hK : 1 ≤ K)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, |A i j| ≤ εc * r ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (g Wf : Vec 2 → V)
    (hg : ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 1 ≤ i → i ≤ K + N + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf))
    (x : Vec 2) :
    ENNReal.ofReal (∑ γ ∈ multiIndicesBetween 1 (K + N), ρ ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (covPolyP A p (fun y => R (g y))) x‖) ≤
      ENNReal.ofReal (liftInputConst Cn Cc Ck Cρ cr K N p * (ρ * E ^ (s - 1))) *
        profileSeminorm E K s Wf := by
  have hr0 : 0 < r := by rw [hr]; positivity
  have hB : 0 ≤ εc * r ^ 2 := by positivity
  have hCρ0 : 0 ≤ Cρ := zero_le_one.trans hCρ
  have hCc0 : 0 ≤ Cc := zero_le_one.trans hCc
  have hconst : 0 ≤ (4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) * cr⁻¹ ^ N) *
      (ρ * E ^ (s - 1)) * (K.factorial : ℝ) := by positivity
  have hterm : ∀ γ ∈ multiIndicesBetween 1 (K + N),
      ENNReal.ofReal (ρ ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (covPolyP A p (fun y => R (g y))) x‖) ≤
      ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck *
        Cρ ^ (K - 1) * cr⁻¹ ^ N) * (ρ * E ^ (s - 1)) * (K.factorial : ℝ))) *
        profileSeminorm E K s Wf := by
    intro γ hγ
    have hj := (Finset.mem_filter.mp hγ).2
    have heq : ![γ 0, γ 1] = γ := by ext i; fin_cases i <;> rfl
    have hgj : ContDiff ℝ ((γ 0 + γ 1 + 2 * p : ℕ) : ℕ∞) g :=
      hg.of_le (by exact_mod_cast (by omega : γ 0 + γ 1 + 2 * p ≤ K + N + 2 * p))
    have hw := liftInput_word_le A (εc * r ^ 2) Cn hB hA R hR p (γ 0 + γ 1) hgj
      (Fin.append (fun _ : Fin (γ 0) => (0 : Fin 2)) (fun _ : Fin (γ 1) => (1 : Fin 2))) x
    rw [weakPositive_sorted_word_eq_partial, heq] at hw
    calc ENNReal.ofReal (ρ ^ (γ 0 + γ 1) *
          ‖partialDerivative γ (covPolyP A p (fun y => R (g y))) x‖)
        ≤ ENNReal.ofReal (ρ ^ (γ 0 + γ 1) * ∑ n ∈ Finset.range (p + 1),
            (4 * (εc * r ^ 2)) ^ n * (Cn * ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) g x‖)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw (by positivity))
      _ = ∑ n ∈ Finset.range (p + 1), ENNReal.ofReal (ρ ^ (γ 0 + γ 1)) *
            (ENNReal.ofReal ((4 * (εc * r ^ 2)) ^ n * Cn) *
              ENNReal.ofReal ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) g x‖) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity), Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← mul_assoc ((4 * (εc * r ^ 2)) ^ n), ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∑ _n ∈ Finset.range (p + 1), ENNReal.ofReal ((4 ^ p * Cc ^ p * Cn *
            2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) * cr⁻¹ ^ N) * (ρ * E ^ (s - 1)) *
            (K.factorial : ℝ)) * profileSeminorm E K s Wf :=
          Finset.sum_le_sum fun n hn => liftInput_term_le hρ hE hρE hcr hcr1 hθ hθ1 hr hCρ hρω
            hωθ hε hεC hCc hCn hCk hK hj.1 hj.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            g Wf x hg hker
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun γ _ => by positivity)]
  calc ∑ γ ∈ multiIndicesBetween 1 (K + N), ENNReal.ofReal (ρ ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (covPolyP A p (fun y => R (g y))) x‖)
      ≤ ∑ _γ ∈ multiIndicesBetween 1 (K + N),
        ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * ((4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck *
          Cρ ^ (K - 1) * cr⁻¹ ^ N) * (ρ * E ^ (s - 1)) * (K.factorial : ℝ))) *
          profileSeminorm E K s Wf := Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 2
        unfold liftInputConst
        ring

end Abstract

/-- The width of the fresh kernel born at `m - 1` is `c_r ρ_L E^{σ₀}`. -/
theorem freshWidth_eq_liftLength (D : OCData) (cr σ₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    freshWidth D cr σ₀ (m - 1) = cr * liftLength D m * D.eps (m - 1) ^ σ₀ := by
  unfold freshWidth freshLength liftLength
  rw [Nat.sub_add_cancel hm]

/-- **The input of the retained lift at the lift radius**, by the smoothing bound of Lemma 13.4(a)
of the paper. -/
theorem passageLiftInput_bound (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (_hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ →
      Function.support φ₀ ⊆ closedEuclideanUnitBall →
    ∀ (K N p : ℕ) (nk : ℕ+) (cr σ₀ Cn : ℝ), 1 ≤ K → 0 < cr → cr ≤ 1 → 0 ≤ σ₀ →
      2 * σ₀ ≤ ocDelta α q → σ₀ * N ≤ ocC α q * ((K - 1 : ℕ) : ℝ) →
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ 2 ≤ m₀ ∧
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ M : ℕ, IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ m : ℕ, m₀ ≤ m → m ≤ M → ∀ Sr : KernelSpec, IsFreshKernel D cr σ₀ nk (m - 1) Sr →
    ∀ {S S' : Finset Comp} (π : CompIn S → ℝ) (π' : CompIn S' → ℝ), (∀ v', 0 < π' v') →
    ∀ η₀ : ℝ, ‖readoutCLM m (D.eps (m - 1)) η₀ π π'‖ ≤ Cn →
    ∀ (aY : ℝ → Vec 2 → ∀ v : CompIn S', ScalarH v.1.root) (t : ℝ),
      ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞) (aY t) → IsZ2Periodic (aY t) → ∀ x : Vec 2,
      ENNReal.ofReal (∑ γ ∈ multiIndicesBetween 1 (K + N), liftLength D m ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (compField π (fieldCov D m p
          (fieldReadout m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY)) t)) x‖) ≤
      ENNReal.ofReal (C * (liftLength D m * D.eps (m - 1) ^ (s - 1))) *
        profileSeminorm (D.eps (m - 1)) K s (compField π' (aY t)) := by
  obtain ⟨Λa, hΛa, hadm⟩ := retCov_fresh_admissible α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Cs, hCs, Λs, _hΛs, hscale⟩ := retCov_cov_scales α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Cl, hCl, Λl, _hΛl, hled⟩ :=
    CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λn, _hΛn, hnat⟩ := native_lift_scale_bounds hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max (max Λa Λs) (max Λl Λn), hΛa.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφs hφsupp K N p nk cr σ₀ Cn hK hcr hcr1 hσ hσδ hexp
  have hΛa' : Λa ≤ Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛs' : Λs ≤ Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛl' : Λl ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛn' : Λn ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛ1 : 1 ≤ Λ := by have := hΛa.trans hΛa'; omega
  obtain ⟨Γ, _hΓ, ma, _hma, hadm'⟩ := hadm Λ hΛa'
  obtain ⟨mn, hmn, hnat'⟩ := hnat Λ hΛn'
  obtain ⟨Ck, hCk, hker⟩ := retCov_kernel_orders φ₀ hφ₀ hφs hφsupp Γ 0 nk K (p + N) hK
  obtain ⟨C1, hC1, hker1⟩ :=
    Providers.passage_kernel_sup φ₀ hφ₀ hφs hφsupp Γ 0 nk 1 1 le_rfl le_rfl
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
  have hCl0 : 0 ≤ Cl := zero_le_one.trans hCl
  refine ⟨liftInputConst (max Cn 0) (Cs / cr ^ 2) (Ck + C1) Cl cr K N p, max ma mn, ?_,
    (hmn.trans (le_max_right _ _)), ?_⟩
  · have h0 : 0 ≤ max Cn 0 := le_max_right _ _
    unfold liftInputConst
    positivity
  intro D hDα hDq hDΛ hDζ hseq M hband hterm m hm hmM Sr hSr S S' π π' hπ' η₀ hL aY t haY haYp x
  subst hDα hDq hDΛ hDζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by rw [hterm]; exact hband
  have hm2 : 2 ≤ m := (hmn.trans (le_max_right _ _)).trans hm
  have hmt : m ≤ D.term := by rw [hterm]; exact hmM
  obtain ⟨hSadm, hSw⟩ := hadm' D rfl rfl rfl rfl hseq hbandD cr σ₀ hcr nk 0
    (by have := nk.pos; omega) m ((le_max_left _ _).trans hm) hmt Sr hSr
  obtain ⟨hεle, _hrE, hcov⟩ := hscale D.Λ hΛs' D rfl rfl rfl rfl M hband hterm cr σ₀ hcr hcr1
    hσ hσδ m hm2 hmM
  obtain ⟨hρ, _, hρE⟩ := hnat' D rfl rfl rfl rfl hbandD m ((le_max_right _ _).trans hm) hmt
  have hk := (hled D.Λ hΛl' M (by omega) D.κ hband).2 m hm2 hmM (D.κ m) (D.κ (m - 1)) rfl rfl
  have hrh : liftLength D m ≤ Cl * D.eps (m - 1) ^ (1 + ocC D.α D.q) := hk.2.2.2.2.1.2
  have hE0 : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hE1 : D.eps (m - 1) ≤ 1 := ocEpsilon_le_one hΛ1 _
  have hρE' : liftLength D m ≤ D.eps (m - 1) := (div_le_one hE0).mp hρE
  have hfw : Sr.width = cr * liftLength D m * D.eps (m - 1) ^ σ₀ := by
    rw [hSr.1, freshWidth_eq_liftLength D cr σ₀ (by omega : 1 ≤ m)]
  have hθ : 0 < D.eps (m - 1) ^ σ₀ := Real.rpow_pos_of_pos hE0 _
  have hθ1 : D.eps (m - 1) ^ σ₀ ≤ 1 := Real.rpow_le_one hE0.le hE1 hσ
  have hρω : liftLength D m ≤ Cl * (D.eps (m - 1) * D.eps (m - 1) ^ ocC D.α D.q) := by
    have h1 : D.eps (m - 1) ^ (1 + ocC D.α D.q) =
        D.eps (m - 1) * D.eps (m - 1) ^ ocC D.α D.q := by
      rw [Real.rpow_add hE0, Real.rpow_one]
    rw [← h1]
    exact hrh
  have hωθ : (D.eps (m - 1) ^ ocC D.α D.q) ^ (K - 1) ≤ (D.eps (m - 1) ^ σ₀) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hE0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hexp
  have hcr2 : cr ^ 2 ≤ 1 := pow_le_one₀ hcr.le hcr1
  have hCc : 1 ≤ Cs / cr ^ 2 := (one_le_div (pow_pos hcr 2)).mpr (hcr2.trans hCs)
  have hεC : Cs / cr ^ 2 * D.eps (m - 1) ^ (ocDelta D.α D.q - 2 * σ₀) ≤ Cs / cr ^ 2 :=
    mul_le_of_le_one_right (zero_le_one.trans hCc) hεle
  have hε0 : 0 ≤ Cs / cr ^ 2 * D.eps (m - 1) ^ (ocDelta D.α D.q - 2 * σ₀) :=
    mul_nonneg (zero_le_one.trans hCc) (Real.rpow_nonneg hE0.le _)
  have hA : ∀ i j, |covPrimitive D m t i j| ≤
      (Cs / cr ^ 2 * D.eps (m - 1) ^ (ocDelta D.α D.q - 2 * σ₀)) * Sr.width ^ 2 := by
    intro i j
    rw [hSr.1]
    exact hcov t i j
  have hSreg := regularKernel_contDiff_periodic hφs hφsupp Sr t haY haYp
  have hRreg : ContDiff ℝ ((2 * p : ℕ) : ℕ∞)
      (fieldReadout (S := S) m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY) t) :=
    regularReadout_contDiff m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY) t
      (hSreg.1.of_le (by exact_mod_cast (by omega : 2 * p ≤ K + N + 2 * p)))
  have hkernel := retCov_compField_kernel hφs hφsupp Sr t π' haY.continuous haYp
  have hmodel : compField π (fieldCov D m p
      (fieldReadout m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY)) t) =
      covPolyP (covPrimitive D m t) p (fun y => readoutCLM m (D.eps (m - 1)) η₀ π π'
        (Sr.applyClassical φ₀ t (compField π' (aY t)) y)) := by
    rw [retCov_compField_cov D m p π _ t hRreg]
    congr 1
    funext y
    rw [retCov_compField_readout m (D.eps (m - 1)) η₀ π π' hπ' (fieldKernel φ₀ Sr aY) t y]
    congr 1
    exact congrFun hkernel y
  have hV : ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞) (compField π' (aY t)) :=
    regularCompField_contDiff π' haY
  have hVp : IsZ2Periodic (compField π' (aY t)) := regularCompField_periodic π' haYp
  have hg : ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞)
      (Sr.applyClassical φ₀ t (compField π' (aY t))) := by
    rw [← hkernel]
    exact regularCompField_contDiff π' hSreg.1
  have hkerAll : ∀ i, 1 ≤ i → i ≤ K + N + 2 * p →
      ∑ α ∈ multiIndicesBetween i i,
          supNorm (partialDerivative α (Sr.applyClassical φ₀ t (compField π' (aY t)))) ≤
        ENNReal.ofReal ((Ck + C1) * Sr.width ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i),
            supNorm (partialDerivative β (compField π' (aY t))) := by
    intro i hi1 hiM
    by_cases hi2 : 2 ≤ i
    · refine (hker Sr hSr.2.1 hSadm hSw t (compField π' (aY t))
        (hV.of_le (by exact_mod_cast (by omega : K ≤ K + N + 2 * p))) hVp i hi2
        (by omega)).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hSw.le _)
    · have hi : i = 1 := by omega
      subst hi
      have hmin : min K 1 = 1 := Nat.min_eq_right hK
      rw [hmin]
      refine (hker1 Sr hSr.2.1 hSadm hSw t (compField π' (aY t))
        (hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + N + 2 * p))) hVp).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hSw.le _)
  rw [hmodel]
  exact liftInput_bound (s := s) hρ hE0 hρE' hcr hcr1 hθ hθ1 hfw hCl hρω hωθ hε0 hεC hCc
    (le_max_right Cn 0) (by linarith) hK (covPrimitive D m t) hA
    (readoutCLM m (D.eps (m - 1)) η₀ π π') (hL.trans (le_max_left Cn 0))
    (Sr.applyClassical φ₀ t (compField π' (aY t))) (compField π' (aY t)) hg hkerAll x

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The retained covariance profile**.

`passageRetainedCovariance`: `𝓘_{E,K;s}(F 𝖱(P_p - I)S_r aY) ≤ C E^{δ-2σ₀} [F'aY]_{E,K;s}`.
The prefix of `iteration_passage` is consumed as in `passageProfilesRegular`; no stage geometry is
needed (the profile involves neither the lift nor `aU`). Level threshold `m_* = m₀` of the
admissibility of the fresh kernel. Constants: `Λ₀ = max(Λ_adm, Λ_scales)`, `Γ` from the fresh axes
bounds, `L = 0`, `C₀ = jetCount · retCovConst · (C/c_r²)`.

Special cases: `p = 0`/`aY t = 0`: the profile is `0`; `C_n < 0`: the readout hypothesis is
false. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation AVRegularity.Finite
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The final real inequality: the constant of the bound. -/
theorem retCov_final_const {jc rc Cc x Cb : ℝ} (hjc : 0 ≤ jc)
    (hx : 0 ≤ x) (hCb : jc * rc * Cc ≤ Cb) (S : ℝ≥0∞) :
    ENNReal.ofReal jc * (ENNReal.ofReal (rc * (Cc * x)) * S) ≤ ENNReal.ofReal (Cb * x) * S := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hjc]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc jc * (rc * (Cc * x)) = (jc * rc * Cc) * x := by ring
    _ ≤ Cb * x := mul_le_mul_of_nonneg_right hCb hx

theorem passageRetainedCovariance (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageRetainedCovarianceStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hadm⟩ := retCov_fresh_admissible α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨C, hC, Λs, hΛs, hsc⟩ := retCov_cov_scales α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨max Λa Λs, by omega, ?_⟩
  intro Λ hΛ
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hQb
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched
    hNaux hNout L hL hwid
  refine ⟨0, 0, 0, ?_⟩
  intro sX sZ _ _ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart Cn
  obtain ⟨Γ, hΓ, m₀, hm₀, hadm'⟩ := hadm Λ ((le_max_left _ _).trans hΛ)
  obtain ⟨_, _, _, _, _, hσa, ha, haσ, _, hDs, _, _, _, _, _, _, _, hN2, hp1, hnk1⟩ := hsched
  have hDst : 1 ≤ succDstar D₀ N p H := by
    unfold succDstar
    have : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    omega
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα₀ hq
  have hσ₀pos : 0 < σ₀ := by linarith
  have hσδ : 2 * σ₀ ≤ ocDelta α q := by
    have h1 : σ₀ * 1 ≤ σ₀ * (succDstar D₀ N p H : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hDst) hσ₀pos.le
    linarith
  have hcrk : kI.cr = kS.cr := (Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  have hcr0 : 0 < kI.cr := hcrk ▸ hcr
  have hcr1 : kI.cr ≤ 1 := hcrk ▸ hcrupper
  obtain ⟨Ck, hCk, hkerf⟩ := retCov_kernel_orders φ₀ hφ₀ hφsmooth hφsupport Γ 0 nk.toPNat' K p
    (by omega)
  have hCc : 0 ≤ C / kI.cr ^ 2 := by positivity
  have hC0 : 0 ≤ retCovConst (max Cn 0) (C / kI.cr ^ 2) Ck C K p := by
    unfold retCovConst
    have : 0 ≤ ∑ n ∈ Finset.range p, (4 : ℝ) ^ (n + 1) * (C / kI.cr ^ 2) ^ n :=
      Finset.sum_nonneg fun n _ => by positivity
    have h2 : 0 ≤ max Cn 0 := le_max_right _ _
    have : 0 ≤ C := by linarith
    positivity
  refine ⟨(profileJetCount K : ℝ) * retCovConst (max Cn 0) (C / kI.cr ^ 2) Ck C K p *
    (C / kI.cr ^ 2), m₀, ?_⟩
  intro Cb hCb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hmol m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual hRn CcT hCcT
    aU aY t hts htf haY haYp
  have hm2 : 2 ≤ m := by omega
  have hΛD128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hspec := hfresh (m - 1) (by omega) (by omega)
  obtain ⟨hSadm, hSw⟩ := hadm' D hDα hDq hDΛ hDζ hseq hbandD kI.cr σ₀ hcr0 nk.toPNat' 0
    (by have := nk.toPNat'.pos; omega) m hm (by omega) (freshK (m - 1)) hspec
  obtain ⟨hxle, hrle, hcovb⟩ := hsc Λ ((le_max_right _ _).trans hΛ) D hDα hDq hDΛ hDζ M hband
    hterm kI.cr σ₀ hcr0 hcr1 hσ₀pos.le hσδ m hm2 (by omega)
  have hπ' : ∀ v, 0 < (G'.retained m H J).mass law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have hEpos : 0 < D.eps (m - 1) := by
    have hΛ1 : 1 ≤ D.Λ := by omega
    exact Construction.Stream.ocEpsilon_pos hΛ1
  have hxnn : 0 ≤ D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀) := Real.rpow_nonneg hEpos.le _
  have haY0 : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aY t) := haY
  have haY' : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) (aY t) :=
    haY0.of_le (by exact_mod_cast (by omega : K + 2 * p ≤ K + N + 2 * p + 2))
  have hSw' : 0 < (freshK (m - 1)).width := hSw
  have hrE : (freshK (m - 1)).width ≤ C * D.eps (m - 1) := by rw [hspec.1]; exact hrle
  have hbound := retCov_profile_bound D m p K s (D.eps (m - 1)) (succEta0 α q s)
    (G.mass law) ((G'.retained m H J).mass law) hπ' hφsmooth hφsupport (freshK (m - 1)) aY t
    haY' haYp (ε := C / kI.cr ^ 2 * D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀))
    (Cc := C / kI.cr ^ 2) (Cn := max Cn 0) (Ck := Ck) (c₂ := C) hEpos hSw' hrE hC
    (mul_nonneg hCc hxnn)
    (by simpa using mul_le_of_le_one_right hCc hxle) (le_max_right _ _) hCk.le (by omega)
    (by intro i j; rw [hspec.1]; exact hcovb t i j)
    (hRn.trans (le_max_left _ _))
    (fun i hi2 hiM => hkerf (freshK (m - 1)) hspec.2.1 hSadm hSw' t _
      ((retCovNormCLM _).contDiff.comp (haY0.of_le (by exact_mod_cast (by omega : K ≤ K + N + 2 * p + 2))))
      (fun n x => by
        change toCompSpace _ (aY t (x + latticeShift n)) = toCompSpace _ (aY t x)
        rw [haYp n x]) i hi2 hiM)
  have hprof : ((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H)
        (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 0 0 =
      compField (G.mass law) (fieldReadout (S := G.comps) m (D.eps (m - 1)) (succEta0 α q s)
        (fieldCov D m p (fieldKernel φ₀ (freshK (m - 1)) aY) - fieldKernel φ₀ (freshK (m - 1)) aY) t) :=
    rfl
  rw [hprof]
  refine hbound.trans ?_
  rw [show (profileJetCount K : ℝ≥0∞) = ENNReal.ofReal (profileJetCount K : ℝ) by simp]
  exact retCov_final_const (Nat.cast_nonneg _) hxnn hCb _

end AVRegularity.IterationPassage.Passage
end
end
end
