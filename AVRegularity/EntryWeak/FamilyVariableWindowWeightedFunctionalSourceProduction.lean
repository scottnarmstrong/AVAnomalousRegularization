-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFreshCoarseAppendedSourceReserve
import AVRegularity.EntryWeak.MolecularUlFluxNormBound
import AVRegularity.CycleComparison.Lift.SecondCrossMean

section
section
/-! Parent phase translations remain exact symmetries after actual moving-child sampling. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendedSource_translation {E : Type*}
    (r : ℕ) (D : OCData) (m : ℕ) (parentSlot slot : ℤ) (ell : ℝ)
    (δ : Vec (2 + 4 * r)) (hδ : δ ∈ independentFreshPhaseTranslations r)
    (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → E)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations (r + 1), IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ
      (fun t z Y => f t 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
        (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y)))) := by
  intro t z Y
  let P := independentStoredParameterProjection (4 * r) Y
  let dP := independentStoredParameterProjection (4 * r) δ
  let c := independentIntrinsicSlowProjection (4 * r) Y +
    ell • D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z
  let w := z + D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z
  have hprefix (j : Fin r) (phase : Bool) (q : Vec (4 * r)) :
      independentFreshChildProjection j.castSucc phase
        (independentFreshInsertCoordinates r (q, c, w)) = independentFreshChildProjection j phase q := by
    rw [← independentFreshPrefixProjection_component, independentFreshInsertCoordinates_prefix]
  have hc : ∀ j, independentFreshChildProjection j false
      (independentFreshInsertCoordinates r (P + dP, c, w)) =
        independentFreshChildProjection j false (independentFreshInsertCoordinates r (P, c, w)) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [independentFreshInsertCoordinates_last_center]
    · rw [hprefix, hprefix, map_add]
      change independentFreshChildProjection i false P +
        independentFreshChildProjection i false (independentStoredParameterProjection (4 * r) δ) = _
      rw [hδ.2.1 i, add_zero]
  have hp : ∀ j, ∃ n : Fin 2 → ℤ, independentFreshChildProjection j true
      (independentFreshInsertCoordinates r (P + dP, c, w)) =
        independentFreshChildProjection j true (independentFreshInsertCoordinates r (P, c, w)) + latticeShift n := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · refine ⟨0, ?_⟩
      simp only [independentFreshInsertCoordinates_last_phase]
      have hz : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
        funext i
        change ((0 : ℤ) : ℝ) = 0
        norm_num
      rw [hz, add_zero]
    · obtain ⟨n, hn⟩ := hδ.2.2 i
      refine ⟨n, ?_⟩
      rw [hprefix, hprefix, map_add]
      exact congrArg (fun v => independentFreshChildProjection i true P + v) hn
  dsimp only [independentFreshCoarseAppendPacking]
  rw [map_add, map_add, hδ.1, add_zero]
  exact independentFresh_zero_slow_sampling_phase_invariant (f t 0)
    (fun δ hδ W => hf δ hδ t 0 W) _ _ hc hp

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual moving append sources keep the native cell clock explicit and retain every full-family jet price. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseClockAppendedSource_window_reserve
    (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (parentSlot slot : ℤ) (hp : Odd parentSlot) (ell : ℝ) (hell : |ell| ≤ 1)
    (clock : ℝ → ℝ) (hclock : Measurable clock) (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K : ℕ) (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → ℝ)
    (Q : IndependentParameterSourceReserve K f) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ j ≤ K, Q.budget j ≤ θ * B)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations (r + 1), IndependentSourceTranslationInvariant δ f) :
    ∃ R : IndependentParameterSourceReserve K
      (independentTimeWindowSource I (independentFreshCoarseAppendedSource r D m parentSlot slot ell
        (fun t z Y => f (clock t) z Y))),
      ∀ n, R.budget n = θ * (K.factorial * B * (1 + (2 * Real.pi) ^ (K + 1)) ^ K) := by
  exact independentFreshCoarseAppendedSource_window_reserve r D hΛ hζ m parentSlot slot hp ell hell I hI hsmall K
    (fun t z Y => f (clock t) z Y) (Q.timeReparam clock hclock) θ B hθ hB hQ
    (fun δ hδ => (hf δ hδ).timeReparam clock)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal parent-normalized parameter chain has an open admissible recentering carrier. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseParameterChain_recenter_carrier_isOpen
    (D : OCData) (hΛ : 1 ≤ D.Λ) (bw ρ : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (A : RealChain) (hA : IsAdmissibleChain D bw j₀ level slot A) :
    IsOpen {Y : Vec (4 * A.children.length) × Vec 2 |
      IsAdmissibleChain D bw j₀ level slot
        ((actualIndependentCoarseParameterChain D A Y.1).recenter D (ρ • Y.2))} := by
  have hwell : A.WellSlotted := hA.2.2.1
  have hnative : IsAdmissibleChain D bw j₀ level slot
      (independentFreshChain (independentFreshBaseChain A)
        (fun j : Fin A.children.length => realChainSlotSeq A (j + 1))
        (independentFreshCoarseBirthLength D A) (independentFreshCoarseChainPacking D A)) := by
    rw [independentFreshCoarseChainPacking_reconstruct D hΛ A hwell]
    exact hA
  simp_rw [actualIndependentCoarseParameterChain_eq_fresh D A hwell,
    independentFreshStoredFamily_eq_chain]
  exact independentFreshChain_empty_base_recenter_carrier_isOpen D (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) rfl _ _ ρ bw j₀ level slot
    (independentFreshCoarseChainPacking D A) hnative

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal coordinate-windowed reference arrays retain all parent phase symmetries. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseClockSampledArray_translation
    (r : ℕ) (D : OCData) (m : ℕ) (parentSlot slot : ℤ) (ell : ℝ)
    (clock : ℝ → ℝ) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → Vec 2)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations (r + 1), IndependentSourceTranslationInvariant δ f)
    (δ : Vec (2 + 4 * r)) (hδ : δ ∈ independentFreshPhaseTranslations r) :
    IndependentSourceTranslationInvariant δ
      (fun t z Y a => independentTimeWindowSource I
        (independentFreshCoarseAppendedSource r D m parentSlot slot ell
          (fun t z Y => f (clock t) z Y a)) t z Y) := by
  classical
  have he := independentFreshCoarseAppendedSource_translation r D m parentSlot slot ell δ hδ
    (fun t z Y => f (clock t) z Y) (fun δ hδ => (hf δ hδ).timeReparam clock)
  intro t z Y
  funext a
  have hh : f (clock t) 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y + δ))) a =
    f (clock t) 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y))) a :=
    congrFun (he t z Y) a
  change (if t ∈ I then f (clock t) 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y + δ))) a else 0) =
    (if t ∈ I then f (clock t) 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y))) a else 0)
  rw [hh]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native inverse production is localized to the actual admissible recentered family. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseLiftCarrier (D : OCData) (A : RealChain) (bw ρ : ℝ)
    (j₀ level : ℕ) (slot : ℤ) : Set (Vec (2 + 4 * A.children.length)) :=
  actualIndependentCoarseNativeCarrier D A bw ∩
    {Y | IsAdmissibleChain D bw j₀ level slot
      ((actualIndependentCoarseParameterChain D A
        (independentStoredParameterProjection (4 * A.children.length) Y)).recenter D
          (ρ • independentIntrinsicSlowProjection (4 * A.children.length) Y))}

theorem actualIndependentCoarseLiftCarrier_isOpen (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw ρ : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) :
    IsOpen (actualIndependentCoarseLiftCarrier D A bw ρ j₀ level slot) := by
  apply (actualIndependentCoarseNativeCarrier_isOpen D A bw).inter
  exact (actualIndependentCoarseParameterChain_recenter_carrier_isOpen
    D hΛ bw ρ j₀ level slot A hA).preimage
      ((independentStoredParameterProjection (4 * A.children.length)).continuous.prodMk
        (independentIntrinsicSlowProjection (4 * A.children.length)).continuous)

theorem actualIndependentCoarseLiftCarrier_native (D : OCData)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (A : RealChain) (bw ρ : ℝ)
    (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (X : Vec 2) (hX : ‖X‖ ≤ 1 / 8)
    (hAX : IsAdmissibleChain D bw j₀ level slot (A.recenter D (ρ • X))) :
    independentIntrinsicParameterPacking (4 * A.children.length) X
      (independentFreshCoarseChainPacking D A) ∈ actualIndependentCoarseLiftCarrier D A bw ρ j₀ level slot := by
  refine ⟨actualIndependentCoarseNativeCarrier_native D hq hΛ A bw hbw j₀ level slot hA X hX, ?_⟩
  change IsAdmissibleChain D bw j₀ level slot _
  rw [independentIntrinsicParameterPacking_stored, independentIntrinsicParameterPacking_slow,
    actualIndependentCoarseParameterChain_native D (by omega) A hA.2.2.1]
  exact hAX

end AVRegularity.EntryWeakProofs
end
end

section
/-! A smaller open slow carrier licenses reference cutoffs and still contains every native anchor. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseProductionCarrier (D : OCData) (A : RealChain) (bw ρ : ℝ)
    (j₀ level : ℕ) (slot : ℤ) : Set (Vec (2 + 4 * A.children.length)) :=
  actualIndependentCoarseLiftCarrier D A bw ρ j₀ level slot ∩
    {Y | ‖independentIntrinsicSlowProjection (4 * A.children.length) Y‖ < 1 / 8}

theorem actualIndependentCoarseProductionCarrier_isOpen (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw ρ : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) :
    IsOpen (actualIndependentCoarseProductionCarrier D A bw ρ j₀ level slot) :=
  (actualIndependentCoarseLiftCarrier_isOpen D hΛ A bw ρ j₀ level slot hA).inter
    (isOpen_lt (independentIntrinsicSlowProjection _).continuous.norm continuous_const)

theorem actualIndependentCoarseProductionCarrier_native_anchor (D : OCData)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (A : RealChain) (bw ρ : ℝ)
    (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) :
    independentIntrinsicParameterPacking (4 * A.children.length) 0
      (independentFreshCoarseChainPacking D A) ∈
        actualIndependentCoarseProductionCarrier D A bw ρ j₀ level slot := by
  refine ⟨actualIndependentCoarseLiftCarrier_native D hq hΛ A bw ρ hbw j₀ level slot hA 0
    (by simp only [norm_zero]; norm_num) ?_, ?_⟩
  · simpa only [smul_zero, Providers.GenSem.recenter_zero D hζ] using hA
  · change ‖independentIntrinsicSlowProjection (4 * A.children.length)
      (independentIntrinsicParameterPacking (4 * A.children.length) 0
        (independentFreshCoarseChainPacking D A))‖ < 1 / 8
    rw [independentIntrinsicParameterPacking_slow, norm_zero]
    norm_num

end AVRegularity.EntryWeakProofs
end
end

section
/-! Common genuine primitive budgets uniformly produce mean-free next-stage sources before all family data. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {A : Type*} {d H : ℕ}

theorem family_variable_window_coordinate_word_classical_source_reserves_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : A → ℝ → Vec 2 → Vec d → ℂ}
    {F : A → ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qf : ∀ x, IndependentParameterSourceReserve H (f x))
    (QF : ∀ x, IndependentParameterSourceReserve H (F x))
    (BG Bs Bf : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n) (hBf : ∀ n, 0 ≤ Bf n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (hQf : ∀ x n, n ≤ H → (Qf x).budget n ≤ Bs n)
    (hQF : ∀ x n, n ≤ H → (QF x).budget n ≤ Bf n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hf : ∀ x t, t ≤ a x → ∀ z Y, f x t z Y = 0)
    (hF : ∀ x t, t ≤ a x → ∀ z Y, F x t z Y = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (c : A → List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
      (u : A → List (Fin d) → Vec d → ℝ → TorusHk K ℂ),
      (∀ x Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P x Y))
        (fun t => cellQ0 (coordinateSourceWord (f x) w Y t))
        (coordinateSourceWord (F x) w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) w) (c x w Y)) ∧
      (∀ x w, w.length ≤ N → ∀ Y, StronglyMeasurable (u x w Y) ∧ ∀ t ∈ Icc (a x) (b x),
        torusHkValueCLM (u x w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c x w Y) t) ∧
      ∃ Q : ∀ x, IndependentParameterSourceReserve S (independentTimeWindowSource (Ioc (a x) (b x))
        (fun t z Y => realClassicalLift K (mapTorusHk Complex.reCLM (u x [] Y t)) z)),
        (∀ x r, r ≤ S → (Q x).budget r ≤ ((d : ℝ) + 1) ^ r * B) ∧
        (∀ x t Y, fieldCellMean (fun z => independentTimeWindowSource (Ioc (a x) (b x))
          (fun t z Y => realClassicalLift K (mapTorusHk Complex.reCLM (u x [] Y t)) z) t z Y) = 0) := by
  have hp x := coordinate_word_inverse_norm_jet_family_exists N hN (QG x) (Qf x) (QF x) (hv x)
  choose c hc hs using hp
  have hsol x Y w (hw : w.length ≤ N) : IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (coordinateSourceWord (f x) w Y t))
      (coordinateSourceWord (F x) w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) w) (c x w Y) := by
    rw [hP x Y, hPv x Y]
    exact hs x Y w hw
  obtain ⟨u, R, hub⟩ := family_variable_window_coordinate_word_uniform_carrier_family_exists hab N (by omega)
    QG Qf QF BG Bs Bf hBG hBs hBf hQG hQf hQF P hP v hv hPv V c hsol hf hF K (by omega)
  have hu x p (hp : p.length ≤ N) Y t (ht : t ∈ Icc (a x) (b x)) := (hub p hp).2 x Y |>.2.2 t ht
  obtain ⟨B, hB, hb⟩ := family_variable_window_coordinate_word_classical_joint_bound hab N K hH QG Qf QF
    P hP v hv hPv V c hc hsol hf hF u hu R (fun x p hp Y t => (hub p hp).2 x Y |>.2.1 t) (by omega)
  let Q := fun x => classicalWindowIndependentSourceReserve S K (by omega) (a x) (b x) (u x [])
    (fun Y => (hub [] (by simp)).2 x Y |>.1)
    (fun t ht => coordinate_word_classical_joint_contDiff (hab x) N K hH (QG x) (Qf x) (QF x)
      (P x) (hP x) (v x) (hv x) (hPv x) (V x) (c x) (hc x) (hsol x) (hf x) (hF x)
      (u x) (hu x) R (fun p hp Y t => (hub p hp).2 x Y |>.2.1 t)
      [] S 0 (by simpa using hS) (by omega) t ht)
    (fun r => ((d : ℝ) + 1) ^ r * B) (fun r => mul_nonneg (by positivity) hB)
    (fun r hr t ht X => hb x [] r 0 (by simpa using hr.trans hS) (by omega) t ht X)
  refine ⟨B, hB, c, u, hsol, ?_, Q, ?_, ?_⟩
  · intro x w hw Y
    exact ⟨(hub w hw).2 x Y |>.1, hu x w hw Y⟩
  · intro x r hr
    exact le_refl _
  · intro x t Y
    by_cases ht : t ∈ Ioc (a x) (b x)
    · simp only [independentTimeWindowSource, ite_eq_left ht]
      exact realHigherCarrier_inverse_mean_zero K (by omega) _ _ _ (c x [] Y)
        (hsol x Y [] (by simp)) t (u x [] Y t) (hu x [] (by simp) Y t ⟨ht.1.le, ht.2⟩)
    · simp only [independentTimeWindowSource, ite_eq_right ht, fieldCellMean_const]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent primitive reserves produce uniformly priced extensions of actual local scalar inverses. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {A : Type*} {d H : ℕ}

theorem coordinateSourceWord_nil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → Vec 2 → Vec d → E) (Y : Vec d) :
    coordinateSourceWord f [] Y = fun t z => f t z Y := by
  funext t z
  exact iteratedFDeriv_zero_apply _

end AVRegularity.EntryWeakProofs
end
end

section
/-! Phase-preserving clamped geometry gives global Piola transition jets at zero fine displacement. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshClampedTransferEntry (r : ℕ) (D : OCData)
    (family : Vec (4 * r) → RealChain) (m : ℕ) (ρ : ℝ) (slot : ℤ) (t : ℝ)
    (i j : Fin 2) (Y : (Vec 2 × Vec (2 + 4 * r)) × Vec 2) : ℝ :=
  let Z := independentFreshClampedMovingTransferCoordinates r Y
  let C := (family Z.1.1.1).recenter D (ρ • Z.1.1.2)
  (childTransition D slot t (C.recenter D (D.eps m • Z.2))
    (Z.1.2 + (D.eps m)⁻¹ • (D.eps m • Z.2)))⁻¹ i j

theorem independentFreshClampedTransferEntry_contDiff (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshClampedTransferEntry r D family m ρ slot t i j) :=
  (independent_moving_transfer_entry_contDiff D hΛ hζ family hfamily m pslot hm hs hp
    harea ρ θ hscale slot t hf i j).comp
      (independentFreshClampedMovingTransferCoordinates_contDiff r)

theorem independentFreshClampedTransferEntry_zero_jet_bound (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hscale : D.eps m = ρ * θ)
    (slot : ℤ) (t : ℝ)
    (hsmall : |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2))
    (H n : ℕ) (hn : n ≤ H) (B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hclamp : ∀ a, 1 ≤ a → a ≤ H → ∀ Y,
      ‖iteratedFDeriv ℝ a (independentFreshGeometryClamp r) Y‖ ≤ C)
    (hchart : ∀ P, independentFreshCenterStrip P → ∀ a, 1 ≤ a → a ≤ H + 2 →
      ∀ Z : Vec 2, ‖Z‖ ≤ 1 / 2 + (0 + 2 * Real.pi) →
        ‖iteratedFDeriv ℝ a (fun Y : Vec (4 * r) × Vec 2 => centeredGeometryChart
          ((family Y.1).geom D) ρ (D.slotAnchor (m + 1) slot) Y.2) (P, Z)‖ ≤ B)
    (X : Vec 2 × Vec (2 + 4 * r)) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (independentFreshClampedTransferEntry r D family m ρ slot t i j) (X, 0)‖ ≤
      H.factorial * independentMovingTransferJetCost H B 0 * C ^ H := by
  let f := fun Y : ((Vec (4 * r) × Vec 2) × Vec 2) × Vec 2 =>
    let A := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
    (childTransition D slot t (A.recenter D (D.eps m • Y.2))
      (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ i j
  change ‖iteratedFDeriv ℝ n (f ∘ independentFreshClampedMovingTransferCoordinates r) (X, 0)‖ ≤ _
  have hcost : 0 ≤ independentMovingTransferJetCost H B 0 :=
    zero_le_one.trans (positiveJetCompositionBudget_ge_one _ _
      ((le_max_left 1 _).trans (le_max_left _ _)))
  have hh := finite_weighted_jet_composition_bound f
    (independentFreshClampedMovingTransferCoordinates r) H n hn
    ((independent_moving_transfer_entry_contDiff D hΛ hζ family hfamily m pslot hm hs hp
      harea ρ θ hscale slot t hf i j).of_le (by simp))
    ((independentFreshClampedMovingTransferCoordinates_contDiff r).of_le (by simp))
    (X, 0) 1 (independentMovingTransferJetCost H B 0) C zero_le_one hcost hC ?_ ?_
  · simpa only [one_mul] using hh
  · intro a ha
    rw [one_mul]
    apply independent_moving_transfer_entry_jet_production D hΛ hζ family hfamily m pslot hm hs hp harea
      ρ θ hθ hθ₁ hscale slot t hsmall hf H a ha B (1 / 2) 0 hB
      (independentFreshClampedMovingTransferCoordinates r (X, 0))
      (independentFreshGeometryClamp_slow_bound r X.2)
      (by change ‖(0 : Vec 2)‖ ≤ 0; simp only [norm_zero, le_refl]) ?_ i j
    intro b hb hbH Z hZ
    exact hchart _ (independentFreshGeometryClamp_center_strip r X.2) b hb hbH Z hZ
  · intro a ha haH
    exact independentFreshClampedMovingTransferCoordinates_positive_jets r H a ha haH C hC hclamp (X, 0)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Genuine primitive stream data supply the literal metric reserve with all choices before the data. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_scaled_metric_reserve_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps A.lastLevel → let a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
      let b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
      ∃ Q : IndependentParameterMetricReserve H
        (actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length) a b),
        (∀ n ≤ H, Q.budget n ≤ BG) ∧ ∀ t Y (ξ : Vec 2),
        (3 / 4) * ∑ i, ξ i ^ 2 ≤
          ∑ i, ∑ j, actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length) a b t Y i j * ξ i * ξ j ∧
        (∑ i, ∑ j, actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length) a b t Y i j * ξ i * ξ j) ≤
          (5 / 4) * ∑ i, ξ i ^ 2 := by
  choose χ C hχ hχrange hC hbχ hsupport hgerm hinvariant using independent_fresh_carrier_cutoff_invariant_exists
  let B := nativeWeakMixedMetricBudget H J 1
  have hB : 0 ≤ B := zero_le_one.trans (nativeWeakMixedMetricBudget_ge_one H J 1)
  let price := fun r n => independentCutoffUnitBudget ℝ (C r) (fun _ => B) n
  have hprice r n : 0 ≤ price r n := independentCutoffUnitBudget_nonneg (C r) (fun _ => B) (hC r) (fun _ => hB) n
  let BG := 1 + ∑ r ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), price r n
  have hBG : 1 ≤ BG := le_add_of_nonneg_right (Finset.sum_nonneg
    (fun r _ => Finset.sum_nonneg (fun n _ => hprice r n)))
  have hbound r n (hr : r ≤ J) (hn : n ≤ H) : price r n ≤ BG := by
    have hi : price r n ≤ ∑ k ∈ Finset.range (H + 1), price r k :=
      Finset.single_le_sum (fun k _ => hprice r k) (Finset.mem_range.mpr (by omega))
    have ho : (∑ k ∈ Finset.range (H + 1), price r k) ≤
        ∑ p ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), price p k :=
      Finset.single_le_sum (fun p _ => show 0 ≤ ∑ k ∈ Finset.range (H + 1), price p k from
        Finset.sum_nonneg (fun k _ => hprice p k)) (Finset.mem_range.mpr (by omega))
    exact (hi.trans ho).trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨M₀, hM₀, hjet⟩ := uniform_actual_family_coarse_scaled_metric_jets α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J H
  obtain ⟨M₁, _, he⟩ := uniform_actual_independent_coarse_scaled_metric_eventually_elliptic α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨χ, BG, (fun r => ⟨hχ r, hχrange r, hgerm r, hinvariant r⟩), hBG,
    max M₀ M₁, hM₀.trans (le_max_left _ _), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq hband A hbase hdepth bw j₀ hA ρ hρ hρle
  dsimp only
  let a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
  let b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hab : a ≤ b := weakData_lift_window D hΛ₁ hζ' hband A.ctxLevel A.slot
  have he' : ∀ t ∈ Icc a b, ∀ Y, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j ∧
      (∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2 :=
    he D hDα hDq hDΛ hDζ hseq hband A ((le_max_right _ _).trans hbase) hdepth bw j₀ hA ρ
  let Q := actualIndependentCoarseScaledMetricReserve H D hΛ₁ hζ' A bw j₀ A.ctxLevel A.slot hA ρ hρ
    (χ A.children.length) (hχ _) (hχrange _) (hsupport _) a b hab he' (C A.children.length)
    (hC _) (fun n _ Y => hbχ _ n Y) B hB
    (fun n hn t ht Y hY hS => hjet D hDα hDq hDΛ hDζ hseq hband A
      ((le_max_left _ _).trans hbase) hdepth bw j₀ hA ρ hρ hρle t ht Y hY hS n hn)
  refine ⟨Q, ?_, ?_⟩
  · intro n hn
    exact hbound A.children.length n hdepth hn
  · intro t Y ξ
    exact cutoffParameterMetric_clamped_elliptic (χ A.children.length) (hχrange _)
      (actualIndependentCoarseScaledMetric D A ρ) a b hab he' t Y ξ

end AVRegularity.EntryWeakProofs
end
end

section
/-! The physical slow-variable Piola matrix is the clamped transition with exact native normalization. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshClampedTransferMatrix (r : ℕ) (D : OCData)
    (family : Vec (4 * r) → RealChain) (m : ℕ) (ρ : ℝ) (slot : ℤ) (t : ℝ)
    (X : Vec 2 × Vec (2 + 4 * r)) (h : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => independentFreshClampedTransferEntry r D family m ρ slot t i j
    (X, (D.eps m)⁻¹ • h)

theorem independentFreshClampedTransferMatrix_normalized (r : ℕ) (D : OCData)
    (hΛ : 1 ≤ D.Λ) (family : Vec (4 * r) → RealChain) (m : ℕ) (ρ : ℝ)
    (slot : ℤ) (t : ℝ) (i j : Fin 2) :
    (fun X : (Vec 2 × Vec (2 + 4 * r)) × Vec 2 =>
      independentFreshClampedTransferMatrix r D family m ρ slot t X.1 (D.eps m • X.2) i j) =
      independentFreshClampedTransferEntry r D family m ρ slot t i j := by
  funext X
  change independentFreshClampedTransferEntry r D family m ρ slot t i j
    (X.1, (D.eps m)⁻¹ • (D.eps m • X.2)) = _
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [inv_smul_smul₀ hE]

theorem independentFreshClampedTransferMatrix_literal (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (family : Vec (4 * r) → RealChain) (m : ℕ) (ρ : ℝ) (slot : ℤ) (t : ℝ)
    (X : Vec 2 × Vec (2 + 4 * r)) (h : Vec 2) :
    let Y := independentFreshGeometryClamp r X.2
    let C := (family (independentStoredParameterProjection (4 * r) Y)).recenter D
      (ρ • independentIntrinsicSlowProjection (4 * r) Y)
    independentFreshClampedTransferMatrix r D family m ρ slot t X h =
      (childTransition D slot t (C.recenter D h) (X.1 + (D.eps m)⁻¹ • h))⁻¹ := by
  dsimp only
  ext i j
  change (childTransition D slot t
    (((family (independentStoredParameterProjection (4 * r) (independentFreshGeometryClamp r X.2))).recenter D
      (ρ • independentIntrinsicSlowProjection (4 * r) (independentFreshGeometryClamp r X.2))).recenter D
        (D.eps m • ((D.eps m)⁻¹ • h)))
    (X.1 + (D.eps m)⁻¹ • (D.eps m • ((D.eps m)⁻¹ • h))))⁻¹ i j = _
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [smul_inv_smul₀ hE]

theorem independentFreshClampedTransferMatrix_native (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (family : Vec (4 * r) → RealChain) (m : ℕ) (ρ : ℝ) (slot : ℤ) (t : ℝ)
    (X : Vec 2 × Vec (2 + 4 * r)) (hX : ‖independentFreshCarrierCoordinates r X.2‖ < 1 / 4)
    (h : Vec 2) :
    let C := (family (independentStoredParameterProjection (4 * r) X.2)).recenter D
      (ρ • independentIntrinsicSlowProjection (4 * r) X.2)
    independentFreshClampedTransferMatrix r D family m ρ slot t X h =
      (childTransition D slot t (C.recenter D h) (X.1 + (D.eps m)⁻¹ • h))⁻¹ := by
  rw [independentFreshClampedTransferMatrix_literal r D hΛ]
  rw [(independentFreshGeometryClamp_identity_germ r X.2 hX).self_of_nhds]
  rfl

theorem independentFreshClampedTransferMatrix_entry_contDiff (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Z : (Vec 2 × Vec (2 + 4 * r)) × Vec 2 =>
      independentFreshClampedTransferMatrix r D family m ρ slot t Z.1 Z.2 i j) :=
  (independentFreshClampedTransferEntry_contDiff r D hΛ hζ family hfamily m pslot hm hs hp
    harea ρ θ hscale slot t hf i j).comp
      (contDiff_fst.prodMk (contDiff_snd.const_smul (D.eps m)⁻¹))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier full-parameter productions produce the actual ordered inverse forcing at a common
matrix price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count hh n : ℕ} {BG BV BE B : ℝ}
  (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
  (P : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) (H + 2 * D + 2) q S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M p v u) B)

def independentLiftPredecessorSource (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) :
    ℝ → Vec 2 → Vec (2 + d) → ℝ :=
  independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
    A 1 S.G S.v (independentLiftPredecessorFields S P) hh n out inp

theorem independentLiftPredecessorSource_production (A : Vec 2 →L[ℝ] ℝ) (out inp : ι)
    (hn : 1 ≤ n) (hnD : n ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftPredecessorSource S P A out inp),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower S.M hh out inp *
        independentLiftCellProductionCost (2 + d) H D hh n count A 1 BG BV BE B := by
  exact independentLiftCoefficientCellSource_uniform_production H S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d) A 1 S.G S.v
    (independentLiftPredecessorFields S P) hh n hn hnD out inp S.metric_entries S.drift_entries
    (independentLiftPredecessorFields_reserve S P) S.edges S.M S.matrix_nonneg count BG BV BE B
    hBG hBV hBE hB S.metric_entries_bound S.drift_bound (independentLiftPredecessorFields_bound S P)
    S.edge_bound S.edge_maps S.edge_lengths

theorem independentLiftPredecessorSource_mean_zero (A : Vec 2 →L[ℝ] ℝ) (out inp : ι)
    (hn : 1 ≤ n) (hnD : n ≤ D) (t : ℝ) (Y : Vec (2 + d)) :
    fieldCellMean (fun z => independentLiftPredecessorSource S P A out inp t z Y) = 0 := by
  exact independent_lift_cell_source_from_centered_earlier_coefficients_mean_zero H S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d) A 1 S.G S.v
    (independentLiftPredecessorFields S P) hh n hn hnD out inp S.metric_entries S.drift_entries
    (independentLiftPredecessorFields_reserve S P) S.edges
    (fun p q hpq hq m α v u => independentLiftPredecessorFields_mean_zero S P p q hpq hq m α v u) t Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! The physical transition has exactly the normalized jet bound used by the Piola reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshClampedTransferMatrix_normalized_jet_bound (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hscale : D.eps m = ρ * θ)
    (slot : ℤ) (t : ℝ)
    (hsmall : |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2))
    (H n : ℕ) (hn : n ≤ H) (B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hclamp : ∀ a, 1 ≤ a → a ≤ H → ∀ Y,
      ‖iteratedFDeriv ℝ a (independentFreshGeometryClamp r) Y‖ ≤ C)
    (hchart : ∀ P, independentFreshCenterStrip P → ∀ a, 1 ≤ a → a ≤ H + 2 →
      ∀ Z : Vec 2, ‖Z‖ ≤ 1 / 2 + (0 + 2 * Real.pi) →
        ‖iteratedFDeriv ℝ a (fun Y : Vec (4 * r) × Vec 2 => centeredGeometryChart
          ((family Y.1).geom D) ρ (D.slotAnchor (m + 1) slot) Y.2) (P, Z)‖ ≤ B)
    (X : Vec 2 × Vec (2 + 4 * r)) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Z : (Vec 2 × Vec (2 + 4 * r)) × Vec 2 =>
      independentFreshClampedTransferMatrix r D family m ρ slot t Z.1 (D.eps m • Z.2) i j) (X, 0)‖ ≤
      H.factorial * independentMovingTransferJetCost H B 0 * C ^ H := by
  rw [independentFreshClampedTransferMatrix_normalized r D hΛ]
  exact independentFreshClampedTransferEntry_zero_jet_bound r D hΛ hζ family hfamily m pslot
    hm hs hp harea ρ θ hθ hθ₁ hscale slot t hsmall hf H n hn B C hB hC hclamp hchart X i j

end AVRegularity.EntryWeakProofs
end
end

section
/-! Geometric clamping preserves the exact phase-translation symmetries of native Piola matrices. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshClampedTransferMatrix_phase_translation (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (hm : ∀ p, (family p).ctxLevel = m)
    (pslot : ℤ) (hs : ∀ p, (family p).slot = pslot)
    (δ : Vec (2 + 4 * r)) (hδ : δ ∈ independentFreshPhaseTranslations r)
    (hg : ∀ p, (family (p + independentStoredParameterProjection (4 * r) δ)).geom D = (family p).geom D)
    (ρ : ℝ) (slot : ℤ) (t : ℝ) (z h : Vec 2) (Y : Vec (2 + 4 * r)) :
    independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y + δ) h =
      independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h := by
  let Z := independentFreshGeometryClamp r Y
  let p := independentStoredParameterProjection (4 * r) Z
  let q := p + independentStoredParameterProjection (4 * r) δ
  let x := ρ • independentIntrinsicSlowProjection (4 * r) Z
  let A := (family q).recenter D x
  let B := (family p).recenter D x
  obtain ⟨hAc, hAs, hAw⟩ := weak_recenter_ctxLevel_slot D (family q) x
  obtain ⟨hBc, hBs, hBw⟩ := weak_recenter_ctxLevel_slot D (family p) x
  have hAm : A.ctxLevel = m := hAc.trans (hm q)
  have hBm : B.ctxLevel = m := hBc.trans (hm p)
  have hslots : A.slot = B.slot := (hAs.trans (hs q)).trans (hBs.trans (hs p)).symm
  have hgeom : A.geom D = B.geom D :=
    realChain_recenter_geom_eq_of_geom_eq D _ _ (hfamily q) (hfamily p) (hg p) x
  have hh := weak_transfer_inverse_geometry_congr D hΛ hζ A B
    (hAw.mpr (hfamily q)) (hBw.mpr (hfamily p)) (hAm.trans hBm.symm) hslots hgeom
    slot t z ((D.eps m)⁻¹ • h)
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [hAm, hBm, smul_inv_smul₀ hE] at hh
  rw [independentFreshClampedTransferMatrix_literal r D hΛ,
    independentFreshClampedTransferMatrix_literal r D hΛ,
    independentFreshGeometryClamp_phase_translation r δ Y hδ,
    map_add, map_add, hδ.1, add_zero]
  exact hh

theorem independentFreshChain_geom_phase_translation (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (hp : ∀ p ∈ A.slots ++ List.ofFn slots, Odd p)
    (δ : Vec (2 + 4 * r)) (hδ : δ ∈ independentFreshPhaseTranslations r)
    (p : Vec (4 * r)) :
    (independentFreshChain A slots birthLength
      (p + independentStoredParameterProjection (4 * r) δ)).geom D =
      (independentFreshChain A slots birthLength p).geom D := by
  apply independentFreshChain_geom_eq_of_phase_lattice D hΛ A slots birthLength hp
  · intro j
    rw [map_add, hδ.2.1 j, add_zero]
  · intro j
    obtain ⟨n, hn⟩ := hδ.2.2 j
    exact ⟨n, by rw [map_add, hn]⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual real dual inverse relation produces independent readout reserves even at requested fast order zero. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ ((d : ℝ) + 1) ^ r * B) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      ∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z) := by
  let f : A → ℝ → Vec 2 → Vec d → ℂ := fun x t z Y => (ℓ (g x t z Y) : ℂ)
  let F : A → ℝ → Vec 2 → Vec d → ComplexCellVector := fun _ _ _ _ => 0
  let Qf := fun x => (Qg x).map Complex.ofRealCLM
  let QF : ∀ x, IndependentParameterSourceReserve H (F x) := fun _ =>
    IndependentParameterSourceReserve.zero H
  obtain ⟨B, hB, c, u, hsol, hu, Q, hb, hm⟩ :=
    family_variable_window_coordinate_word_classical_source_reserves_exist hab N K S hN hH hS hSK
      QG Qf QF BG (fun n => ‖Complex.ofRealCLM‖ * Bs n) (fun _ => 0) hBG
      (fun n => mul_nonneg (norm_nonneg _) (hBs n)) (fun _ => le_rfl) hQG
      (fun x n hn => mul_le_mul_of_nonneg_left (hQg x n hn) (norm_nonneg _))
      (fun _ _ _ => le_rfl) P hP v hv hPv V
      (fun x t ht z Y => by
        change (ℓ (g x t z Y) : ℂ) = 0
        rw [hg x t ht z Y, Complex.ofReal_zero])
      (fun _ _ _ _ _ => rfl)
  let fe := fun x => independentTimeWindowSource (Ioc (a x) (b x))
    (fun t z Y => realClassicalLift K (mapTorusHk Complex.reCLM (u x [] Y t)) z)
  have hs x Y w (hw : w.length ≤ N) := hsol x Y w hw
  have hsn x Y : IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (fun z => (ℓ (g x t z Y) : ℂ))) 0 (c x [] Y) := by
    have hh := hs x Y [] (by simp)
    rw [coordinateSourceWord_nil, coordinateSourceWord_nil, independentWordMetricFlux_nil,
      add_zero] at hh
    exact hh
  have hz x := coordinate_word_inverse_past_zero N (QG x) (hv x) (c x)
    (fun Y w hw => by
      have hh := hs x Y w hw
      rw [hP x Y, hPv x Y] at hh
      exact hh) (a x)
    (fun t ht z Y => by
      change (ℓ (g x t z Y) : ℂ) = 0
      rw [hg x t ht z Y, Complex.ofReal_zero])
    (fun _ _ _ _ => rfl)
  have he x Y (hY : Y ∈ U x) := independent_actual_inverse_higher_readout_eq_functional (hab x).le
    (g x) ℓ (Qg x) Y (hmean x · Y) (P x Y) (c x [] Y) (hsn x Y)
    (hz x Y [] (by simp) (a x) le_rfl) sZ (fun t z => C x t Y z) (hactual x Y hY)
    K (by omega) (u x [] Y) ((hu x [] (by simp) Y).2)
  refine ⟨B, hB, fe, Q, hb, hm, ?_, ?_⟩
  · intro x t ht z Y
    have hn : t ∉ Ioc (a x) (b x) := fun hh => (not_lt_of_ge ht) hh.1
    simp only [fe, independentTimeWindowSource, ite_eq_right hn]
  · intro x t ht Y hY z
    by_cases hta : (a x) < t
    · simpa only [fe, independentTimeWindowSource, ite_eq_left (show t ∈ Ioc (a x) (b x) from ⟨hta, ht.2⟩)]
        using congrFun (he x Y hY t ht) z
    · have hta : t = (a x) := le_antisymm (le_of_not_gt hta) ht.1
      subst t
      have hzero := realHigherCarrier_zero_of_value_zero K (c x [] Y) (a x) (u x [] Y (a x))
        ((hsn x Y).1.2.2.1 (a x) (mem_univ _)).1 ((hu x [] (by simp) Y).2 (a x) ⟨le_rfl, (hab x).le⟩)
        (hz x Y [] (by simp) (a x) le_rfl)
      have hc0 : (fun z => ℓ (C x (a x) Y z)) = 0 := (he x Y hY (a x) ⟨le_rfl, (hab x).le⟩).symm.trans hzero
      have hn : (a x) ∉ Ioc (a x) (b x) := fun hh => lt_irrefl (a x) hh.1
      dsimp only [fe, independentTimeWindowSource]
      rw [ite_eq_right hn]
      exact (congrFun hc0 z).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual real dual inverse relation produces independent readout reserves even at requested fast order zero. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_cross_natural_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (Rel : A → Vec d → Vec d → Prop)
    (hGR : ∀ x Y Z, Rel x Y Z → ∀ t, G x t Y = G x t Z)
    (hgR : ∀ x Y Z, Rel x Y Z → ∀ t z, ℓ (g x t z Y) = ℓ (g x t z Z))
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ ((d : ℝ) + 1) ^ r * B) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      (∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z)) ∧
      (∀ x t Y Z, Rel x Y Z → ∀ z, fext x t z Y = fext x t z Z) ∧
      ∀ x x' Y Z, a x = a x' → b x = b x' → v x = v x' →
        (∀ t, G x t Y = G x' t Z) →
        (∀ t z, ℓ (g x t z Y) = ℓ (g x' t z Z)) →
        ∀ t z, fext x t z Y = fext x' t z Z := by
  let f : A → ℝ → Vec 2 → Vec d → ℂ := fun x t z Y => (ℓ (g x t z Y) : ℂ)
  let F : A → ℝ → Vec 2 → Vec d → ComplexCellVector := fun _ _ _ _ => 0
  let Qf := fun x => (Qg x).map Complex.ofRealCLM
  let QF : ∀ x, IndependentParameterSourceReserve H (F x) := fun _ =>
    IndependentParameterSourceReserve.zero H
  obtain ⟨B, hB, c, u, hsol, hu, Q, hb, hm⟩ :=
    family_variable_window_coordinate_word_classical_source_reserves_exist hab N K S hN hH hS hSK
      QG Qf QF BG (fun n => ‖Complex.ofRealCLM‖ * Bs n) (fun _ => 0) hBG
      (fun n => mul_nonneg (norm_nonneg _) (hBs n)) (fun _ => le_rfl) hQG
      (fun x n hn => mul_le_mul_of_nonneg_left (hQg x n hn) (norm_nonneg _))
      (fun _ _ _ => le_rfl) P hP v hv hPv V
      (fun x t ht z Y => by
        change (ℓ (g x t z Y) : ℂ) = 0
        rw [hg x t ht z Y, Complex.ofReal_zero])
      (fun _ _ _ _ _ => rfl)
  let fe := fun x => independentTimeWindowSource (Ioc (a x) (b x))
    (fun t z Y => realClassicalLift K (mapTorusHk Complex.reCLM (u x [] Y t)) z)
  have hs x Y w (hw : w.length ≤ N) := hsol x Y w hw
  have hsn x Y : IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (fun z => (ℓ (g x t z Y) : ℂ))) 0 (c x [] Y) := by
    have hh := hs x Y [] (by simp)
    rw [coordinateSourceWord_nil, coordinateSourceWord_nil, independentWordMetricFlux_nil,
      add_zero] at hh
    exact hh
  have hz x := coordinate_word_inverse_past_zero N (QG x) (hv x) (c x)
    (fun Y w hw => by
      have hh := hs x Y w hw
      rw [hP x Y, hPv x Y] at hh
      exact hh) (a x)
    (fun t ht z Y => by
      change (ℓ (g x t z Y) : ℂ) = 0
      rw [hg x t ht z Y, Complex.ofReal_zero])
    (fun _ _ _ _ => rfl)
  have he x Y (hY : Y ∈ U x) := independent_actual_inverse_higher_readout_eq_functional (hab x).le
    (g x) ℓ (Qg x) Y (hmean x · Y) (P x Y) (c x [] Y) (hsn x Y)
    (hz x Y [] (by simp) (a x) le_rfl) sZ (fun t z => C x t Y z) (hactual x Y hY)
    K (by omega) (u x [] Y) ((hu x [] (by simp) Y).2)
  refine ⟨B, hB, fe, Q, hb, hm, ?_, ?_, ?_, ?_⟩
  · intro x t ht z Y
    have hn : t ∉ Ioc (a x) (b x) := fun hh => (not_lt_of_ge ht) hh.1
    simp only [fe, independentTimeWindowSource, ite_eq_right hn]
  · intro x t ht Y hY z
    by_cases hta : (a x) < t
    · simpa only [fe, independentTimeWindowSource, ite_eq_left (show t ∈ Ioc (a x) (b x) from ⟨hta, ht.2⟩)]
        using congrFun (he x Y hY t ht) z
    · have hta : t = (a x) := le_antisymm (le_of_not_gt hta) ht.1
      subst t
      have hzero := realHigherCarrier_zero_of_value_zero K (c x [] Y) (a x) (u x [] Y (a x))
        ((hsn x Y).1.2.2.1 (a x) (mem_univ _)).1 ((hu x [] (by simp) Y).2 (a x) ⟨le_rfl, (hab x).le⟩)
        (hz x Y [] (by simp) (a x) le_rfl)
      have hc0 : (fun z => ℓ (C x (a x) Y z)) = 0 := (he x Y hY (a x) ⟨le_rfl, (hab x).le⟩).symm.trans hzero
      have hn : (a x) ∉ Ioc (a x) (b x) := fun hh => lt_irrefl (a x) hh.1
      dsimp only [fe, independentTimeWindowSource]
      rw [ite_eq_right hn]
      exact (congrFun hc0 z).symm

  · intro x t Y Z hYZ z
    by_cases ht : t ∈ Ioc (a x) (b x)
    · have hy := hsn x Y
      have hz := hsn x Z
      rw [hP x Y, hPv x Y] at hy
      rw [hP x Z, hPv x Z] at hz
      have heq := independent_inverse_higher_readout_eq_of_data_eq
        ((QG x).metric Y) (hv x)
        (fun t => cellQ0 (fun z => (ℓ (g x t z Y) : ℂ)))
        (fun t => cellQ0 (fun z => (ℓ (g x t z Z) : ℂ)))
        0 0 (c x [] Y) (c x [] Z) hy hz
        (by funext t w; exact hGR x Y Z hYZ t)
        (by
          funext s
          congr 1
          funext w
          rw [hgR x Y Z hYZ]) rfl K t (u x [] Y t) (u x [] Z t)
        ((hu x [] (by simp) Y).2 t ⟨ht.1.le, ht.2⟩)
        ((hu x [] (by simp) Z).2 t ⟨ht.1.le, ht.2⟩)
      simp only [fe, independentTimeWindowSource, ite_eq_left ht]
      exact congrFun heq z
    · simp only [fe, independentTimeWindowSource, ite_eq_right ht]

  · intro x x' Y Z ha hb hvEq hG hforce t z
    by_cases ht : t ∈ Ioc (a x) (b x)
    · have ht' : t ∈ Ioc (a x') (b x') := by simpa only [← ha, ← hb] using ht
      have hy := hsn x Y
      have hz := hsn x' Z
      rw [hP x Y, hPv x Y] at hy
      rw [hP x' Z, hPv x' Z, ← hvEq] at hz
      have heq := independent_inverse_higher_readout_eq_of_data_eq
        ((QG x).metric Y) (hv x)
        (fun t => cellQ0 (fun z => (ℓ (g x t z Y) : ℂ)))
        (fun t => cellQ0 (fun z => (ℓ (g x' t z Z) : ℂ)))
        0 0 (c x [] Y) (c x' [] Z) hy hz
        (by funext t w; exact hG t)
        (by funext r; congr 1; funext w; rw [hforce r w]) rfl K t
        (u x [] Y t) (u x' [] Z t)
        ((hu x [] (by simp) Y).2 t ⟨ht.1.le, ht.2⟩)
        ((hu x' [] (by simp) Z).2 t ⟨ht'.1.le, ht'.2⟩)
      simp only [fe, independentTimeWindowSource, ite_eq_left ht, ite_eq_left ht']
      exact congrFun heq z
    · have ht' : t ∉ Ioc (a x') (b x') := by simpa only [← ha, ← hb] using ht
      simp only [fe, independentTimeWindowSource, ite_eq_right ht, ite_eq_right ht']

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native and off-carrier reference geometries have identical Piola matrices on a common open slow slice. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

theorem independentFreshClampedTransfer_geometry_congr (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family other : Vec (4 * r) → RealChain)
    (hfamily : ∀ p, (family p).WellSlotted) (hother : ∀ p, (other p).WellSlotted)
    (m : ℕ) (pslot : ℤ)
    (hfm : ∀ p, (family p).ctxLevel = m) (hom : ∀ p, (other p).ctxLevel = m)
    (hfs : ∀ p, (family p).slot = pslot) (hos : ∀ p, (other p).slot = pslot)
    (ρ : ℝ) (slot : ℤ) (Y Z : Vec (2 + 4 * r))
    (hY : ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4)
    (hZ : ‖independentFreshCarrierCoordinates r Z‖ < 1 / 4)
    (hgeom : (family (independentStoredParameterProjection (4 * r) Y)).geom D =
      (other (independentStoredParameterProjection (4 * r) Z)).geom D)
    (hslow : independentIntrinsicSlowProjection (4 * r) Y = independentIntrinsicSlowProjection (4 * r) Z) :
    ∀ t z h, independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h =
      independentFreshClampedTransferMatrix r D other m ρ slot t (z, Z) h := by
  intro t z h
  rw [independentFreshClampedTransferMatrix_native r D hΛ family m ρ slot t (z, Y) hY h,
    independentFreshClampedTransferMatrix_native r D hΛ other m ρ slot t (z, Z) hZ h]
  rw [hslow]
  let p := independentStoredParameterProjection (4 * r) Y
  let q := independentStoredParameterProjection (4 * r) Z
  let x := ρ • independentIntrinsicSlowProjection (4 * r) Z
  let A := (family p).recenter D x
  let B := (other q).recenter D x
  obtain ⟨hcA, hsA, hwA⟩ := weak_recenter_ctxLevel_slot D (family p) x
  obtain ⟨hcB, hsB, hwB⟩ := weak_recenter_ctxLevel_slot D (other q) x
  have hmA : A.ctxLevel = m := hcA.trans (hfm p)
  have hmB : B.ctxLevel = m := hcB.trans (hom q)
  have hsAB : A.slot = B.slot := (hsA.trans (hfs p)).trans (hsB.trans (hos q)).symm
  have hgAB : A.geom D = B.geom D :=
    realChain_recenter_geom_eq_of_geom_eq D _ _ (hfamily p) (hother q) hgeom x
  have hh := weak_transfer_inverse_geometry_congr D hΛ hζ A B
    (hwA.mpr (hfamily p)) (hwB.mpr (hother q)) (hmA.trans hmB.symm) hsAB hgAB
    slot t z ((D.eps m)⁻¹ • h)
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [hmA, hmB, smul_inv_smul₀ hE] at hh
  exact hh

theorem independentFreshClampedTransfer_geometry_on_reference_ball (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family other : Vec (4 * r) → RealChain)
    (hfamily : ∀ p, (family p).WellSlotted) (hother : ∀ p, (other p).WellSlotted)
    (m : ℕ) (pslot : ℤ)
    (hfm : ∀ p, (family p).ctxLevel = m) (hom : ∀ p, (other p).ctxLevel = m)
    (hfs : ∀ p, (family p).slot = pslot) (hos : ∀ p, (other p).slot = pslot)
    (ρ : ℝ) (P Q : Vec (4 * r))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (family P).geom D = (other Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) :
    ∀ slot t z h,
      independentFreshClampedTransferMatrix r D family m ρ slot t
        (z, independentIntrinsicParameterPacking (4 * r) X P) h =
      independentFreshClampedTransferMatrix r D other m ρ slot t
        (z, independentIntrinsicParameterPacking (4 * r) X Q) h := by
  have hbound (W : Vec (4 * r))
      (hW : ∀ j, ‖independentFreshChildProjection j false W‖ ≤ 3 / 16) :
      ‖independentFreshCarrierCoordinates r (independentIntrinsicParameterPacking (4 * r) X W)‖ < 1 / 4 := by
    apply lt_of_le_of_lt (independentFreshCarrierCoordinates_norm_le_of_bounds r _ (3 / 16)
      (by norm_num) ?_ ?_) (by norm_num)
    · intro j
      simpa only [independentIntrinsicParameterPacking_stored] using hW j
    · rw [independentIntrinsicParameterPacking_slow]
      exact hX.le.trans (by norm_num)
  intro slot
  apply independentFreshClampedTransfer_geometry_congr r D hΛ hζ family other hfamily hother
    m pslot hfm hom hfs hos ρ slot _ _ (hbound P hP) (hbound Q hQ)
  · simpa only [independentIntrinsicParameterPacking_stored] using hgeom
  · simp only [independentIntrinsicParameterPacking_slow]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Normalizing genuine forcing before inversion retains each positive stored birth weight. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_weighted_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 < θ x)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ θ x * Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      ∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z) := by
  let L := fun x => (θ x)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let gn := fun x t z Y => (θ x)⁻¹ • g x t z Y
  let Qn : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (gn x t z Y)) := fun x =>
    ((Qg x).map (L x)).congrSource (by
      funext t z Y
      change (θ x)⁻¹ • ℓ (g x t z Y) = ℓ ((θ x)⁻¹ • g x t z Y)
      exact (ℓ.map_smul _ _).symm)
  have hL x : ‖L x‖ = (θ x)⁻¹ := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hθ x))]
  have hQn x r (hr : r ≤ H) : (Qn x).budget r ≤ Bs r := by
    dsimp only [Qn]
    rw [IndependentParameterSourceReserve.congrSource_budget]
    change ‖L x‖ * (Qg x).budget r ≤ Bs r
    rw [hL]
    calc
      (θ x)⁻¹ * (Qg x).budget r ≤ (θ x)⁻¹ * (θ x * Bs r) :=
        mul_le_mul_of_nonneg_left (hQg x r hr) (inv_nonneg.mpr (hθ x).le)
      _ = Bs r := by rw [← mul_assoc, inv_mul_cancel₀ (hθ x).ne', one_mul]
  have han x Y (hY : Y ∈ U x) : IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => gn x t z Y) (fun t z => (θ x)⁻¹ • C x t Y z) := by
    have hh := cellFieldInverse_const_smul _ _ sZ (a x) (b x) 0 _ _ (hactual x Y hY) (θ x)⁻¹
    have hz : (fun z : Vec 2 => (θ x)⁻¹ • (0 : Vec 2 → E) z) = 0 := by
      funext z
      exact smul_zero _
    rw [hz] at hh
    exact hh
  obtain ⟨B, hB, fn, Qf, hb, hm, hp, he⟩ :=
    family_variable_window_functional_independent_meanfree_source_extensions_exist hab N K S hN hH hS hSK
      ℓ QG Qn BG Bs hBG hBs hQG hQn P hP v hv hPv V
      (fun x t ht z Y => by
        change ℓ ((θ x)⁻¹ • g x t z Y) = 0
        rw [map_smul, hg x t ht z Y, smul_zero])
      (fun x t Y => by
        change fieldCellMean (fun z => ℓ ((θ x)⁻¹ • g x t z Y)) = 0
        simp_rw [map_smul]
        rw [fieldCellMean_smul, hmean x t Y, smul_zero]) sZ
      (fun x t Y z => (θ x)⁻¹ • C x t Y z) U han
  let R := fun x => θ x • ContinuousLinearMap.id ℝ ℝ
  let fe := fun x t z Y => R x (fn x t z Y)
  let Qe := fun x => (Qf x).map (R x)
  refine ⟨B, hB, fe, Qe, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    change ‖R x‖ * (Qf x).budget r ≤ _
    have hR : ‖R x‖ = θ x := by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs, abs_of_pos (hθ x)]
    rw [hR]
    exact mul_le_mul_of_nonneg_left (hb x r hr) (hθ x).le
  · intro x t Y
    change fieldCellMean (fun z => θ x • fn x t z Y) = 0
    rw [fieldCellMean_smul, hm x t Y, smul_zero]
  · intro x t ht z Y
    change R x (fn x t z Y) = 0
    rw [hp x t ht z Y, map_zero]
  · intro x t ht Y hY z
    change θ x • fn x t z Y = ℓ (C x t Y z)
    rw [he x t ht Y hY z, map_smul, smul_smul, mul_inv_cancel₀ (hθ x).ne', one_smul]

end AVRegularity.EntryWeakProofs
end
end
end
