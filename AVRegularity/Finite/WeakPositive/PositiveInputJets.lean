-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.Finite.Assembly.WeakPositiveChartOfIngredients
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Readout.RepresentationEstimates
import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
import AVRegularity.Analysis.Convolution
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.WeakLift

/-! The scalar-power induction gives the weak parent-radius coefficient jets.
This is the arbitrary-radius adapter of the preservation argument's native grading theorem. -/

section
open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs

/-- The original uniform slow reserve pays every slot's smaller effective cap. -/
theorem weak_positive_slot_slow_reserve {N H U : ℕ} (P : WeakPositiveParameters N H U)
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ) :
    U + (N + A.cap) ≤ P.slowOrder + 4 * (H + 1) * (N + A.cap) ^ 2 := by
  have hbase : N + 2 ≤ N + A.cap := Nat.add_le_add_left A.cap_ge N
  have hsquare : (N + 2) ^ 2 ≤ (N + A.cap) ^ 2 := by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul hbase hbase
  exact (Nat.add_le_add_left (Nat.add_le_add_left A.cap_le N) U).trans
    (P.slow_reserve.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left (4 * (H + 1)) hsquare) P.slowOrder))

/-- All actual tested rectangular jets, with a component-count independent scalar budget. -/
theorem weak_positive_graded_recurrence : WeakGradedRecurrenceStatement := by
  intro N H U P D Dm j₀ bw i G π slot ρ A hh hhh n hn
  have hd := (setting_ambient_scalar_power_recurrence_data A.setting
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    (by omega) A.coeff A.sequence U (weak_positive_slot_slow_reserve P A) hh hhh n (by omega)).coefficient
  have he := hd.enlarge (div_nonneg A.setting.ρ_pos.le A.setting.E_pos.le) (fun v u =>
    mul_le_mul_of_nonneg_right
      (ambientCoefficientScalarBudget_le_native U (max P.fastOrder (P.fastOrder + 2))
        P.capMax H N P.CG P.Cw P.Cj A.cap hh n A.cap_le hhh hn)
      (finiteMatrixPower_nonneg _
        (physicalEdgeEnvelopeMatrix_nonneg π A.price A.setting.envelope.nonneg) hh v u))
  apply he.mono
  · unfold ambientDegreeSlowReserve
    omega
  · unfold ambientDegreeFastReserve
    have hf := P.fast_reserve
    omega
end

/-! Reuse the preservation argument's mass-conjugated Schur powers and finite-height sum,
with the actual weak slot price and the data-independent cap budget. -/

section
open Construction.Preservation.FullLift CycleComparison.Lift

/-- Each height costs only the uniform scalar coefficient budget times the source price power. -/
theorem weak_positive_height_matrix_budget {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ) (hh : ℕ) :
    HasRealSchurBudget (massConjugatedMatrix π (weakPositiveMatrix A hh))
      (nativeLiftScalarBudget U (max P.fastOrder (P.fastOrder + 2)) P.capMax H N
        P.CG P.Cw P.Cj * P.S ^ hh) := by
  classical
  have he : HasRealSchurBudget A.price P.S :=
    ⟨A.setting.envelope.nonneg, A.setting.envelope.row_sum, A.setting.envelope.col_sum⟩
  have hp := physicalEdgeEnvelopeMatrix_power_schur_budget π A.setting.mass_pos A.price
    P.S P.S_nonneg he hh
  convert hp.const_mul
    (nativeLiftScalarBudget U (max P.fastOrder (P.fastOrder + 2)) P.capMax H N P.CG P.Cw P.Cj)
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _)) using 1
  funext v u
  simp only [weakPositiveMatrix, massConjugatedMatrix]
  ring

/-- Sum all heights before testing the row and column budgets; no component or slot count. -/
theorem weak_positive_weighted_path_sums : WeakWeightedPathSumsStatement := by
  intro N H U P D Dm j₀ bw i G π slot ρ A
  have hb := finite_sum_real_schur_budget (Finset.range (H + 1))
    (fun hh => massConjugatedMatrix π (weakPositiveMatrix A hh))
    (fun hh => nativeLiftScalarBudget U (max P.fastOrder (P.fastOrder + 2)) P.capMax H N
      P.CG P.Cw P.Cj * P.S ^ hh)
    (fun hh _ => weak_positive_height_matrix_budget A hh)
  have heq : (fun v u => ∑ hh ∈ Finset.range (H + 1),
      massConjugatedMatrix π (weakPositiveMatrix A hh) v u) =
      massConjugatedMatrix π (fun v u => ∑ hh ∈ Finset.range (H + 1), weakPositiveMatrix A hh v u) := by
    funext v u
    simp only [massConjugatedMatrix, Finset.mul_sum]
  rw [heq] at hb
  simpa only [weakPositivePathCost, Finset.mul_sum] using hb
end

/-! The native polynomial identity of the slot lift transports the supplied arbitrary sequence to
the same effective recurrence. Inverse uniqueness and constant annihilation then
identify all tested coefficients and remove the input-amplitude coefficient. -/

section
open CycleComparison.Lift

/-- Changing the cap/window extension preserves the actual lift sequence on its original window. -/
theorem weak_positive_sequence_to_slot_lift {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ)
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hc : IsLiftSequence (weakPositiveNativeData i G slot ρ) sX sZ
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc) :
    IsLiftSequence A.Q sX sZ (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc := by
  obtain ⟨hzero, hheight, hcut, horder, hsym, hbox, hfield⟩ := hc
  refine ⟨hzero, hheight, hcut, horder, hsym, hbox, ?_⟩
  intro hh hhh n hn hnN a₀ ha₀ X
  have hi := hfield hh hhh n hn hnN a₀ ha₀ X
  rw [← A.metric_eq, ← A.drift_eq] at hi
  apply cellFieldInverse_source_congr_on (fun t => Matrix.of (A.Q.G t X)) A.Q.v sZ
    (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) (fun _ => 0)
    (fun t z => liftCellSource (weakPositiveNativeData i G slot ρ) Cc (fun _ => a₀) hh n t X z)
    (fun t z => liftCellSource A.Q Cc (fun _ => a₀) hh n t X z)
    (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z) _ hi
  intro t ht
  funext z
  exact (A.source_eq Cc (fun _ => a₀) hh n hnN t ht X z).symm

/-- Arbitrary stored reserves do not alter the coefficients; positive n annihilates constants. -/
theorem weak_positive_support_identification : WeakPositiveSupportIdentificationStatement := by
  intro N H U P D Dm j₀ bw i G π slot ρ A sX sZ Cc hc
  have hslotLift := weak_positive_sequence_to_slot_lift A sX sZ Cc hc
  refine ⟨liftSequence_coefficients_unique A.setting sX sZ
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    Cc A.coeff hslotLift
      (weak_positive_sequence_to_slot_lift A _ _ A.coeff A.ambient), ?_⟩
  intro hh hhh n hn _hnN a t ht X z v u
  exact liftSequence_zero_order_coefficient_zero A.setting
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    A.coeff A.sequence hh hhh n hn a t ht X z v u

/-- The positive response jets from the factory statement `WeakPlateauParentSettingStatement` and
the physical positive-derivative chart statement `WeakPositiveDerivativeChartStatement`; the
other ingredients are proved. -/
theorem weak_positive_response_jet_of_factory_and_chart
    (hf : WeakPlateauParentSettingStatement) (hc : WeakPositiveDerivativeChartStatement) :
    WeakPositiveResponseJetStatement :=
  weak_positive_response_jet_of_ingredients hf weak_positive_graded_recurrence
    weak_positive_support_identification hc weak_positive_weighted_path_sums

/-- The weak representation statement is reduced to the two hard inputs, with no change to the statement. -/
theorem weak_lift_rep_of_positive_factory_and_chart
    (hf : WeakPlateauParentSettingStatement) (hc : WeakPositiveDerivativeChartStatement) :
    Assembly.WeakLiftRepStatement :=
  weak_lift_rep_of_correction_jets (weak_lift_correction_jets_of_positive_response
    (weak_positive_response_jet_of_factory_and_chart hf hc))
end

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.WeakLift

/-! The single-passage case tests the factory at its literal root. Its native family has
no identity. A nonempty eddy alphabet still forces the ambient order through the outgoing
passage, even though the root itself needs no coefficient certificate. -/

open EntryWeakProofs Construction.Preservation.FullLift CycleComparison.Lift

/-- The intermediate family of every Jw=1 construction is precisely its edge-free root. -/
theorem weak_parent_case_root {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hJ : R.J = 1) : IsWeakRoot C.i 0 C.G := by
  have hi : C.M + R.J = C.i := by have := C.hi; have := C.hiJ; omega
  have hroot := C.construction.2.1
  rwa [hi] at hroot

/-- The high-degree eddy source is present whenever the response depth is positive.
Its tagged order cannot exceed the ambient order of the actual output family. -/
theorem weak_parent_eddy_identity_exists {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D ScalarH Dm bw j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hR : 1 ≤ Mn.R) (v : CompIn G.comps) :
    ∃ (v' u' : CompIn G'.comps) (γ : G'.fam.Γ v' u'),
      (G'.fam.identity v' u' γ).maxOrder = Mn.N + 1 := by
  obtain ⟨_, _, _, hcomps, _, e, idx, Cc, Cc0, _, _, _, he⟩ := hp
  let s : WeakSource G := .eddy v [] (Mn.N + 1)
  have hvalid : s.Valid Mn.N Mn.R Din := by
    exact ⟨Or.inl rfl, by change 0 < Mn.R; omega, by omega, le_rfl⟩
  have hletter : WordLetter.eddy (Mn.N + 1) ∈ weakAlphabet Mn.N :=
    Finset.mem_image.mpr ⟨Mn.N + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, rfl⟩
  have hword : [WordLetter.eddy (Mn.N + 1)] ∈ wordsUpTo (weakAlphabet Mn.N) Mn.R := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hR⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(WordLetter.eddy (Mn.N + 1), []), Finset.mem_product.mpr ?_, rfl⟩
    exact ⟨hletter, by simp only [wordsOfLength, Finset.mem_singleton]⟩
  have hsrc : s.srcComp G.level ∈ G'.comps := by
    rw [hcomps]
    change succComp G.level v.1 [] ∈ weakExtComps G.level Mn.N Mn.R G.comps
    simp only [succComp]
    exact Finset.mem_union_left _ v.2
  have htgt : s.tgtComp G.level ∈ G'.comps := by
    rw [hcomps]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨(v.1, [WordLetter.eddy (Mn.N + 1)]), Finset.mem_product.mpr ⟨v.2, hword⟩, rfl⟩
  let u' : CompIn G'.comps := ⟨s.srcComp G.level, hsrc⟩
  let v' : CompIn G'.comps := ⟨s.tgtComp G.level, htgt⟩
  let γ : G'.fam.Γ v' u' := (e v' u').symm ⟨s, hvalid, rfl, rfl⟩
  have hs : (e v' u' γ).1 = s :=
    congrArg Subtype.val ((e v' u').apply_symm_apply ⟨s, hvalid, rfl, rfl⟩)
  have ho := (ht v' u' γ).2
  rw [(he v' u' γ).1] at ho
  change (G'.fam.identity v' u' γ).maxOrder =
    ((e v' u' γ).1.weakTag P G.level rW Mn.η0).maxOrder at ho
  rw [hs] at ho
  exact ⟨v', u', γ, ho⟩

/-- The outgoing eddy identity's tagged degree fits in the actual ambient order. -/
theorem weak_parent_eddy_order_le_ambient {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D ScalarH Dm bw j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hR : 1 ≤ Mn.R) (v : CompIn G.comps) : Mn.N + 1 ≤ Dm := by
  obtain ⟨v', u', γ, ho⟩ := weak_parent_eddy_identity_exists P Mn rW Din G G' hp ht hN hR v
  rw [← ho]
  exact (G'.fam.identity v' u' γ).le_D

/-- An inherited one-edge source is present at the full outgoing menu degree. -/
theorem weak_parent_inherited_order_le_ambient {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D ScalarH Dm bw j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hDin : 1 ≤ Din) (v u : CompIn G.comps) (γ₀ : G.fam.Γ v u) :
    Mn.N + Din ≤ Dm := by
  obtain ⟨_, _, _, hcomps, _, e, idx, Cc, Cc0, _, _, _, he⟩ := hp
  let π : StagePath G 1 := { step := fun _ => ⟨v, u, γ₀⟩, joined := by intro j hj; omega }
  let s : WeakSource G := .inherited [] 1 π (Mn.N + Din)
  have hvalid : s.Valid Mn.N Mn.R Din := ⟨Or.inl rfl, le_rfl, by omega, le_rfl⟩
  have hsrc : s.srcComp G.level ∈ G'.comps := by
    rw [hcomps]
    change succComp G.level π.src [] ∈ weakExtComps G.level Mn.N Mn.R G.comps
    simpa only [succComp, weakExtComps, StagePath.src, Nat.zero_lt_succ, dite_true, π] using
      (Finset.mem_union_left
        ((G.comps ×ˢ wordsUpTo (weakAlphabet Mn.N) Mn.R).image
          (fun x => succComp G.level x.1 x.2)) u.2)
  have htgt : s.tgtComp G.level ∈ G'.comps := by
    rw [hcomps]
    change succComp G.level π.tgt [] ∈ weakExtComps G.level Mn.N Mn.R G.comps
    simpa only [succComp, weakExtComps, StagePath.tgt, Nat.zero_lt_succ, dite_true, π] using
      (Finset.mem_union_left
        ((G.comps ×ˢ wordsUpTo (weakAlphabet Mn.N) Mn.R).image
          (fun x => succComp G.level x.1 x.2)) v.2)
  let u' : CompIn G'.comps := ⟨s.srcComp G.level, hsrc⟩
  let v' : CompIn G'.comps := ⟨s.tgtComp G.level, htgt⟩
  let γ : G'.fam.Γ v' u' := (e v' u').symm ⟨s, hvalid, rfl, rfl⟩
  have hs : (e v' u' γ).1 = s :=
    congrArg Subtype.val ((e v' u').apply_symm_apply ⟨s, hvalid, rfl, rfl⟩)
  have ho := (ht v' u' γ).2
  rw [(he v' u' γ).1] at ho
  change (G'.fam.identity v' u' γ).maxOrder =
    ((e v' u' γ).1.weakTag P G.level rW Mn.η0).maxOrder at ho
  rw [hs] at ho
  change (G'.fam.identity v' u' γ).maxOrder = Mn.N + Din at ho
  rw [← ho]
  exact (G'.fam.identity v' u' γ).le_D

/-- The original root component survives every actual weak passage. -/
theorem weak_parent_root_component_mem {B : WeakParentBase} {R : WeakParentMenu B}
    {sX sZ : ℕ} (C : WeakParentCase R sX sZ) (j : ℕ) (hj : C.M ≤ j) (hjJ : j ≤ C.M + R.J) :
    (⟨0, []⟩ : Comp) ∈ (C.stage j).comps := by
  have main : ∀ n, n ≤ R.J → (⟨0, []⟩ : Comp) ∈ (C.stage (C.M + R.J - n)).comps := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Nat.sub_zero, C.construction.2.1.2.1, Finset.mem_singleton]
    | succ n ih =>
      intro hn
      have hp := (C.construction.2.2 (C.M + R.J - n) (by omega) (by omega)).1
      have heq : C.M + R.J - n - 1 = C.M + R.J - (n + 1) := by omega
      rw [← heq, hp.2.2.2.1]
      exact Finset.mem_union_left _ (ih (by omega))
  have heq : C.M + R.J - (C.M + R.J - j) = j := by omega
  simpa only [heq] using main (C.M + R.J - j) (by omega)

/-- The root-stage case of the ambient-cap alternative: `1 + J N ≤ D_m`. -/
theorem weak_parent_root_cap {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hJ : R.J = 1) (hR : 1 ≤ R.R) :
    1 + R.J * R.N ≤ C.Dm := by
  have hroot := weak_parent_case_root C hJ
  let v : CompIn C.G.comps := ⟨⟨0, []⟩, by rw [hroot.2.1]; simp⟩
  have hp := C.construction.2.2 C.i C.hi C.hiJ
  have hb := weak_parent_eddy_order_le_ambient C.PW
    (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) (C.D.termRW R.σ C.M)
    (1 + (C.M + R.J - C.i) * R.N) C.G (C.stage (C.i - 1)) hp.1 hp.2 R.hN hR v
  simpa only [hJ, one_mul, Nat.add_comm] using hb

/-- The actual construction forces the complete finite ambient cap when the eddy alphabet
has positive depth, including all J>=2 cases. -/
theorem weak_parent_case_cap {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hR : 1 ≤ R.R) : 1 + R.J * R.N ≤ C.Dm := by
  by_cases hJ : R.J = 1
  · exact weak_parent_root_cap C hJ hR
  have hJ2 : 2 ≤ R.J := by have := R.hJ; omega
  let Mn : WeakMenu := ⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩
  let v₀ : CompIn (C.stage (C.M + 2)).comps :=
    ⟨⟨0, []⟩, weak_parent_root_component_mem C (C.M + 2) (by omega) (by omega)⟩
  have hp2 := C.construction.2.2 (C.M + 2) (by omega) (by omega)
  have hid := weak_parent_eddy_identity_exists C.PW Mn
    (C.D.termRW R.σ C.M) (1 + (C.M + R.J - (C.M + 2)) * R.N)
    (C.stage (C.M + 2)) (C.stage (C.M + 2 - 1)) hp2.1 hp2.2 R.hN hR v₀
  have hp1 := C.construction.2.2 (C.M + 1) (by omega) (by omega)
  have hidx : C.M + 2 - 1 = C.M + 1 := by omega
  rw [hidx] at hid
  obtain ⟨v, u, γ, _ho⟩ := hid
  have hb := weak_parent_inherited_order_le_ambient C.PW Mn (C.D.termRW R.σ C.M)
    (1 + (C.M + R.J - (C.M + 1)) * R.N) (C.stage (C.M + 1))
    (C.stage (C.M + 1 - 1)) hp1.1 hp1.2 R.hN (by omega) v u γ
  have hidxJ : C.M + R.J - (C.M + 1) = R.J - 1 := by omega
  change R.N + (1 + (C.M + R.J - (C.M + 1)) * R.N) ≤ C.Dm at hb
  rw [hidxJ] at hb
  have hJsplit : R.J = (R.J - 1) + 1 := by omega
  have heq : 1 + R.J * R.N = R.N + (1 + (R.J - 1) * R.N) := by
    calc
      _ = 1 + ((R.J - 1) + 1) * R.N := congrArg (fun j => 1 + j * R.N) hJsplit
      _ = _ := by rw [Nat.add_mul, one_mul]; omega
  rw [heq]
  exact hb

/-- With zero response depth, strict component rank forces every stage identity type empty. -/
theorem weak_parent_case_empty_zero {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hR : R.R = 0) : ∀ v u, IsEmpty (C.G.fam.Γ v u) := by
  obtain ⟨hb, he⟩ := weakConstruction_rank_bounds C.PW
    (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
    (C.D.termRW R.σ C.M) C.stage C.construction C.i C.hi.le C.hiJ
  intro v u
  refine ⟨fun γ => ?_⟩
  have hv := hb v.1 v.2
  have hs := he v u γ
  simp only [hR, mul_zero] at hv
  omega

/-- Every actual native source vanishes above the data-independent finite menu cap. -/
theorem weak_parent_case_native_cap {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (slot : OddSlot) (v u : CompIn C.G.comps)
    (d : Finset.Icc 2 C.Dm) (hd : weakParentCap R < d.1) :
    (weakPositiveNativeData C.i C.G slot).edge v u d = [] := by
  have hb := weakConstruction_stage_maxOrderBound C.PW
    (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
    (C.D.termRW R.σ C.M) C.construction C.i C.hi.le C.hiJ
  have hfiber : C.G.fam.fiber slot (C.G.actual slot) v u d = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro γ _hγ
    have ho := hb v u γ
    change (C.G.fam.identity v u γ).maxOrder ≤ 1 + R.J * R.N at ho
    have hbound : 1 + R.J * R.N ≤ weakParentCap R := le_max_right _ _
    have hn : ¬d.1 ≤ (C.G.fam.identity v u γ).maxOrder := by omega
    simp only [hn, dite_false]
  simp only [weakPositiveNativeData, familyLiftData, liftEdges, hfiber, List.map_nil]

end AVRegularity.Finite.WeakLift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Positive physical jets restore the dimension-free representation cost. The proof
uses only finite sums, Schur amplitudes and abstract real powers, not stage data. -/

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

/-- Finite component restoration costs only the Schur budget, never the number of labels.
This is the input/output normalization used before applying the abstract profile estimate. -/
theorem positive_component_norm_restoration {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (M : ι → ι → ℝ) (Cpath C : ℝ)
    (hpath : 0 ≤ Cpath) (hC : 0 ≤ C)
    (hM : CycleComparison.Lift.HasRealSchurBudget
      (CycleComparison.Lift.massConjugatedMatrix π M) Cpath)
    (x y : ι → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hb : ∀ v, y v ≤ C * ∑ u, M v u * x u) :
    Real.sqrt (∑ v, (π v)⁻¹ * y v ^ 2) ≤
      C * Cpath * Real.sqrt (∑ u, (π u)⁻¹ * x u ^ 2) := by
  have hs : (∑ v, (π v)⁻¹ * y v ^ 2) ≤
      (C * Cpath) ^ 2 * ∑ u, (π u)⁻¹ * x u ^ 2 := by
    calc
      _ ≤ ∑ v, C ^ 2 * Cpath * ∑ u,
          CycleComparison.Lift.massConjugatedMatrix π M v u * ((π u)⁻¹ * x u ^ 2) :=
        Finset.sum_le_sum fun v _ =>
          Construction.Preservation.FullLift.weighted_positive_row_norm_square_le
            π hπ M Cpath C hC hM x v (y v) (hy v) (hb v)
      _ = C ^ 2 * Cpath * ∑ u,
          (∑ v, CycleComparison.Lift.massConjugatedMatrix π M v u) *
            ((π u)⁻¹ * x u ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_mul]
      _ ≤ C ^ 2 * Cpath * ∑ u, Cpath * ((π u)⁻¹ * x u ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_right (hM.col_sum u)
            (mul_nonneg (inv_nonneg.mpr (hπ u).le) (sq_nonneg _)))
          (mul_nonneg (sq_nonneg _) hpath)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hh := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hC hpath)] at hh
  exact hh

private theorem positive_profile_factorial_le {J : ℕ} {α : Fin 2 → ℕ}
    (hα : α ∈ multiIndicesBetween 1 J) : multiIndexFactorial α ≤ J.factorial := by
  have hJ : α 0 + α 1 ≤ J := (Finset.mem_filter.mp hα).2.2
  have hf := Nat.le_of_dvd (Nat.factorial_pos (α 0 + α 1))
    (Nat.factorial_mul_factorial_dvd_factorial (Nat.le_add_right (α 0) (α 1)))
  have hf' : (α 0).factorial * (α 1).factorial ≤ (α 0 + α 1).factorial := by
    simpa only [Nat.add_sub_cancel_left] using hf
  have hn : (α 0).factorial * (α 1).factorial ≤ J.factorial :=
    hf'.trans (Nat.factorial_le hJ)
  simp only [multiIndexFactorial, Fin.prod_univ_two]
  exact_mod_cast hn

private theorem positive_profile_weight_le {J : ℕ} {α : Fin 2 → ℕ}
    (hα : α ∈ multiIndicesBetween 1 J) {E s : ℝ} (hE : 0 < E) :
    E ^ (α 0 + α 1) ≤ E ^ s * J.factorial *
      (E ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) := by
  have hf := Finite.profile_factorial_one_le α
  have hfac : 0 < multiIndexFactorial α := zero_lt_one.trans_le hf
  have hsplit : E ^ (α 0 + α 1) =
      E ^ s * E ^ (((α 0 + α 1 : ℕ) : ℝ) - s) := by
    rw [← Real.rpow_add hE]
    simp only [add_sub_cancel, Real.rpow_natCast]
  calc
    _ = E ^ s * (E ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) *
        multiIndexFactorial α := by rw [mul_assoc, div_mul_cancel₀ _ hfac.ne']; exact hsplit
    _ ≤ E ^ s * (E ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) *
        J.factorial := mul_le_mul_of_nonneg_left (positive_profile_factorial_le hα)
      (mul_nonneg (Real.rpow_nonneg hE.le _) (div_nonneg (Real.rpow_nonneg hE.le _) hfac.le))
    _ = _ := by ring

/-- Removing the input factorials costs at most J!, independently of the ambient space. -/
theorem positive_profile_jet_sum_le {E s : ℝ} (hE : 0 < E) (J : ℕ) (F : Vec 2 → H) :
    positiveProfileJetSum E J F ≤
      ENNReal.ofReal (E ^ s * J.factorial) * profileSeminorm E J s F := by
  unfold positiveProfileJetSum profileSeminorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α hα
  calc
    _ ≤ ENNReal.ofReal (E ^ s * J.factorial *
        (E ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α)) *
        supNorm (partialDerivative α F) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (positive_profile_weight_le hα hE)) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hE.le _) (Nat.cast_nonneg _))]
      exact mul_assoc _ _ _

omit [NormedSpace ℝ H'] in
private theorem positive_pointwise_sup_le {E : ℝ} (hE : 0 < E) (J : ℕ)
    (F : Vec 2 → H) (g : Vec 2 → H') (w A : ℝ) (hw : 0 ≤ w) (hA : 0 ≤ A)
    (hbound : ∀ x, w * ‖g x‖ ≤ A *
      ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α F x‖) :
    ENNReal.ofReal w * supNorm g ≤ ENNReal.ofReal A * positiveProfileJetSum E J F := by
  unfold supNorm
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro x
  calc
    _ = ENNReal.ofReal (w * ‖g x‖) := by
      rw [ENNReal.ofReal_mul hw]
      congr 1
      exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal (A *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α F x‖) :=
      ENNReal.ofReal_le_ofReal (hbound x)
    _ = ENNReal.ofReal A * ∑ α ∈ multiIndicesBetween 1 J,
        ENNReal.ofReal (E ^ (α 0 + α 1)) * ‖partialDerivative α F x‖ₑ := by
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_sum_of_nonneg
        (fun α _ => mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _))]
      congr 1
      apply Finset.sum_congr rfl
      intro α _
      rw [ENNReal.ofReal_mul (pow_nonneg hE.le _), ofReal_norm]
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro α _
      exact mul_le_mul' le_rfl (le_iSup (fun x => ‖partialDerivative α F x‖ₑ) x)

/-- The physical positive gain is pure real algebra and is independent of all PDE data. -/
theorem positive_physical_gain {e E s : ℝ} (he : 0 < e) (hE : 0 < E) :
    e ^ (-s) * (e / E) * E ^ s = (e / E) ^ (1 - s) := by
  rw [Real.div_rpow he.le hE.le]
  rw [Real.rpow_sub he, Real.rpow_one, Real.rpow_neg he.le]
  rw [Real.rpow_sub hE, Real.rpow_one]
  have hes : 0 < e ^ s := Real.rpow_pos_of_pos he _
  have hEs : 0 < E ^ s := Real.rpow_pos_of_pos hE _
  field_simp

/-- The stage-free norm restoration ingredient is fully discharged. -/
theorem positive_chart_norm_restoration : PositiveChartNormRestorationStatement := by
  intro e E s K J C he hE hs hs1 hC H H' _ _ _ _ r corr hr hpoint
  have hA : 0 ≤ C * (e / E) := mul_nonneg hC (div_nonneg he.le hE.le)
  have hsum : positiveProfileJetSum E J r.value ≤
      ENNReal.ofReal (E ^ s * J.factorial) * representedSize s J E r :=
    (positive_profile_jet_sum_le hE J r.value).trans (mul_le_mul' le_rfl
      ((le_add_left le_rfl : profileSeminorm E J s r.value ≤
        supNorm r.value + profileSeminorm E J s r.value).trans
          (Readout.representation_profile_readout hs hs1 r hr)))
  have hfactor : ENNReal.ofReal (e ^ (-s)) * ENNReal.ofReal (C * (e / E)) *
      ENNReal.ofReal (E ^ s * J.factorial) =
      ENNReal.ofReal (C * J.factorial) * ENNReal.ofReal ((e / E) ^ (1 - s)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg he.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg he.le _) hA),
      ← ENNReal.ofReal_mul (mul_nonneg hC (Nat.cast_nonneg _))]
    congr 1
    calc
      _ = (C * J.factorial) * (e ^ (-s) * (e / E) * E ^ s) := by ring
      _ = _ := by rw [positive_physical_gain he hE]
  have hraw (g : Vec 2 → H') (w : ℝ) (hw : 0 ≤ w)
      (hb : ∀ x, w * ‖g x‖ ≤ C * (e / E) *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α r.value x‖) :
      ENNReal.ofReal (e ^ (-s)) * (ENNReal.ofReal w * supNorm g) ≤
        ENNReal.ofReal (C * J.factorial) * ENNReal.ofReal ((e / E) ^ (1 - s)) *
          representedSize s J E r := by
    calc
      _ ≤ ENNReal.ofReal (e ^ (-s)) *
          (ENNReal.ofReal (C * (e / E)) * positiveProfileJetSum E J r.value) :=
        mul_le_mul' le_rfl (positive_pointwise_sup_le hE J r.value g w _ hw hA hb)
      _ ≤ ENNReal.ofReal (e ^ (-s)) * (ENNReal.ofReal (C * (e / E)) *
          (ENNReal.ofReal (E ^ s * J.factorial) * representedSize s J E r)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)
      _ = _ := by rw [← mul_assoc, ← mul_assoc, hfactor]
  refine ⟨?_, ?_⟩
  · simpa only [ENNReal.ofReal_one, one_mul] using
      hraw corr 1 zero_le_one (fun x => by simpa only [one_mul] using hpoint.1 x)
  · intro α hα
    have hw := hraw (partialDerivative α corr) (e ^ (α 0 + α 1)) (pow_nonneg he.le _)
      (hpoint.2 α hα)
    have heq : e ^ (((α 0 + α 1 : ℕ) : ℝ) - s) = e ^ (-s) * e ^ (α 0 + α 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add he]
      congr 1
      ring
    rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg he.le _), mul_assoc]
    exact hw

/-- Keep the full exact chart leaf with only the two actual analytic/geometric inputs. -/
theorem weak_positive_derivative_chart_of_pointwise_and_regularity
    (hpoint : WeakPositivePointwiseChartStatement) (hreg : WeakPositiveChartRegularityStatement) :
    WeakPositiveDerivativeChartStatement :=
  weak_positive_derivative_chart_of_ingredients hpoint hreg positive_chart_norm_restoration

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.WeakLift

/-! Empty source families have the same polynomial recurrence at every ambient cap.
Thus a degree-two lift of the incoming weak root is also its literal native lift. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)] {D D' : ℕ}

private theorem weak_root_sourceCoeff_empty (edge : ConstituentEdges D h)
    (hz : ∀ v u d, edge v u d = []) (η t : ℝ) (j : ℕ)
    (Φ : Vec 2 → Vec 2 → ∀ v, h v) : sourceCoeff edge η j t Φ = 0 := by
  have hf (ε : ℝ) (k : Fin 2) : sourceFlux edge η ε t Φ k = 0 := by
    funext X z v
    simp only [sourceFlux, hz, List.map_nil, List.sum_nil, Finset.sum_const_zero,
      Pi.zero_apply]
  have hop (ε : ℝ) : sourceOp edge η ε t Φ = 0 := by
    unfold sourceOp
    simp_rw [hf]
    funext X z
    simp only [dEps, fastPartial, slowPartial, Pi.zero_apply,
      fderiv_const_apply, zero_apply, smul_zero, add_zero,
      Finset.sum_const_zero]
  funext X z
  unfold sourceCoeff
  simp only [hop, Pi.zero_apply, iteratedDeriv_const, ite_self, smul_zero]

/-- All centered recursion sources coincide for two empty families with the same metric,
contrast and drift, without an ambient-order restriction or a reserve hypothesis. -/
theorem weak_root_source_degree_congr (Q : LiftOperatorData ι h D)
    (Q' : LiftOperatorData ι h D') (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (hz : ∀ v u d, Q.edge v u d = []) (hz' : ∀ v u d, Q'.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ v, h v) (hh n : ℕ) (t : ℝ) :
    liftCellSource Q Cc f hh n t = liftCellSource Q' Cc f hh n t := by
  have hA (p m : ℕ) (s : ℝ) : liftA Q Cc f p m s = liftA Q' Cc f p m s := by
    unfold liftA
    simp only [hη, hG, hv, weak_root_sourceCoeff_empty Q.edge hz,
      weak_root_sourceCoeff_empty Q'.edge hz', Pi.zero_apply, Finset.sum_const_zero]
  have hm (p m : ℕ) : liftMean Q Cc f p m = liftMean Q' Cc f p m := by
    funext s X
    simp only [liftMean, hA]
  funext X z
  unfold liftCellSource
  simp only [hA, hm]

/-- Transport a full graded sequence between empty source menus, including positive grades. -/
theorem weak_root_sequence_degree_congr [∀ v, FiniteDimensional ℝ (h v)]
    (Q : LiftOperatorData ι h D) (Q' : LiftOperatorData ι h D')
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (hz : ∀ v u d, Q.edge v u d = []) (hz' : ∀ v u d, Q'.edge v u d = [])
    (sX sZ N H : ℕ) (a b : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc) : IsLiftSequence Q' sX sZ a b N H Cc := by
  obtain ⟨hzero, hheight, hcut, horder, hsym, hbox, hfield⟩ := hc
  refine ⟨hzero, hheight, hcut, horder, hsym, hbox, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hi := hfield hh hhh n hn hnN f hf X
  rw [hG, hv] at hi
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t _ht
  funext z
  exact congrFun (congrFun
    (weak_root_source_degree_congr Q Q' hη hG hv hz hz' Cc (fun _ => f) hh n t) X) z

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Finite.WeakLift

/-! Physical slow-lattice invariance for the radius-generic actual weak slot lift.
Ambient translation is transported to the effective setting, avoiding any artificial
comparison between its padded cap and the original ambient degree. -/

open CycleComparison.Lift CycleComparison.LiftMeanEntrywise Construction.Preservation.FullLift

/-- The native ambient recurrence and effective-setting uniqueness preserve the slow lattice. -/
theorem weak_positive_slot_coefficient_slow_shift {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ) (hcell1 : D.cellScaleSq 1 ≠ 0) (hlevel : G.level = i)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (i - 1)))
    (p : Fin 2 → ℤ) (hh : ℕ) (hhh : hh ≤ H) (n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1))
    (X z : Vec 2) (v u : CompIn G.comps) :
    A.coeff hh n m α t (X + ρ⁻¹ • latticeShift p) z v u = A.coeff hh n m α t X z v u := by
  let T := ρ⁻¹ • latticeShift p
  have hg : ∀ s Y a b, (weakPositiveNativeData i G slot ρ).G s (Y + T) a b =
      (weakPositiveNativeData i G slot ρ).G s Y a b := by
    intro s Y a b
    by_cases hi : 1 ≤ i
    · exact congrFun (congrFun (native_familyLiftData_metric_shift D i hi slot.1
        A.setting.ρ_pos.ne' (G.fam.fiber slot (G.actual slot)) p s Y) a) b
    · have hi0 : i = 0 := by omega
      let s' := D.cellScaleSq 0 * s / D.cellScaleSq 1
      have ht : D.cellScaleSq 1 * s' = D.cellScaleSq 0 * s := by
        dsimp only [s']; field_simp [hcell1]
      have hmetric := congrFun (congrFun (native_familyLiftData_metric_shift D 1 le_rfl slot.1
        A.setting.ρ_pos.ne' (G.fam.fiber slot (G.actual slot)) p s' Y) a) b
      simpa only [weakPositiveNativeData, familyLiftData, nativeChain, Nat.reduceSub, ht, hi0, T] using hmetric
  have he : ∀ v' u' d, ∀ γ ∈ (weakPositiveNativeData i G slot ρ).edge v' u' d,
      ∀ β s Y w, γ.coeff β s (Y + T) w = γ.coeff β s Y w := by
    intro v' u' d γ hγ β s Y w
    have htorus' : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) := by
      simpa only [hlevel] using htorus
    have hγ' : γ ∈ (familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
        (G.fam.fiber slot (G.actual slot))).edge v' u' d := by
      simpa only [weakPositiveNativeData, hlevel] using hγ
    exact native_familyLiftData_edge_coeff_shift G htorus' slot A.setting.ρ_pos.ne'
      p v' u' d γ hγ' β s Y w
  have hs := isLiftSequence_slowShift (weakPositiveNativeData i G slot ρ)
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H A.coeff A.ambient T hg he
  have hQ := weak_positive_sequence_to_slot_lift A _ _ (slowShiftSequence T A.coeff) hs
  have hu := liftSequence_coefficients_unique A.setting
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    (P.slowOrder + A.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
    A.coeff (slowShiftSequence T A.coeff) A.sequence hQ hh hhh n m α t ht X z v u
  exact hu.symm

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.WeakLift

/-! Spatial regularity and physical periodicity of the actual positive weak glued correction.
The generic pulse theorem reuses the preservation argument; normalization reuses the terminal case. -/

open CycleComparison.Lift Construction.Preservation.FullLift EntryWeakProofs

/-- The value of a finite representation has its reserved smoothness and periodicity. -/
theorem representation_value_contDiff_periodic {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {e : ℝ} {K : ℕ} (r : Representation H) (hr : IsRepresentationAt e K r) :
    ContDiff ℝ (K : ℕ) r.value ∧ IsZ2Periodic r.value := by
  let gs := r.profiles.map Prod.fst
  have he : r.value = r.base + gs.sum := by
    funext x
    change r.base x + (r.profiles.map fun p => p.1 x).sum = r.base x + gs.sum x
    rw [show r.profiles.map (fun p => p.1 x) = gs.map (fun G => G x) by
      simp only [gs, List.map_map, Function.comp_def]]
    rw [Readout.list_eval_sum]
  constructor
  · rw [he]
    exact hr.2.2.1.add (Readout.list_sum_contDiff K gs (by
      intro F hF
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
      exact (hr.2.2.2.2 p hp).1))
  · intro p x
    change r.base (x + latticeShift p) + (r.profiles.map fun q => q.1 (x + latticeShift p)).sum =
      r.base x + (r.profiles.map fun q => q.1 x).sum
    rw [hr.2.2.2.1 p x]
    congr 1
    apply congrArg List.sum
    exact List.map_congr_left fun q hq => (hr.2.2.2.2 q hq).2.1 p x

/-- Regularity of the literal scalar input array recovered from its normalized representation. -/
theorem weak_positive_chart_input_regular {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) :
    ContDiff ℝ (C.K + N : ℕ) (fun x v => C.f v x) ∧ IsZ2Periodic (fun x v => C.f v x) := by
  obtain ⟨hr, hp⟩ := representation_value_contDiff_periodic C.r C.representation
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn C.G.comps => ℝ)
  let F : Vec 2 → (CompIn C.G.comps → ℝ) := fun x v => Real.sqrt (C.π v) * T (C.r.value x) v
  have he : F = fun x v => C.f v x := by
    funext x v
    rw [show F x v = Real.sqrt (C.π v) * T (C.r.value x) v from rfl, C.value]
    change Real.sqrt (C.π v) * ((Real.sqrt (C.π v))⁻¹ * C.f v x) = C.f v x
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (C.mass v)).ne', one_mul]
  constructor
  · rw [← he]
    exact contDiff_pi.mpr fun v => contDiff_const.mul
      ((contDiff_apply ℝ ℝ v).comp (T.contDiff.comp hr))
  · rw [← he]
    intro p x
    exact congrArg (fun y : CompSpace C.G.comps => fun v => Real.sqrt (C.π v) * T y v) (hp p x)

/-- The actual positive pulse with its physical chart and input frozen at the output time. -/
def weakPositiveChartPulse {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (k : ℤ) : Vec 2 → (CompIn C.G.comps → ℝ) :=
  pulsePhysicalLift (C.D.cellScaleSq C.i) (C.D.eps (C.i - 1)) (C.D.eps C.i)
    (C.D.eps C.i / C.D.eps (C.i - 1)) N H (positiveLiftCoefficients C.coeff k)
    (fun _ y => C.D.flowOf (C.i - 1) C.t y (C.D.slotAnchor C.i k))
    (fun _ y => C.D.flowOf (C.i - 1) (C.D.slotAnchor C.i k) y C.t)
    (fun _ y v => C.f v y) C.t

private def weak_positive_original_pulse {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (k : ℤ) : Vec 2 → (CompIn C.G.comps → ℝ) :=
  pulsePhysicalLift (C.D.cellScaleSq C.i) (C.D.eps (C.i - 1)) (C.D.eps C.i)
    (C.D.eps C.i / C.D.eps (C.i - 1)) N H (positiveLiftCoefficients C.coeff k)
    (fun s y => C.D.flowOf (C.i - 1) s y (C.D.slotAnchor C.i k))
    (fun s y => C.D.flowOf (C.i - 1) (C.D.slotAnchor C.i k) y s)
    (fun _ y v => C.f v y) C.t

private theorem weak_positive_original_pulse_eq {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (k : ℤ) :
    weak_positive_original_pulse C k = weakPositiveChartPulse C k := by
  have hΛ : 1 ≤ C.D.Λ := by have := C.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos C.D hΛ C.geometry.fast C.geometry.band C.i
  unfold weak_positive_original_pulse weakPositiveChartPulse
  rw [pulsePhysicalLift_freeze_time]
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- An active physical pulse lies in the original cell-time window. -/
theorem weak_positive_chart_active_time {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (slot : OddSlot)
    (hcut : ocCutoff C.D.α C.D.q C.D.Λ C.i slot.1 C.t ≠ 0) :
    (C.D.cellScaleSq C.i)⁻¹ * C.t ∈
      Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1) := by
  have hΛ : 1 ≤ C.D.Λ := by have := C.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos C.D hΛ C.geometry.fast C.geometry.band C.i
  have hτ := Construction.Stream.ocTau_pos (α := C.D.α) (q := C.D.q) (m := C.i) hΛ
  have hp := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  change C.D.slotStart C.i slot.1 / C.D.cellScaleSq C.i ≤ _ ∧
    _ ≤ (((slot.1 : ℝ) + 61 / 48) * ocTau C.D.α C.D.q C.D.Λ C.i) / C.D.cellScaleSq C.i
  rw [mul_comm, ← div_eq_mul_inv]
  exact ⟨(div_le_div_iff_of_pos_right hc).mpr hp.1,
    (div_le_div_iff_of_pos_right hc).mpr hp.2⟩

/-- Active positive pulses are regular and physically periodic before finite convex gluing. -/
theorem weak_positive_chart_pulse_regular {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (slot : OddSlot)
    (hcut : ocCutoff C.D.α C.D.q C.D.Λ C.i slot.1 C.t ≠ 0) :
    (∀ v, ContDiff ℝ (C.K : ℕ) (fun Y => weakPositiveChartPulse C slot.1 Y v)) ∧
      IsZ2Periodic (weakPositiveChartPulse C slot.1) := by
  obtain ⟨hf, hfper⟩ := weak_positive_chart_input_regular C
  have hΛ : 1 ≤ C.D.Λ := by have := C.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos C.D hΛ C.geometry.fast C.geometry.band C.i
  let f := fun x v => C.f v x
  let Φ := fun k x => C.D.flowOf (C.i - 1) C.t x (C.D.slotAnchor C.i k)
  let Ψ := fun k x => C.D.flowOf (C.i - 1) (C.D.slotAnchor C.i k) x C.t
  have hΦ (k : ℤ) : ContDiff ℝ (C.K + N : ℕ) (Φ k) :=
    (CycleReference.streamFlow_spatial_smooth (C.D.hΦ (C.i - 1)) C.t (C.D.slotAnchor C.i k)).of_le (by simp)
  have hΨ (k : ℤ) : ContDiff ℝ (C.K : ℕ) (Ψ k) :=
    (CycleReference.streamFlow_spatial_smooth (C.D.hΦ (C.i - 1)) (C.D.slotAnchor C.i k) C.t).of_le (by simp)
  have ht := weak_positive_chart_active_time C slot hcut
  have hid := (C.identified slot).1
  constructor
  · intro v
    apply pulsePhysicalLift_static_contDiff_of_boxes _ _ _ _ N H C.K _ _ _ _ C.t hf (hΦ _) (hΨ _)
    intro hh hhh n hn m hm α v' u'
    by_cases hn0 : n = 0
    · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
      exact IsBoxSmooth.zero
    · have he : (fun X z => positiveLiftCoefficients C.coeff slot.1 hh n m α
          ((C.D.cellScaleSq C.i)⁻¹ * C.t) X z v' u') =
        fun X z => (C.slotLift slot).coeff hh n m α ((C.D.cellScaleSq C.i)⁻¹ * C.t) X z v' u' := by
        funext X z
        exact (by simpa only [positiveLiftCoefficients, hn0, ite_false] using hid hh hhh n m α _ ht X z v' u')
      rw [he]
      exact ((C.graded slot hh hhh n hn).box m hm α v' u' _ ht).mono C.K_le C.K_le
  · obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast C.D.q C.D.Λ C.i
    apply pulsePhysicalLift_static_periodic _ _ _ _ N H _ _ _ f C.t
      (C.slotLift slot).setting.ρ_pos.ne' hJ
      (fun p Y => native_flow_latticeShift C.D _ _ _ p Y)
      (fun p Y => native_flow_latticeShift C.D _ _ _ p Y) hfper
    · intro hh hhh n hn m _hm α p X z v u
      by_cases hn0 : n = 0
      · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
      · simp only [positiveLiftCoefficients, hn0, ite_false]
        rw [hid hh hhh n m α _ ht, hid hh hhh n m α _ ht]
        exact weak_positive_slot_coefficient_slow_shift (C.slotLift slot)
          (weakData_cellScaleSq_pos C.D hΛ C.geometry.fast C.geometry.band 1).ne' C.geometry.level C.geometry.torus p hh hhh n m α _ ht X z v u
    · intro hh hhh n _hn m _hm α X v u
      by_cases hn0 : n = 0
      · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
        exact fun _ _ => rfl
      · simp only [positiveLiftCoefficients, hn0, ite_false]
        intro p z
        change C.coeff slot.1 hh n m α ((C.D.cellScaleSq C.i)⁻¹ * C.t) X
          (z + latticeShift p) v u = C.coeff slot.1 hh n m α ((C.D.cellScaleSq C.i)⁻¹ * C.t) X z v u
        rw [hid hh hhh n m α _ ht, hid hh hhh n m α _ ht]
        exact ((C.slotLift slot).ambient.2.2.2.2.2.1 hh hhh n m α v u _ ht).2 X p z

/-- The literal correction is the normalized convex sum of its time-frozen pulses. -/
theorem weak_positive_chart_correction_eq_pulses {N H U : ℕ}
    {P : WeakPositiveParameters N H U} (C : WeakPositiveChartCase P) :
    C.correction = fun x => ∑ k ∈ ocObsPulses C.D.α C.D.q C.D.Λ C.i C.t C.t,
      ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t • toCompSpace C.π (weakPositiveChartPulse C k x) := by
  funext x
  apply PiLp.ext
  intro v
  change (Real.sqrt (C.π v))⁻¹ * weakGluedLift C.i N H C.G
    (positiveLiftCoefficients C.coeff) C.t C.f v x = _
  simp only [weakGluedLift, gluedLift, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (Real.sqrt (C.π v))⁻¹ * (∑ k ∈ ocObsPulses C.D.α C.D.q C.D.Λ C.i C.t C.t,
    ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t * weak_positive_original_pulse C k x v) = _
  simp_rw [weak_positive_original_pulse_eq]
  rw [Finset.mul_sum, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change (Real.sqrt (C.π v))⁻¹ * (ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t *
    weakPositiveChartPulse C k x v) = ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t *
      ((Real.sqrt (C.π v))⁻¹ * weakPositiveChartPulse C k x v)
  ring

/-- The regularity and periodicity input, with the actual array identified on active windows. -/
theorem weak_positive_chart_regularity : WeakPositiveChartRegularityStatement := by
  intro N H U P C
  let kset := ocObsPulses C.D.α C.D.q C.D.Λ C.i C.t C.t
  have hodd (k : ℤ) (hk : k ∈ kset) : Odd k := (Finset.mem_filter.mp hk).2.1
  apply EntryTerminal.Ingredients.compField_contDiff_periodic C.π C.K
  · intro v
    change ContDiff ℝ (C.K : ℕ) (fun x => weakGluedLift C.i N H C.G
      (positiveLiftCoefficients C.coeff) C.t C.f v x)
    simp only [weakGluedLift, gluedLift, Finset.sum_apply, Pi.smul_apply]
    change ContDiff ℝ (C.K : ℕ) (fun x => ∑ k ∈ kset,
      ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t • weak_positive_original_pulse C k x v)
    simp_rw [weak_positive_original_pulse_eq C]
    apply ContDiff.sum
    intro k hk
    by_cases hw : ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t = 0
    · simpa only [hw, zero_smul] using (contDiff_const : ContDiff ℝ (C.K : ℕ) (fun _ : Vec 2 => (0 : ℝ)))
    · exact ((weak_positive_chart_pulse_regular C ⟨k, hodd k hk⟩ hw).1 v).const_smul _
  · intro v p x
    change weakGluedLift C.i N H C.G (positiveLiftCoefficients C.coeff) C.t C.f v
      (x + latticeShift p) = weakGluedLift C.i N H C.G (positiveLiftCoefficients C.coeff) C.t C.f v x
    simp only [weakGluedLift, gluedLift, Finset.sum_apply, Pi.smul_apply]
    change (∑ k ∈ kset, ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t •
      weak_positive_original_pulse C k (x + latticeShift p) v) =
      ∑ k ∈ kset, ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t • weak_positive_original_pulse C k x v
    simp_rw [weak_positive_original_pulse_eq C]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hw : ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t = 0
    · simp only [hw, zero_smul]
    · exact congrArg (fun y => ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t • y)
        (congrFun ((weak_positive_chart_pulse_regular C ⟨k, hodd k hk⟩ hw).2 p x) v)

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.WeakLift

/-! Finite positive input jets in the exact coordinate derivatives of the physical field. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The sorted coordinate word is the coordinate derivative `partialDerivative ![a, b]`, even
before regularity. -/
theorem weakPositive_sorted_word_eq_partial (a b : ℕ) (f : Vec 2 → V) :
    orderedDerivative (Fin.append (fun _ : Fin a => (0 : Fin 2))
      (fun _ : Fin b => (1 : Fin 2))) f = partialDerivative ![a, b] f := by
  have hrepl (j : Fin 2) (n : ℕ) (g : Vec 2 → V) :
      (List.replicate n j).foldl (fun g' i => Readout.along (basisVec i) g') g =
        (Readout.along (basisVec j))^[n] g := by
    induction n generalizing g with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]
  unfold orderedDerivative
  rw [List.ofFn_fin_append, List.ofFn_const, List.ofFn_const, List.foldl_append]
  change (List.replicate b (1 : Fin 2)).foldl
    (fun g' i => Readout.along (basisVec i) g')
    ((List.replicate a (0 : Fin 2)).foldl (fun g' i => Readout.along (basisVec i) g') f) = _
  rw [hrepl, hrepl]
  rfl

/-- Symmetry identifies the sorted multilinear partial with the coordinate derivative. -/
theorem weakPositive_thetaPartial_eq_partial (a b : ℕ) (f : Vec 2 → V)
    (hf : ContDiff ℝ ((a + b : ℕ) : ℕ∞) f) :
    thetaPartial a b f = partialDerivative ![a, b] f := by
  rw [← weakPositive_sorted_word_eq_partial a b f,
    orderedDerivative_eq_iteratedFDeriv _ hf]
  funext x
  unfold thetaPartial
  have he : (Fin.append (fun _ : Fin a => basisVec (0 : Fin 2))
      (fun _ : Fin b => basisVec (1 : Fin 2))) =
      fun i => basisVec ((Fin.append (fun _ : Fin a => (0 : Fin 2))
        (fun _ : Fin b => (1 : Fin 2))) i) := by
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  rw [he]
  exact (Analysis.iteratedFDeriv_comp_perm_of_contDiff (a + b) hf x
    (fun i => basisVec ((Fin.append (fun _ : Fin a => (0 : Fin 2))
      (fun _ : Fin b => (1 : Fin 2))) i)) (Fin.revPerm : Equiv.Perm (Fin (a + b)))).symm

/-- A single positive full derivative is controlled by the finite physical partial jet sum. -/
theorem weakPositive_scaled_full_jet_le {J j : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hj : 1 ≤ j) (hjJ : j ≤ J) (f : Vec 2 → V)
    (hf : ContDiff ℝ (J : ℕ∞) f) (x : Vec 2) :
    E ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
      (2 : ℝ) ^ J * (J + 1) *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
  let B := ∑ α ∈ multiIndicesBetween 1 J,
    E ^ (α 0 + α 1) * ‖partialDerivative α f x‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hE _) (norm_nonneg _)
  have ha (a : ℕ) (ha : a ∈ Finset.range (j + 1)) :
      E ^ j * ‖thetaPartial a (j - a) f x‖ ≤ B := by
    have haj : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have he : a + (j - a) = j := Nat.add_sub_of_le haj
    have hmem : ![a, j - a] ∈ multiIndicesBetween 1 J := by
      simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range, Matrix.cons_val_zero, Matrix.cons_val_one, he]
      refine ⟨?_, hj, hjJ⟩
      intro i
      fin_cases i <;> simp <;> omega
    have hff : ContDiff ℝ ((a + (j - a) : ℕ) : ℕ∞) f := by
      rw [he]
      exact hf.of_le (by exact_mod_cast hjJ)
    rw [weakPositive_thetaPartial_eq_partial a (j - a) f hff]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, he] using
      Finset.single_le_sum (f := fun α => E ^ (α 0 + α 1) * ‖partialDerivative α f x‖)
        (fun α _ => mul_nonneg (pow_nonneg hE _) (norm_nonneg _)) hmem
  calc
    _ ≤ E ^ j * ((2 : ℝ) ^ j * ∑ a ∈ Finset.range (j + 1), ‖thetaPartial a (j - a) f x‖) :=
      mul_le_mul_of_nonneg_left (CycleWords.Assembly.norm_iteratedFDeriv_le_sum_thetaPartial
        (hf.of_le (by exact_mod_cast hjJ)) x) (pow_nonneg hE _)
    _ = (2 : ℝ) ^ j * ∑ a ∈ Finset.range (j + 1), E ^ j * ‖thetaPartial a (j - a) f x‖ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (2 : ℝ) ^ j * ((j + 1) * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_le_sum fun a ha' => ha a ha').trans_eq (by simp)
    _ ≤ (2 : ℝ) ^ J * ((J + 1) * B) := mul_le_mul
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjJ)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hjJ 1) hB)
      (mul_nonneg (by positivity) hB) (by positivity)
    _ = _ := by rw [mul_assoc]

/-- The entire positive full jet density has a cost independent of the component family. -/
theorem weakPositive_full_jet_density_le {J : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (f : Vec 2 → V) (hf : ContDiff ℝ (J : ℕ∞) f) (x : Vec 2) :
    (∑ j ∈ Finset.range (J + 1), if j = 0 then 0 else E ^ j * ‖iteratedFDeriv ℝ j f x‖) ≤
      ((2 : ℝ) ^ J * (J + 1) ^ 2) *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
  have hb := Finset.sum_nonneg (s := multiIndicesBetween 1 J)
    (fun α _ => mul_nonneg (pow_nonneg hE (α 0 + α 1)) (norm_nonneg (partialDerivative α f x)))
  calc
    _ ≤ ∑ _j ∈ Finset.range (J + 1), (2 : ℝ) ^ J * (J + 1) *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hzero
      · exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hb
      · exact weakPositive_scaled_full_jet_le hE (by omega)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) f hf x
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

section Weighted
variable {ι : Type*} [Fintype ι]

/-- The inverse-square-root mass normalization of a real component vector. -/
def weakPositiveWeightedVector (π z : ι → ℝ) : PiLp 2 (fun _ : ι => ℝ) :=
  WithLp.toLp 2 (fun v => (Real.sqrt (π v))⁻¹ * z v)

/-- The normalized component norm is exactly the inverse-mass Euclidean norm. -/
theorem weakPositiveWeightedVector_norm (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (z : ι → ℝ) :
    ‖weakPositiveWeightedVector π z‖ = Real.sqrt (∑ v, (π v)⁻¹ * z v ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  change ‖(Real.sqrt (π v))⁻¹ * z v‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]
  exact Construction.Preservation.FullLift.inverse_sqrt_mass_square (hπ v).le (z v)

/-- Weighted Euclidean triangle inequality, with no component-count factor. -/
theorem weakPositive_weighted_minkowski {κ : Type*} (s : Finset κ)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (z : κ → ι → ℝ) :
    Real.sqrt (∑ v, (π v)⁻¹ * (∑ j ∈ s, z j v) ^ 2) ≤
      ∑ j ∈ s, Real.sqrt (∑ v, (π v)⁻¹ * z j v ^ 2) := by
  rw [← weakPositiveWeightedVector_norm π hπ]
  have he : weakPositiveWeightedVector π (fun v => ∑ j ∈ s, z j v) =
      ∑ j ∈ s, weakPositiveWeightedVector π (z j) := by
    apply PiLp.ext
    intro v
    change (Real.sqrt (π v))⁻¹ * (∑ j ∈ s, z j v) = _
    rw [Finset.mul_sum]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  rw [he]
  exact (norm_sum_le _ _).trans_eq (by simp only [weakPositiveWeightedVector_norm π hπ])

/-- Positive full input densities reduce to the exact normalized partial derivatives. -/
theorem weakPositive_weighted_input_density_le {J : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (f : Vec 2 → ι → ℝ)
    (hf : ContDiff ℝ (J : ℕ∞) f) (x : Vec 2) :
    Real.sqrt (∑ v, (π v)⁻¹ *
      (∑ j ∈ Finset.range (J + 1), if j = 0 then 0 else
        E ^ j * ‖iteratedFDeriv ℝ j (fun X => f X v) x‖) ^ 2) ≤
      ((2 : ℝ) ^ J * (J + 1) ^ 2) *
        ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) *
          ‖partialDerivative α (fun X => weakPositiveWeightedVector π (f X)) x‖ := by
  let A : ℝ := (2 : ℝ) ^ J * (J + 1) ^ 2
  have hA : 0 ≤ A := mul_nonneg (by positivity) (sq_nonneg _)
  let B := fun v => ∑ α ∈ multiIndicesBetween 1 J,
    E ^ (α 0 + α 1) * ‖partialDerivative α (fun X => f X v) x‖
  have hb := Real.sqrt_le_sqrt (Finset.sum_le_sum (s := Finset.univ) fun v _ =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (pow_nonneg hE _) (norm_nonneg _))
        (weakPositive_full_jet_density_le hE (fun X => f X v)
          ((contDiff_apply ℝ ℝ v).comp hf) x) 2) (inv_nonneg.mpr (hπ v).le))
  have he : (∑ v, (π v)⁻¹ * (A * B v) ^ 2) =
      A ^ 2 * ∑ v, (π v)⁻¹ * B v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  change _ ≤ Real.sqrt (∑ v, (π v)⁻¹ * (A * B v) ^ 2) at hb
  rw [he, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_nonneg hA] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply (weakPositive_weighted_minkowski (multiIndicesBetween 1 J) π hπ
    (fun α v => E ^ (α 0 + α 1) * ‖partialDerivative α (fun X => f X v) x‖)).trans
  apply Finset.sum_le_sum
  intro α hα
  have horder : α 0 + α 1 ≤ J := (Finset.mem_filter.mp hα).2.2
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let L : (ι → ℝ) →L[ℝ] PiLp 2 (fun _ : ι => ℝ) := T.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun v => (Real.sqrt (π v))⁻¹ • ContinuousLinearMap.proj v)
  have hL (z : ι → ℝ) : L z = weakPositiveWeightedVector π z := rfl
  have hp : partialDerivative α (fun X => weakPositiveWeightedVector π (f X)) x =
      weakPositiveWeightedVector π (fun v => partialDerivative α (fun X => f X v) x) := by
    have h := congrFun (Readout.partialDerivative_comp α horder L f hf) x
    simp only [hL] at h
    rw [h]
    apply PiLp.ext
    intro v
    change (Real.sqrt (π v))⁻¹ * (partialDerivative α f x) v = _
    have hh := congrFun (Readout.partialDerivative_comp α horder
      (ContinuousLinearMap.proj v) f hf) x
    change partialDerivative α (fun X => f X v) x = (partialDerivative α f x) v at hh
    change (Real.sqrt (π v))⁻¹ * (partialDerivative α f x) v =
      (Real.sqrt (π v))⁻¹ * partialDerivative α (fun X => f X v) x
    rw [hh]
  rw [hp, weakPositiveWeightedVector_norm π hπ]
  have hsq : (∑ v, (π v)⁻¹ * (E ^ (α 0 + α 1) * ‖partialDerivative α (fun X => f X v) x‖) ^ 2) =
      (E ^ (α 0 + α 1)) ^ 2 * ∑ v, (π v)⁻¹ *
        (partialDerivative α (fun X => f X v) x) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg hE _)]

/-- A fixed matrix bounds normalized spatial words with its Schur cost, without label loss. -/
theorem weakPositive_weighted_word_bound {r : ℕ} (β : DerivativeWord2 r)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (f : Vec 2 → ι → ℝ)
    (hf : ContDiff ℝ (r : ℕ∞) f) (x : Vec 2) {e C Cpath : ℝ}
    (he : 0 ≤ e) (hC : 0 ≤ C) (hpath : 0 ≤ Cpath)
    (M : ι → ι → ℝ) (hM : CycleComparison.Lift.HasRealSchurBudget
      (CycleComparison.Lift.massConjugatedMatrix π M) Cpath) (z : ι → ℝ)
    (hb : ∀ v, e ^ r * ‖orderedDerivative β (fun X => f X v) x‖ ≤
      C * ∑ u, M v u * z u) :
    e ^ r * ‖orderedDerivative β (fun X => weakPositiveWeightedVector π (f X)) x‖ ≤
      C * Cpath * Real.sqrt (∑ u, (π u)⁻¹ * z u ^ 2) := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let L : (ι → ℝ) →L[ℝ] PiLp 2 (fun _ : ι => ℝ) := T.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun v => (Real.sqrt (π v))⁻¹ • ContinuousLinearMap.proj v)
  have hL (z : ι → ℝ) : L z = weakPositiveWeightedVector π z := rfl
  have hp : orderedDerivative β (fun X => weakPositiveWeightedVector π (f X)) x =
      weakPositiveWeightedVector π (fun v => orderedDerivative β (fun X => f X v) x) := by
    have h := congrFun (orderedDerivative_clm_comp L β hf) x
    simp only [hL] at h
    rw [h]
    apply PiLp.ext
    intro v
    have hh := congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj v) β hf) x
    change orderedDerivative β (fun X => f X v) x = (orderedDerivative β f x) v at hh
    change (Real.sqrt (π v))⁻¹ * (orderedDerivative β f x) v =
      (Real.sqrt (π v))⁻¹ * orderedDerivative β (fun X => f X v) x
    rw [hh]
  rw [hp, weakPositiveWeightedVector_norm π hπ]
  have heq : e ^ r * Real.sqrt (∑ v, (π v)⁻¹ *
      (orderedDerivative β (fun X => f X v) x) ^ 2) =
      Real.sqrt (∑ v, (π v)⁻¹ *
        (e ^ r * ‖orderedDerivative β (fun X => f X v) x‖) ^ 2) := by
    have hs : (∑ v, (π v)⁻¹ * (e ^ r * ‖orderedDerivative β (fun X => f X v) x‖) ^ 2) =
        (e ^ r) ^ 2 * ∑ v, (π v)⁻¹ * (orderedDerivative β (fun X => f X v) x) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (pow_nonneg he _)]
  rw [heq]
  exact positive_component_norm_restoration π hπ M Cpath C hpath hC hM z _
    (fun _ => mul_nonneg (pow_nonneg he _) (norm_nonneg _)) hb

end Weighted

end AVRegularity.Finite.WeakLift
end
