-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.LiftCarrierInverse
public import AVRegularity.Construction.Uniqueness.CellFieldUnique
public import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.SettingAmbientSourceTestPeriodicOfCoefficients
public import AVRegularity.EntryWeakAssembly.WindowFieldExtension
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
public import AVRegularity.EntryWeak.IndependentScaledDifferenceSegmentDerivativeJets
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
namespace AVRegularity.WeakEntryProofs

/-! Structural assembly of the actual weak successor from its periodic transferred mean arrays. -/

section
open Homogenization AVRegularity.Sobolev
open scoped Classical

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def weakSuccessorStageOfPeriodicTransfer (G : GenStage D ScalarH Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (Mn : WeakMenu) (Din H : ℕ) (hDin : 1 ≤ Din) (hDm : Mn.N + Din ≤ Dm)
    (hpath : ∀ h, StagePath G h → h ≤ H) (rW : ℝ) (hrW : 0 < rW)
    (heps : ∀ i, 0 < D.eps i) (hi : 1 ≤ G.level - 1) (hj : j₀ ≤ G.level - 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G.level - 1))
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hperiodic : ∀ (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p)
      (s : WeakSource G), s.Valid Mn.N Mn.R Din → ∀ d I t X,
      AVenhance.IsZ2Periodic (weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c s d I t X)) :
    GenStage D ScalarH Dm b j₀ where
  level := G.level - 1
  comps := weakExtComps G.level Mn.N Mn.R G.comps
  fam :=
    { Γ := weakSourceEdge G _ G.level Mn.N Mn.R Din
      fintypeΓ := weakSourceEdgeFintype G _ G.level Mn.N Mn.R Din H hpath
      identity := weakSourceCoefficientIdentity G P ht _ G.level Mn.N Mn.R Din hDin hDm
        rW Mn.η0 heps hrW
      piece := fun p => weakNaturalPiece D Mn.Mtop (G.level - 1) p.1
      flux := fun p c v u γ d I t X z => if 2 ≤ d then
        weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c γ.1 d I t X z else 0
      flux_periodic := by
        intro p c v u γ d I t X
        by_cases hd : 2 ≤ d
        · simpa only [ite_eq_left hd] using hperiodic p c γ.1 γ.2.1 d I t X
        · intro n z
          simp only [ite_eq_right hd]
      flux_zero := by
        intro p c v u γ d I hd
        funext t X z
        by_cases htwo : 2 ≤ d
        · rw [ite_eq_left htwo]
          apply weakSourceTransferredFlux_above_degree
          change ¬ (2 ≤ d ∧ d ≤ γ.1.degree) at hd
          omega
        · rw [ite_eq_right htwo]
      weight := fun p => ocCutoff D.α D.q D.Λ (G.level - 1) p.1
      weight_nonneg := fun _ _ => Real.smoothTransition.nonneg _
      weight_zero := fun p t ht => ocCutoff_zero_off_output D.α D.q D.Λ _ hτ p.1 t ht
      locally_finite := weak_output_locally_finite D.α D.q D.Λ _ hτ
      weight_sum := fun t _ => ocCutoff_finsum_one D.α D.q D.Λ _ hτ t }
  prov := fun v u γ => .seed (weakSourceEdgeIndex G _ G.level Mn.N Mn.R Din H hpath v u γ)
    (γ.1.weakTag P G.level rW Mn.η0)
  actual := fun p => ⟨nativeChain (G.level - 1) p.1,
    nativeChain_isCarrier D b j₀ _ p.1 2 hi hj p.2 0⟩
  exports := G.exports
end

/-! Natural charts and exact weak tags of the explicitly assembled successor. -/

section
open Homogenization AVRegularity.Sobolev

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

variable (G : GenStage D ScalarH Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (Mn : WeakMenu) (Din H : ℕ) (hDin : 1 ≤ Din) (hDm : Mn.N + Din ≤ Dm)
    (hpath : ∀ h, StagePath G h → h ≤ H) (rW : ℝ) (hrW : 0 < rW)
    (heps : ∀ i, 0 < D.eps i) (hi : 1 ≤ G.level - 1) (hj : j₀ ≤ G.level - 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G.level - 1))
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hperiodic : ∀ (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p)
      (s : WeakSource G), s.Valid Mn.N Mn.R Din → ∀ d I t X,
      AVenhance.IsZ2Periodic (weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c s d I t X))

local notation "Gsucc" => weakSuccessorStageOfPeriodicTransfer G P ht Mn Din H hDin hDm
  hpath rW hrW heps hi hj hτ Cc Cc0 hperiodic

theorem weakSuccessorStage_isNatural : (Gsucc).IsNatural Mn.Mtop := by
  refine ⟨fun p => weakNaturalPiece_isNatural D Mn.Mtop _ p.1,
    fun _ _ => rfl, fun _ => rfl, ?_⟩
  intro v u γ γ' hγ
  have he : weakSourceEdgeIndex G _ G.level Mn.N Mn.R Din H hpath v u γ =
      weakSourceEdgeIndex G _ G.level Mn.N Mn.R Din H hpath v u γ' :=
    (Prov.seed.inj hγ).1
  exact eq_of_heq (weakSourceEdgeIndex_injective G _ G.level Mn.N Mn.R Din H hpath
    v u γ v u γ' he).2.2

theorem weakSuccessorStage_hasTags : (Gsucc).HasTags P := by
  intro v u γ
  refine ⟨weakSourceRecord_matches G P ht G.level rW Mn.η0 heps hrW γ.1 _, ?_⟩
  change γ.1.degree = (γ.1.weakTag P G.level rW Mn.η0).maxOrder
  cases γ.1 <;> rfl
end

/-! The structural successor is a weak passage once its actual lift witnesses are supplied. -/

section
open Homogenization AVRegularity.Sobolev

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

variable (G : GenStage D ScalarH Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (Mn : WeakMenu) (Din H : ℕ) (hDin : 1 ≤ Din) (hDm : Mn.N + Din ≤ Dm)
    (hpath : ∀ h, StagePath G h → h ≤ H) (rW : ℝ) (hrW : 0 < rW)
    (heps : ∀ i, 0 < D.eps i) (hi : 1 ≤ G.level - 1) (hj : j₀ ≤ G.level - 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G.level - 1))
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hperiodic : ∀ (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p)
      (s : WeakSource G), s.Valid Mn.N Mn.R Din → ∀ d I t X,
      AVenhance.IsZ2Periodic (weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c s d I t X))

local notation "Gsucc" => weakSuccessorStageOfPeriodicTransfer G P ht Mn Din H hDin hDm
  hpath rW hrW heps hi hj hτ Cc Cc0 hperiodic

theorem weakSuccessorStage_isWeakPassage
    (hlevel : D.term < G.level) (horder : G.maxOrderBound Din)
    (hCc : ∀ s : WeakSource G, s.IsLiftFamily Mn.sX Mn.sZ Mn.N (D.eps (G.level - 1)) (Cc s))
    (hCc0 : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ G.level k A →
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A
        (D.eps (G.level - 1)) (fun _ _ _ => [])) Mn.sX Mn.sZ
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        Mn.N 0 (Cc0 k A)) :
    IsWeakPassage D P Mn rW Din G (Gsucc) := by
  refine ⟨hlevel, rfl, horder, rfl, ?_, (fun _ _ => Equiv.refl _),
    weakSourceEdgeIndex G _ G.level Mn.N Mn.R Din H hpath, Cc, Cc0, hCc, hCc0, ?_, ?_⟩
  · exact weakSuccessorStage_isNatural G P ht Mn Din H hDin hDm hpath rW hrW heps
      hi hj hτ Cc Cc0 hperiodic
  · exact weakSourceEdgeIndex_injective G _ G.level Mn.N Mn.R Din H hpath
  · intro v u γ
    refine ⟨rfl, rfl, ?_⟩
    intro p c d I t X z hd
    change (if 2 ≤ d then weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c γ.1 d I t X z else 0) = _
    rw [ite_eq_left hd]
    rfl
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

/-! Finite-window higher energy from scalar and flux budgets with arbitrary bounded transport. -/

open AVRegularity.EntryWeakProofs

theorem molecularFinite_window_flux_energy_bound {a b : ℝ} (hab : a ≤ b) (N K : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (P : MolecularData) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (y dy : ℝ → CellGalerkinSpace (E := ℂ) N) (S : ℝ → TorusHk K ℂ)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (htime : StrongTimeRegularity a b (fun t => cellGalerkinValue N (y t))
      (fun t => cellGalerkinValue N (dy t)))
    (heq : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy t)) (cellGalerkinValue N z) =
        dataGeneratorForm P t (y t).val z.val +
          inner ℝ ((S t).val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ k : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
              2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)))
            (cellDerivativeCLM k z.val)) :
    ∀ t ∈ Icc a b,
      factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y t))).val ≤
      (factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val +
        ∫ s in a..b, factorialNormSq ρ (S s).val + 4 * factorialNormSq ρ (F s).val) *
        Real.exp ((1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (t - a)) := by
  let f := fun t => factorialNormSq ρ (S t).val + 4 * factorialNormSq ρ (F t).val
  have hf : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      ((factorialNormSq_integrable ρ K (torusJet_memLp K hS)).add
        ((factorialNormSq_integrable ρ K (torusJet_memLp K hF)).const_mul 4))
  have ht := htime.map (dataWeightedFourierCLM N K ρ)
  have hp : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (dataWeightedFourierCLM N K ρ (cellGalerkinValue N (y t)))
        (dataWeightedFourierCLM N K ρ (cellGalerkinValue N (dy t))) ≤
        (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) *
          ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N (y t))‖ ^ 2 + f t := by
    filter_upwards [heq] with t he
    have hh := molecularFinite_flux_gradient_production N K ρ hρ P t Cv hCv
      (hv t) (hp t) (hb t) (y t) (dy t) (S t) (F t) he
    have hn : 0 ≤ gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1)
        (dataFourierCoordinatesCLM N (cellGalerkinValue N (y t)))).val / 2 := by
      rw [← coupledPlainGradientHk_factorialNormSq]
      exact div_nonneg (factorialNormSq_nonneg _ _) (by norm_num)
    simpa only [f, add_assoc] using (le_add_of_nonneg_right hn).trans hh
  have hg := ht.norm_sq_le_gronwall hab
    (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ^ 2) (by positivity) f hf
    (Filter.Eventually.of_forall (fun t => add_nonneg (factorialNormSq_nonneg _ _)
      (mul_nonneg (by norm_num) (factorialNormSq_nonneg _ _)))) hp
  simpa only [dataWeightedFourierCLM_apply, factorialWeightedJet_normSq, f] using hg

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Genuine inverse uniqueness identifies a positive lift step on its open slow carrier. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem localLift_positive_coefficients_unique_of_window_data
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (N H sX sZ sX' sZ' : ℕ)
    (hW : ∀ X ∈ Ω, ∃ lo hi Mv,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v a b lo hi Mv)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc)
    (hd : IsLiftSequenceOn Ω Q sX' sZ' a b N H Dc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t ∈ Set.Icc a b,
        ∀ X ∈ Ω, ∀ z v u, Cc p q m α t X z v u = Dc p q m α t X z v u)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) (v u : ι) :
    Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  classical
  by_cases hmn : n < m
  · rw [hc.2.2.2.1 hh hhh n m hmn, hd.2.2.2.1 hh hhh n m hmn]
  · apply symmetric_lift_coefficient_eq_of_operator_eq n m (by omega)
      (Cc hh n) (Dc hh n) (hc.2.2.2.2.1 hh hhh n m) (hd.2.2.2.2.1 hh hhh n m)
      t X z v u
    intro a₀ ha₀
    have hC := hc.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X hX
    have hD := hd.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X hX
    have hsource (s : ℝ) (hs : s ∈ Set.Icc a b) :
        (fun y => liftCellSource Q Cc (fun _ => a₀) hh n s X y) =
          fun y => liftCellSource Q Dc (fun _ => a₀) hh n s X y := by
      funext y
      exact liftCellSource_slow_open_congr_predecessors hΩ Q Cc Dc (fun _ => a₀)
        hh n hn s (fun p q hpq l hl β Y hY y v u => he p q hpq l hl β s hs Y hY y v u)
        X hX y
    obtain ⟨lo, hi, Mv, hWX⟩ := hW X hX
    have hC0 := cellFieldInverse_order_mono _ _ sZ 0 (Nat.zero_le _) a b 0 _ _ hC
    have hD0 := cellFieldInverse_order_mono _ _ sZ' 0 (Nat.zero_le _) a b 0 _ _ hD
    have heq := Uniqueness.cellField_unique_window hab hWX
      (fun s hs y => congrFun (hsource s hs) y) hC0 hD0 t ht z
    exact congrFun heq v
end

/-! The genuine zero-start inverse on an elliptic window extends linearly to the source space. -/

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

/-- Sources for which the classical finite-window inverse exists. -/
def windowSolvableForcing (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b) :
    Submodule ℝ (ℝ → Vec 2 → ℝ) where
  carrier := {g | ∃ c : ℝ → Vec 2 → ℝ, IsCellFieldInverse G v r a b 0 g c}
  zero_mem' := ⟨0, cellFieldInverse_zero_field G v r a b hab⟩
  add_mem' := by
    rintro g f ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨fun t z => c t z + d t z, cellFieldInverse_add_zero G v r hr a b hab g f c d hc hd⟩
  smul_mem' := by
    rintro k g ⟨c, hc⟩
    refine ⟨fun t z => k • c t z, ?_⟩
    simpa only [Pi.zero_apply, smul_zero] using! cellFieldInverse_const_smul G v r a b 0 g c hc k

def selectedWindowResponse (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (g : windowSolvableForcing G v r hr a b hab) : ℝ → Vec 2 → ℝ := g.2.choose

theorem selectedWindowResponse_isInverse (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (g : windowSolvableForcing G v r hr a b hab) :
    IsCellFieldInverse G v r a b 0 g.1 (selectedWindowResponse G v r hr a b hab g) :=
  g.2.choose_spec

def selectedWindowResponseLinear (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) :
    windowSolvableForcing G v r hr a b hab →ₗ[ℝ]
      ({t : ℝ // t ∈ Set.Icc a b} → Vec 2 → ℝ) where
  toFun := fun g t => selectedWindowResponse G v r hr a b hab g t.1
  map_add' := by
    intro g f
    funext t z
    have hc := selectedWindowResponse_isInverse G v r hr a b hab (g + f)
    have hs := cellFieldInverse_add_zero G v r hr a b hab g.1 f.1
      (selectedWindowResponse G v r hr a b hab g) (selectedWindowResponse G v r hr a b hab f)
      (selectedWindowResponse_isInverse G v r hr a b hab g)
      (selectedWindowResponse_isInverse G v r hr a b hab f)
    exact Uniqueness.cellField_unique_window hab hW (fun _ _ _ => rfl) hc hs t.1 t.2 z
  map_smul' := by
    intro k g
    funext t z
    have hc := selectedWindowResponse_isInverse G v r hr a b hab (k • g)
    have hs : IsCellFieldInverse G v r a b 0 (k • g).1
        (fun t z => k • selectedWindowResponse G v r hr a b hab g t z) := by
      simpa only [Pi.zero_apply, smul_zero] using! cellFieldInverse_const_smul G v r a b 0 g.1
        (selectedWindowResponse G v r hr a b hab g)
        (selectedWindowResponse_isInverse G v r hr a b hab g) k
    exact Uniqueness.cellField_unique_window hab hW (fun _ _ _ => rfl) hc hs t.1 t.2 z

def windowResponseLinear (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) :
    (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ) :=
  (windowFieldExtension a b).comp (selectedWindowResponseLinear G v r hr a b hab hW).exists_extend.choose

theorem windowResponseLinear_isInverse (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv)
    (g : windowSolvableForcing G v r hr a b hab) :
    IsCellFieldInverse G v r a b 0 g.1 (windowResponseLinear G v r hr a b hab hW g.1) := by
  apply cellFieldInverse_field_congr_on G v r a b hab 0 g.1
    (selectedWindowResponse G v r hr a b hab g) _
    (selectedWindowResponse_isInverse G v r hr a b hab g)
  intro t ht
  symm
  have he := (selectedWindowResponseLinear G v r hr a b hab hW).exists_extend.choose_spec
  have hev := congrArg (fun L => L g) he
  change windowFieldExtension a b
    ((selectedWindowResponseLinear G v r hr a b hab hW).exists_extend.choose g.1) t = _
  rw [windowFieldExtension_apply_mem a b _ t ht]
  exact congrFun hev ⟨t, ht⟩
end

/-! The genuine cell response is periodic at every time, including its zero extension. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs

theorem windowResponseLinear_zero_off_window (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) (g : ℝ → Vec 2 → ℝ) (t : ℝ)
    (ht : t ∉ Set.Icc a b) : windowResponseLinear G v r hr a b hab hW g t = 0 := by
  exact windowFieldExtension_apply_not_mem a b _ t ht

theorem windowResponseLinear_periodic (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) (g : windowSolvableForcing G v r hr a b hab) (t : ℝ) :
    AVenhance.IsZ2Periodic (windowResponseLinear G v r hr a b hab hW g.1 t) := by
  by_cases ht : t ∈ Set.Icc a b
  · have hc := windowResponseLinear_isInverse G v r hr a b hab hW g
    intro n x
    exact Complex.ofReal_injective
      ((((hc.2 (ContinuousLinearMap.id ℝ ℝ)).1.2.2.1 t ht).2) n x)
  · rw [windowResponseLinear_zero_off_window G v r hr a b hab hW g.1 t ht]
    intro n x
    rfl

theorem windowResponseLinear_mean_zero (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) (g : windowSolvableForcing G v r hr a b hab) (t : ℝ) :
    (∫ x in AVenhance.unitCube, windowResponseLinear G v r hr a b hab hW g.1 t x) = 0 := by
  by_cases ht : t ∈ Set.Icc a b
  · have hc := windowResponseLinear_isInverse G v r hr a b hab hW g
    have hm := (hc.2 (ContinuousLinearMap.id ℝ ℝ)).2.1 t ht
    change (∫ x in AVenhance.unitCube,
      (windowResponseLinear G v r hr a b hab hW g.1 t x : ℂ)) = 0 at hm
    rw [integral_complex_ofReal] at hm
    exact Complex.ofReal_injective hm
  · rw [windowResponseLinear_zero_off_window G v r hr a b hab hW g.1 t ht]
    simp

theorem windowResponseLinear_initial_zero (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b)
    {lo hi Mv : ℝ} (hW : Uniqueness.WindowData G v a b lo hi Mv) (g : windowSolvableForcing G v r hr a b hab) :
    windowResponseLinear G v r hr a b hab hW g.1 a = 0 := by
  have hc := windowResponseLinear_isInverse G v r hr a b hab hW g
  have hi := (hc.2 (ContinuousLinearMap.id ℝ ℝ)).2.2.1
  have he : windowResponseLinear G v r hr a b hab hW g.1 a =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    filter_upwards [hi] with x hx
    exact Complex.ofReal_injective hx
  apply periodicCell_ae_eq_pointwise _ _ (hc.1 a ⟨le_rfl, hab⟩).continuous continuous_const
    (windowResponseLinear_periodic G v r hr a b hab hW g a) _ he
  intro n x
  rfl
end

/-! Literal higher source carrier bounds pay the complete finite-window forcing energy. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational

def higherSourceWindowBudget (a b : ℝ) (K : ℕ) (Ns Nf : ℝ) : ℝ :=
  (b - a) * (factorialWeightMax 1 K * (Ns ^ 2 + 4 * Nf ^ 2))

theorem higherSourceWindowBudget_nonneg {a b : ℝ} (hab : a ≤ b) (K : ℕ) (Ns Nf : ℝ) :
    0 ≤ higherSourceWindowBudget a b K Ns Nf :=
  mul_nonneg (sub_nonneg.mpr hab) (mul_nonneg (factorialWeightMax_nonneg_local K)
    (add_nonneg (sq_nonneg Ns) (mul_nonneg (by norm_num) (sq_nonneg Nf))))

theorem higher_source_window_budget {a b : ℝ} (hab : a ≤ b)
    {K : ℕ} {src : ℝ → Vec 2 → ℂ} {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData (Icc a b) K src flux) :
    (∫ t in a..b, factorialNormSq 1 (Q.S t).val + 4 * factorialNormSq 1 (Q.F t).val) ≤
      higherSourceWindowBudget a b K Q.Ns Q.Nf := by
  have hW := factorialWeightMax_nonneg_local K
  have hf : IntervalIntegrable (fun t =>
      factorialNormSq 1 (Q.S t).val + 4 * factorialNormSq 1 (Q.F t).val) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      ((factorialNormSq_integrable 1 K (torusJet_memLp K Q.scalar_carrier_memLp)).add
        ((factorialNormSq_integrable 1 K (torusJet_memLp K Q.flux_carrier_memLp)).const_mul 4))
  have hp (t : ℝ) (ht : t ∈ Icc a b) :
      factorialNormSq 1 (Q.S t).val + 4 * factorialNormSq 1 (Q.F t).val ≤
        factorialWeightMax 1 K * (Q.Ns ^ 2 + 4 * Q.Nf ^ 2) := by
    have hs := (factorialNormSq_upper 1 (Q.S t).val).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (Q.scalar_bound t ht) 2) hW)
    have hg := (factorialNormSq_upper 1 (Q.F t).val).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (Q.flux_bound t ht) 2) hW)
    calc
      _ ≤ factorialWeightMax 1 K * Q.Ns ^ 2 + 4 * (factorialWeightMax 1 K * Q.Nf ^ 2) :=
        add_le_add hs (mul_le_mul_of_nonneg_left hg (by norm_num))
      _ = _ := by ring
  have he := intervalIntegral.integral_mono_on hab hf
    (continuous_const.intervalIntegrable a b) hp
  simpa only [intervalIntegral.integral_const, smul_eq_mul, higherSourceWindowBudget] using he
end

/-! Local lift coefficients are uniquely determined by the genuine cell recurrence. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem localLift_zero_degree_coefficients_unique
    (Ω : Set (Vec 2)) (Q : LiftOperatorData ι h D)
    (a b : ℝ) (N H sX sZ sX' sZ' : ℕ) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc)
    (hd : IsLiftSequenceOn Ω Q sX' sZ' a b N H Dc)
    (hh : ℕ) (hhh : hh ≤ H) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc hh 0 m α t X z v u = Dc hh 0 m α t X z v u := by
  classical
  by_cases hh0 : hh = 0
  · subst hh
    cases m with
    | zero =>
      apply ContinuousLinearMap.ext
      intro ξ
      have hC := hc.1 (fun _ => Pi.single u ξ) contDiff_const t ht X z
      have hD := hd.1 (fun _ => Pi.single u ξ) contDiff_const t ht X z
      have he := congrFun (hC.trans hD.symm) v
      rw [liftApply_constant_single 0 (Cc 0 0) α t X z v u ξ,
        liftApply_constant_single 0 (Dc 0 0) α t X z v u ξ] at he
      exact he
    | succ m =>
      rw [hc.2.2.2.1 0 (Nat.zero_le _) 0 (m + 1) (by omega),
        hd.2.2.2.1 0 (Nat.zero_le _) 0 (m + 1) (by omega)]
  · rw [hc.2.1 hh (by omega) hhh, hd.2.1 hh (by omega) hhh]
end

/-! Local lift coefficients are uniquely determined by the genuine cell recurrence. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem localLift_coefficients_unique_of_window_data
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (N H sX sZ sX' sZ' : ℕ)
    (hW : ∀ X ∈ Ω, ∃ lo hi Mv,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v a b lo hi Mv)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc)
    (hd : IsLiftSequenceOn Ω Q sX' sZ' a b N H Dc) :
    ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b →
      ∀ X ∈ Ω, ∀ z v u, Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | h hh ih =>
    intro hhh n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      by_cases hnN : N < n
      · intro m α t _ X _ z v u
        rw [hc.2.2.1 hh hhh n hnN, hd.2.2.1 hh hhh n hnN]
      · by_cases hn0 : n = 0
        · subst n
          intro m α t ht X _ z v u
          exact localLift_zero_degree_coefficients_unique Ω Q a b N H sX sZ sX' sZ'
            Cc Dc hc hd hh hhh m α t ht X z v u
        · apply localLift_positive_coefficients_unique_of_window_data Ω hΩ Q a b hab
            N H sX sZ sX' sZ' hW Cc Dc hc hd hh n hhh (by omega) (by omega)
          intro p q hpq l _hl
          rcases hpq with hp | ⟨rfl, hq⟩
          · exact ih p hp (by omega) q l
          · exact ihn q hq l
end

/-! The weak isotropic pair has a fixed admissibility bound and uniform regularizer constants. -/

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift

private theorem isoPairedKernel_span (r : ℝ) (n : ℕ+) (t : ℝ) :
    (isoPairedKernel r n).span t = (Real.sqrt 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [KernelSpec.span, isoPairedKernel, basisVec]

private theorem isoPairedKernel_inverse (r : ℝ) (n : ℕ+) (t : ℝ) :
    (Matrix.toLin' ((isoPairedKernel r n).span t)⁻¹).toContinuousLinearMap =
      Real.sqrt 2 • ContinuousLinearMap.id ℝ (Vec 2) := by
  let : Invertible ((Real.sqrt 2)⁻¹) :=
    invertibleOfNonzero (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne')
  rw [isoPairedKernel_span, Matrix.inv_smul (A := (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((Real.sqrt 2)⁻¹) (by simp), inv_one, invOf_eq_inv, inv_inv]
  ext x a
  simp

/-- Bound two includes both isotropic axes and the inverse spanning matrix. -/
theorem isoPairedKernel_isAdmissible (r : ℝ) (n : ℕ+) (L : ℕ)
    (hL : L + 1 ≤ 2 * (n : ℕ)) : (isoPairedKernel r n).IsAdmissible 2 L := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  refine ⟨measurable_const, measurable_const, fun t => ?_, hL⟩
  have hnorm : ‖(Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), ContinuousLinearMap.norm_id, mul_one]
    exact (inv_le_one_of_one_le₀ hs1).trans (by norm_num)
  refine ⟨hnorm, hnorm, ?_, ?_⟩
  · rw [isoPairedKernel_span, Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hs.ne'))
  · rw [isoPairedKernel_inverse, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
      ContinuousLinearMap.norm_id, mul_one]
    exact hs2

/-- The same derivative constants work at every positive width and every observation window. -/
theorem exists_isoPairedKernel_regularizer_constants (φ₀ : Vec 2 → ℝ)
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφ₀ : Integrable φ₀) (n : ℕ+) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm,
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b c r ((isoPairedKernel r n).op φ₀ hφ₀) := by
  obtain ⟨c, hcn, hr⟩ := exists_kernelSpec_vector_regularizer_constants φ₀ hc hd n
  refine ⟨c, hcn, fun r hr₀ ρ a b k Dm => ?_⟩
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let V : Vec 2 ≃L[ℝ] Vec 2 := scaledVectorEquiv (ContinuousLinearEquiv.refl ℝ (Vec 2))
    (Real.sqrt 2)⁻¹ (inv_ne_zero hs.ne')
  have hV : V.toContinuousLinearMap = (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2) := by
    ext x a
    rfl
  have hVi : V.symm.toContinuousLinearMap = Real.sqrt 2 • ContinuousLinearMap.id ℝ (Vec 2) := by
    ext x a
    change ((Real.sqrt 2)⁻¹)⁻¹ * x a = Real.sqrt 2 * x a
    rw [inv_inv]
  have hbound : ‖V.symm.toContinuousLinearMap‖ ≤ 2 := by
    rw [hVi, norm_smul, Real.norm_eq_abs, abs_of_pos hs, ContinuousLinearMap.norm_id, mul_one]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  exact hr ℝ (isoPairedKernel r n) rfl hr₀ measurable_const measurable_const
    (fun _ => V) (fun _ => V) (fun _ => V) (fun _ => hV.symm) (fun _ => hV.symm)
    (fun _ => rfl) (fun _ => rfl) (fun _ => hbound) ρ a b k Dm
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

/-! Finite-window higher energy for the actual molecular Galerkin sequence with divergence forcing. -/

open AVRegularity.EntryWeakProofs

theorem molecular_actual_window_flux_energy_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src flux initial)
    (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
 :
    ∀ N t, t ∈ Icc a b →
      factorialNormSq ρ (dataFourierHighCLM N K
        (cellGalerkinValue N (extendCurve hab (D.curve N) t))).val ≤
      (factorialNormSq ρ u₀.val + ∫ s in a..b,
        factorialNormSq ρ (S s).val + 4 * factorialNormSq ρ (F s).val) *
        Real.exp ((1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (t - a)) := by
  intro N t ht
  let y := extendCurve hab (D.curve N)
  let dy := linearRhs (fun r => cellGalerkinOperator N (dataGeneratorB P r))
    (fun r => cellGalerkinForcing N (cellRawSourceFunctional 0 src flux r)) y
  have he : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
        dataGeneratorForm P r (y r).val z.val +
          inner ℝ ((S r).val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ j : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
              2 (volume.restrict AVenhance.unitCube)) ((F r).val (valueIndex2 K)))
            (cellDerivativeCLM j z.val) := by
    have h := (D.variational N).equation
    rw [uIcc_of_le hab] at h
    filter_upwards [h, hs, hf] with r hr hsr hfr
    intro z
    have hh := hr z
    change inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
      dataGeneratorForm P r (y r).val z.val + cellRawSourceFunctional 0 src flux r z.val at hh
    have hz : cellGalerkinValue N z = torusHkValueCLM z.val := rfl
    rw [hz] at hh ⊢
    simpa only [cellRawSourceFunctional, ContinuousLinearMap.coe_coe,
      cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Pi.zero_apply, star_zero, cellShiftedDerivative_zero_apply,
      ← hsr, hfr, add_sub_assoc] using hh
  have hh := molecularFinite_window_flux_energy_bound hab N K ρ hρ P Cv hCv hv hp hb y dy S F hS hF
    (D.variational N).time he t ht
  have hi : factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val ≤
      factorialNormSq ρ u₀.val := by
    dsimp only [y]
    rw [D.initial_value N, hinit]
    exact dataFourierHigh_initial_factorial_le N K ρ u₀
  exact hh.trans (mul_le_mul_of_nonneg_right (add_le_add hi le_rfl) (Real.exp_nonneg _))

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Shared scalar and flux budgets give a common finite-window higher bound without small drift. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.ODE

theorem molecular_finite_window_flux_high_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src flux initial)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hs : ∀ᵐ t ∂volume.restrict (Icc a b), (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : factorialNormSq 1 u₀.val + ∫ s in a..b, factorialNormSq 1 (S s).val + 4 * factorialNormSq 1 (F s).val ≤ B) :
    ∀ N t, t ∈ Icc a b →
      ‖dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))‖ ≤
        Real.sqrt ((B * Real.exp ((1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K) := by
  let C := 1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
    finiteTransportBudget (E := ℂ) K Cv j) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hm := factorialWeightMin_pos 1 (by norm_num) (K := K)
  intro N t ht
  let w := dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))
  have he := molecular_actual_window_flux_energy_bound D K 1 (by norm_num) Cv hCv hv hp hb
    S hs F hS hF hf u₀ hinit N t ht
  have hbnd : factorialNormSq 1 w.val ≤ B * Real.exp (C * (b - a)) := by
    apply he.trans
    apply mul_le_mul hbudget
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hC))
      (Real.exp_nonneg _) hB
  apply (Real.le_sqrt (norm_nonneg w) (div_nonneg (mul_nonneg hB (Real.exp_nonneg _)) hm.le)).2
  apply (le_div_iff₀ hm).2
  have hl := factorialNormSq_lower 1 w.val
  change factorialWeightMin 1 K * ‖w‖ ^ 2 ≤ factorialNormSq 1 w.val at hl
  simpa only [C, mul_comm] using hl.trans hbnd
end

/-! The two existing primitive mixed-source reserve interfaces coincide at slow dimension two. -/

section
open Homogenization AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {H : ℕ}

def jointReserveOfIndependent {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : IndependentParameterSourceReserve H f) : JointSourceReserve H f where
  regular := Q.regular
  periodic := Q.periodic
  measurable := Q.measurable
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound := Q.derivative_bound

def independentReserveOfJoint {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) : IndependentParameterSourceReserve H f where
  regular := Q.regular
  periodic := Q.periodic
  measurable := Q.measurable
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound := Q.derivative_bound
end

/-! Primitive mixed source reserves survive an arbitrary constant change of cell clock. -/

section
open Homogenization MeasureTheory AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def independentSourceReserve_timeMap {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    IndependentParameterSourceReserve H (fun t z Y => f (φ t) z Y) where
  regular t := Q.regular (φ t)
  periodic t Y := Q.periodic (φ t) Y
  measurable Y := (Q.measurable Y).comp
    ((hφ.comp measurable_fst).prodMk measurable_snd)
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn t := Q.derivative_bound n hn (φ t)

def independentSourceReserve_timePrecompose {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (c : ℝ) :
    IndependentParameterSourceReserve H (fun t z Y => f (c * t) z Y) :=
  independentSourceReserve_timeMap Q (fun t => c * t) (measurable_const.mul measurable_id)

variable [BorelSpace E] [SecondCountableTopology E]

def independentSourceReserve_windowTimePrecompose {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (a b c : ℝ) (hc : 0 < c)
    (Q : IndependentParameterSourceReserve H (independentTimeWindowSource (Set.Ioc (c * a) (c * b)) f)) :
    IndependentParameterSourceReserve H (independentTimeWindowSource (Set.Ioc a b)
      (fun t z Y => f (c * t) z Y)) := by
  refine (independentSourceReserve_timePrecompose Q c).congrSource ?_
  funext t z Y
  simp only [independentTimeWindowSource, Set.mem_Ioc, mul_lt_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]


def independentSourceReserve_clock {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (c : ℝ) :
    IndependentParameterSourceReserve H (fun t z Y => c • f (c * t) z Y) :=
  (independentSourceReserve_timePrecompose Q c).map (c • ContinuousLinearMap.id ℝ E)
end

/-! A produced window reserve extends constantly in time, preserving its actual initial zero. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def independentWindowClampedSource (a b : ℝ) (f : ℝ → Vec 2 → P → E)
    (t : ℝ) (z : Vec 2) (Y : P) : E :=
  independentTimeWindowSource (Ioc a b) f (max a (min b t)) z Y

def independentWindowClampedSourceReserve {H : ℕ} (a b : ℝ)
    {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H (independentTimeWindowSource (Ioc a b) f)) :
    IndependentParameterSourceReserve H (independentWindowClampedSource a b f) :=
  independentSourceReserve_timeMap Q (fun t => max a (min b t))
    (measurable_const.max (measurable_const.min measurable_id))
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.WeakEntryProofs

/-! Actual molecular traces retain shared finite-window higher bounds with arbitrary divergence forcing. -/

open AVRegularity.EntryWeakProofs

theorem molecular_regular_flux_exists_window_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsm : Measurable (Function.uncurry src))
    (hfm : Measurable (Function.uncurry flux))
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : factorialNormSq 1 u₀.val + ∫ s in a..b,
      factorialNormSq 1 (S s).val + 4 * factorialNormSq 1 (F s).val ≤ B) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      Continuous u ∧ CellWeakHilbertCurve a b u slice
        (fun t => dataDualDerivative P t (slice t) (cellSourceSlice src t)
          (fun j => cellSourceSlice (fun s x => flux s x j) t)) ∧
      u a = initial ∧
      (∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t ∧
        ‖w‖ ≤ Real.sqrt ((B * Real.exp ((1 + 4 *
          (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
            finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K)) := by
  have hab := hlt.le
  obtain ⟨D⟩ := dataGalerkin_limit_data hab P src flux hsm hfm
    (cellProduct_cellNormSq_finite (Icc a b) src hsp)
    (cellProduct_cellNormSq_finite (Icc a b) flux hfp) initial
  obtain ⟨U, hU, hi⟩ := D.exists_continuous_trace hlt hsp hfp
  let u := extendCurve hab U
  refine ⟨u, D.limit, continuous_extendCurve hab U, hU, hi, ?_⟩
  exact D.higher_flux_trace_uniform_bound hsp hfp K _
    (molecular_finite_window_flux_high_bound D K Cv hCv hv hp hb S hS hs F hF hf
      u₀ hinit B hB hbudget) u hU hi

end AVRegularity.WeakEntryProofs
end

section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.WeakEntryProofs

/-! Genuine independent metric word derivatives, with original finite reserve prices. -/

open AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem general_metric_word_entry_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (B : ℕ → ℝ)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n) (n : ℕ) (hn : n ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1) (Y : P) (t : ℝ) (i j : Fin 2) :
    |independentMetricWordJet G n w Y t i j| ≤ B n := by
  have hword := finite_realWordJet_derivative_bound (fun X => G t X i j) n 0
    ((hr t i j).of_le (by simp)) w hw Y
  rw [norm_iteratedFDeriv_zero, Nat.add_zero, Real.norm_eq_abs] at hword
  exact hword.trans (hb n hn t Y i j)

theorem general_metric_word_entry_measurable
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j)) (n : ℕ)
    (w : Fin n → P) (Y : P) (i j : Fin 2) :
    Measurable (fun t => independentMetricWordJet G n w Y t i j) :=
  finite_independentParameterWordJet_measurable (fun t X => G t X i j) n
    (fun t => (hr t i j).of_le (by simp))
    (fun X => hm X i j) w Y

theorem general_metric_word_cons
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (n : ℕ)
    (w : Fin n → P) (v Y : P) (t : ℝ) (i j : Fin 2) :
    independentMetricWordJet G (n + 1) (Fin.cons v w) Y t i j =
      fderiv ℝ (fun X => independentMetricWordJet G n w X t i j) Y v :=
  finite_realWordJet_cons_eq_fderiv (fun X => G t X i j) n
    ((hr t i j).of_le (by simp)) w v Y

theorem general_metric_word_derivative_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (B : ℕ → ℝ)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n) (n r : ℕ) (hn : n + r ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1) (Y : P) (t : ℝ) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun X => independentMetricWordJet G n w X t i j) Y‖ ≤
      B (n + r) :=
  (finite_realWordJet_derivative_bound (fun X => G t X i j) n r
    ((hr t i j).of_le (by simp)) w hw Y).trans
      (hb (n + r) hn t Y i j)

theorem general_metric_word_quotient_entry_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (B : ℕ → ℝ)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n) (n : ℕ) (hn : n + 1 ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1)
    (Y v : P) (h : ℝ) (hh : h ≠ 0) (t : ℝ) (i j : Fin 2) :
    |h⁻¹ * (independentMetricWordJet G n w (Y + h • v) t i j -
      independentMetricWordJet G n w Y t i j)| ≤ B (n + 1) * ‖v‖ := by
  have hreg : ContDiff ℝ 1 (fun X => independentMetricWordJet G n w X t i j) :=
    finite_realWordJet_contDiff (fun X => G t X i j) n 1
      ((hr t i j).of_le (by simp)) w
  have hfirst (X : P) : ‖fderiv ℝ (fun Z => independentMetricWordJet G n w Z t i j) X‖ ≤
      B (n + 1) := by
    simpa only [norm_iteratedFDeriv_one] using general_metric_word_derivative_bound hr B hb n 1 hn w hw X t i j
  simpa only [Real.norm_eq_abs, smul_eq_mul] using
    independent_parameter_first_quotient_bound _ hreg _ hfirst Y v h hh

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Local inverse extensions give actual cutoff coefficient reserves on the complete time line. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {H : ℕ}

def localWindowCutoffReserve (a b : ℝ) (hab : a ≤ b) (U : Set P)
    (χ : P → ℝ) (hs : tsupport χ ⊆ U)
    (Qχ : IndependentParameterSourceReserve H (fun _ _ Y => χ Y))
    (f f' : ℝ → Vec 2 → P → E)
    (Qf : IndependentParameterSourceReserve H (independentTimeWindowSource (Ioc a b) f'))
    (he : ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, f' t z Y = f t z Y)
    (hz : ∀ Y ∈ U, ∀ z, f a z Y = 0) :
    IndependentParameterSourceReserve H (fun t z Y => χ Y • f (max a (min b t)) z Y) := by
  let Q := Qχ.bilinear (independentWindowClampedSourceReserve a b Qf)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  refine Q.congrSource ?_
  funext t z Y
  change χ Y • independentWindowClampedSource a b f' t z Y = _
  by_cases hχ : χ Y = 0
  · simp only [hχ, zero_smul]
  · have hY : Y ∈ U := hs (subset_tsupport χ (Function.mem_support.mpr hχ))
    have ht := metric_clamp_mem a b hab t
    change χ Y • independentTimeWindowSource (Ioc a b) f' (max a (min b t)) z Y = _
    by_cases ha : a < max a (min b t)
    · rw [show independentTimeWindowSource (Ioc a b) f' (max a (min b t)) z Y =
          f' (max a (min b t)) z Y from ite_eq_left ⟨ha, ht.2⟩]
      rw [he _ ht Y hY z]
    · have hca : max a (min b t) = a := le_antisymm (not_lt.mp ha) ht.1
      rw [hca]
      simp only [independentTimeWindowSource, mem_Ioc, lt_self_iff_false, false_and,
        ite_false, hz Y hY, smul_zero]
end

/-! Genuine primitive source reserves give every finite-window and spatial L² membership. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution Set

local instance independentSourceWindowIntegrabilityFiniteCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by rw [Measure.restrict_apply_univ, cellCube_volume_one]; exact ENNReal.one_lt_top⟩

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem independent_source_window_memLp {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (a b : ℝ) (Y : P) :
    MemLp (fun p : ℝ × Vec 2 => f p.1 p.2 Y) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  apply MemLp.of_bound (Q.measurable Y).aestronglyMeasurable (Q.budget 0)
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [norm_iteratedFDeriv_zero] using Q.derivative_bound 0 (Nat.zero_le H) p.1 (p.2, Y))

theorem independent_source_slice_memLp {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (t : ℝ) (Y : P) :
    MemLp (fun z => f t z Y) 2 (volume.restrict AVenhance.unitCube) := by
  apply MemLp.of_bound
    (((Q.measurable Y).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Q.budget 0)
  exact Filter.Eventually.of_forall (fun z => by
    change ‖f t z Y‖ ≤ Q.budget 0
    simpa only [norm_iteratedFDeriv_zero] using Q.derivative_bound 0 (Nat.zero_le H) t (z, Y))

theorem independent_source_directional_window_memLp {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (hH : 1 ≤ H) (a b : ℝ) (Y v : P) :
    MemLp (fun p : ℝ × Vec 2 => fderiv ℝ (f p.1 p.2) Y v) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  apply MemLp.of_bound (Q.directional_derivative_measurable hH Y v).aestronglyMeasurable
    (Q.budget 1 * ‖v‖)
  exact Filter.Eventually.of_forall (fun p => by
    have hb := Q.parameter_derivative_bound 1 hH p.1 p.2 Y
    rw [norm_iteratedFDeriv_one] at hb
    exact ((fderiv ℝ (f p.1 p.2) Y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg v)))

theorem independent_source_directional_slice_memLp {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (hH : 1 ≤ H) (t : ℝ) (Y v : P) :
    MemLp (fun z => fderiv ℝ (f t z) Y v) 2 (volume.restrict AVenhance.unitCube) := by
  have hm : Measurable (fun z => fderiv ℝ (f t z) Y v) :=
    (Q.directional_derivative_measurable hH Y v).comp
      (measurable_const.prodMk measurable_id)
  apply MemLp.of_bound hm.aestronglyMeasurable (Q.budget 1 * ‖v‖)
  exact Filter.Eventually.of_forall (fun z => by
    have hb := Q.parameter_derivative_bound 1 hH t z Y
    rw [norm_iteratedFDeriv_one] at hb
    exact ((fderiv ℝ (f t z) Y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg v)))
end

/-! A compact cutoff preserves an arbitrary positive lower metric bound. -/

section
open Homogenization AVRegularity.EntryWeakProofs Set

theorem cutoff_metric_quadratic_form (χ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Vec 2) :
    (∑ i, ∑ j, (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j) =
      χ * (∑ i, ∑ j, A i j * ξ i * ξ j) + (1 - χ) * ∑ i, ξ i ^ 2 := by
  have hI : (∑ i, ∑ j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ i * ξ j) = ∑ i, ξ i ^ 2 := by
    simp [Matrix.one_apply, pow_two]
  have hp i j : (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j =
      χ * (A i j * ξ i * ξ j) + (1 - χ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ i * ξ j) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hI]

theorem positive_cutoff_metric_lower {P : Type*} [TopologicalSpace P] (χ : P → ℝ)
    (hχ : ∀ Y, χ Y ∈ Icc 0 1) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (lo : ℝ) (t : ℝ) (Y : P)
    (he : Y ∈ tsupport χ → ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j) (ξ : Vec 2) :
    min lo 1 * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, cutoffParameterMetric χ G t Y i j * ξ i * ξ j := by
  rw [cutoffParameterMetric_eq_convex, cutoff_metric_quadratic_form]
  have hQ : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hY : Y ∈ tsupport χ
  · have hleft := mul_le_mul_of_nonneg_left (he hY ξ) (hχ Y).1
    have hlo := mul_le_mul_of_nonneg_right (min_le_left lo 1) hQ
    have hone := mul_le_mul_of_nonneg_right (min_le_right lo 1) hQ
    have ha := mul_le_mul_of_nonneg_left hlo (hχ Y).1
    have hb := mul_le_mul_of_nonneg_left hone (sub_nonneg.mpr (hχ Y).2)
    linarith only [hleft, ha, hb]
  · rw [image_eq_zero_of_notMem_tsupport hY, zero_mul, sub_zero, one_mul, zero_add]
    exact (mul_le_mul_of_nonneg_right (min_le_right lo 1) hQ).trans_eq (one_mul _)
end

end AVRegularity.WeakEntryProofs
end
