-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
public import AVRegularity.Proofs.WeakGen.PhaseLatticeLiftData
public import AVRegularity.EntryWeakAssembly.NativeWeakLiftFamilies
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Proofs.ComplexContext.Leaf
import AVRegularity.Proofs.GenSem.LiftOn.Omega

section
section
/-! **Cross-data local lift uniqueness** (the lift uniqueness behind the carried quiet invariant
of the weak passage). The lift recurrence at a slow offset `X` reads the metric and the edges only
near `X` (`liftCellSource_metric_slow_open_congr`, with the edge congruence). So a lift sequence
on `Ω` remains a lift sequence, on any open `U ⊆ Ω`, for any data that agree with its own on `U`
over the window (`isLiftSequenceOn_data_congr`). Two families whose lift data agree on an open `U`
in both carriers have the same lift coefficients on `U` over the window
(`familyLift_cross_unique`, from the native uniqueness). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Set

namespace AVRegularity.Providers.WeakGen

open AVRegularity.EntryWeakProofs

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U) (η : ℝ)
    {G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hG : ∀ X ∈ U, G t X = G' t X) :
    SlowOpenFieldEq U (cellB1 η G v t f) (cellB1 η G' v t f) := by
  intro X hX z
  unfold cellB1
  apply congrArg (fun b : E => _ - Real.sqrt η • b)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hp : SlowOpenFieldEq U (fun Y y => G t Y i j • fastPartial j f Y y)
      (fun Y y => G' t Y i j • fastPartial j f Y y) := fun Y hY y => by
    beta_reduce; rw [hG Y hY]
  rw [hG X hX, hp.slowPartial hU i X hX z]

theorem cellB2_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U) (η : ℝ)
    {G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} (t : ℝ) (f : Vec 2 → Vec 2 → E)
    (hG : ∀ X ∈ U, G t X = G' t X) :
    SlowOpenFieldEq U (cellB2 η G t f) (cellB2 η G' t f) := by
  intro X hX z
  unfold cellB2
  apply congrArg (fun a : E => -(η • a))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hp : SlowOpenFieldEq U (fun Y y => G t Y i j • slowPartial j f Y y)
      (fun Y y => G' t Y i j • slowPartial j f Y y) := fun Y hY y => by
    beta_reduce; rw [hG Y hY]
  exact hp.slowPartial hU i X hX z

end Metric

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hG : ∀ X ∈ U, Q.G t X = G' t X) :
    SlowOpenFieldEq U (liftA Q Cc f hh n t) (liftA {Q with G := G'} Cc f hh n t) := by
  intro X hX z
  change _ + _ - _ = _ + _ - _
  rw [cellB1_metric_slow_open_congr hU Q.η Q.v t _ hG X hX z]
  congr 2
  split_ifs
  · exact cellB2_metric_slow_open_congr hU Q.η t _ hG X hX z
  · rfl

theorem liftCellSource_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hG : ∀ X ∈ U, Q.G t X = G' t X) :
    SlowOpenFieldEq U (liftCellSource Q Cc f hh n t)
      (liftCellSource {Q with G := G'} Cc f hh n t) := by
  have ha := liftA_metric_slow_open_congr hU Q G' Cc f hh n t hG
  have hm := ha.fieldCellMean
  intro X hX z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean {Q with G := G'} Cc f p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    exact liftApply_slow_open_congr hU j t (Cc p.1 j) (Cc p.1 j)
      (liftMean Q Cc f p.2 (n - j)) (liftMean {Q with G := G'} Cc f p.2 (n - j))
      (fun _ _ _ _ _ _ _ _ => rfl)
      (fun Y hY => (liftA_metric_slow_open_congr hU Q G' Cc f p.2 (n - j) t hG).fieldCellMean
        Y hY 0) X hX z
  change -(liftA Q Cc f hh n t X z - liftMean Q Cc f hh n t X) + _ = _
  rw [ha X hX z, show liftMean Q Cc f hh n t X =
    liftMean {Q with G := G'} Cc f hh n t X from hm X hX z, hsum]
  rfl

variable [∀ i, FiniteDimensional ℝ (h i)]

/-- A lift sequence on `Ω` is one on any smaller set. -/
theorem isLiftSequenceOn_mono {Ω Ω' : Set (Vec 2)} (hΩ : Ω' ⊆ Ω) {Q : LiftOperatorData ι h D}
    {sX sZ : ℕ} {a b : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc) : IsLiftSequenceOn Ω' Q sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhh n m α v u t ht
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hc.2.2.2.2.2.1 hh hhh n m α v u t ht
    exact ⟨⟨fun X hX => h1 X (hΩ hX), fun b hb z => (h2 b hb z).mono hΩ,
      fun a' b' ha hb => (h3 a' b' ha hb).mono (Set.prod_mono hΩ le_rfl)⟩, h4⟩
  · intro hh hhh n hn hnN f hf X hX
    exact hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X (hΩ hX)

/-- **A lift sequence for data that agree on an open set over the window.** -/
theorem isLiftSequenceOn_data_congr {U : Set (Vec 2)} (hU : IsOpen U)
    {Q Q' : LiftOperatorData ι h D} {sX sZ : ℕ} {a b : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hc : IsLiftSequenceOn U Q sX sZ a b N H Cc)
    (hη : Q'.η = Q.η) (hv : Q'.v = Q.v) (hG : ∀ t ∈ Icc a b, ∀ X ∈ U, Q.G t X = Q'.G t X)
    (hE : ∀ t ∈ Icc a b, SlowOpenEdgeEq U t Q.edge Q'.edge) :
    IsLiftSequenceOn U Q' sX sZ a b N H Cc := by
  have h1 := isLiftSequenceOn_edge_window_congr hU Q Q'.edge a b sX sZ N H Cc hc hE
  obtain ⟨η', G', v', e'⟩ := Q'
  simp only at hη hv hG hE h1
  subst hη hv
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X hX
  have h2 := h1.2.2.2.2.2.2 hh hhh n hn hnN f hf X hX
  have h3 := WeakEntryProofs.cellFieldInverse_metric_congr_on _ (fun t => Matrix.of (G' t X)) _ sZ a b _ _ _
    (fun t ht => by simp only [hG t ht X hX]) h2
  refine CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _
    (fun t ht => ?_) h3
  funext z
  exact liftCellSource_metric_slow_open_congr hU ⟨Q.η, Q.G, Q.v, e'⟩ G' Cc (fun _ => f) hh n t
    (hG t ht) X hX z

section Cross

variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, InnerProductSpace ℝ (hv i)]
  [∀ i, FiniteDimensional ℝ (hv i)] {Dm : ℕ}

/-- **Cross-data local lift uniqueness**: two families whose lift data agree on an open set `U`
in both carriers, over the window, have the same lift coefficients there. -/
theorem familyLift_cross_unique (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ)
    (hslot : Odd slot) (A A' : RealChain) (ρ : ℝ) (edge edge' : ConstituentEdges Dm hv)
    {Ω Ω' U : Set (Vec 2)} (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hUΩ' : U ⊆ Ω') (a b : ℝ)
    (hab : a ≤ b) (N H sX sZ sX' sZ' : ℕ) (Cc Dc : ℕ → ℕ → LiftCoeff ι hv)
    (hc : IsLiftSequenceOn Ω (familyLiftData D m slot A ρ edge) sX sZ a b N H Cc)
    (hd : IsLiftSequenceOn Ω' (familyLiftData D m slot A' ρ edge') sX' sZ' a b N H Dc)
    (hG : ∀ t ∈ Icc a b, ∀ X ∈ U, (familyLiftData D m slot A' ρ edge').G t X =
      (familyLiftData D m slot A ρ edge).G t X)
    (hE : ∀ t ∈ Icc a b, SlowOpenEdgeEq U t (familyLiftData D m slot A' ρ edge').edge
      (familyLiftData D m slot A ρ edge).edge) :
    ∀ hh, hh ≤ H → ∀ n l (α : DerivativeWord2 l) t, t ∈ Icc a b → ∀ X ∈ U, ∀ z v u,
      Cc hh n l α t X z v u = Dc hh n l α t X z v u := by
  have hd' := isLiftSequenceOn_data_congr (Q' := familyLiftData D m slot A ρ edge) hU
    (isLiftSequenceOn_mono hUΩ' hd) rfl rfl hG hE
  exact WeakEntryProofs.native_family_lift_coefficients_unique D hζ m slot hslot A ρ edge U hU
    a b hab N H sX sZ sX' sZ' Cc Dc (isLiftSequenceOn_mono hUΩ hc) hd'

end Cross

end AVRegularity.Providers.WeakGen
end
end

section
/-! Choose inherited lift arrays at fixed phase representatives. Their lift clauses transport
back to the original history; their source means are phase invariant on the solving window. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs AVRegularity.Providers.GenSem
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm b j₀}

/-- Select every inherited array at the normalized history. -/
def phaseNormalizedLifts
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) :
    ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ) :=
  fun s k A => Cc s k (phaseRepresentative A)

/-- Re-indexing by normalized histories preserves the actual localized lift family. -/
theorem phaseNormalizedLifts_isLiftFamily (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (hgen : WeakHolGen G) (sX sZ N : ℕ) (ρ : ℝ)
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hc : ∀ s : WeakSource G, s.IsLiftFamily sX sZ N ρ (Cc s)) :
    ∀ s : WeakSource G, s.IsLiftFamily sX sZ N ρ (phaseNormalizedLifts Cc s) := by
  intro s
  cases s with
  | eddy v w n => trivial
  | inherited w h π n =>
    intro k A hA
    have hp := phaseRepresentative_equivalent A
    have hB := hp.admissible D b j₀ G.level k hA.1
    exact weakHolGen_path_lift_transport hΛ hζ hband hb G hgen π k hA.2 ρ A
      (phaseRepresentative A) hA.1 hB hp sX sZ N _
      (hc (.inherited w h π n) k (phaseRepresentative A) ⟨hB, hA.2⟩)

/-- Physical pulse times belong to the original molecular solving window. -/
theorem physical_pulse_cell_time (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (k : ℤ)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) :
    (D.cellScaleSq m)⁻¹ * t ∈ Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband m
  exact ⟨by simpa only [div_eq_inv_mul, OCData.slotStart] using div_le_div_of_nonneg_right ht.1 hc.le,
    by simpa only [div_eq_inv_mul] using div_le_div_of_nonneg_right ht.2 hc.le⟩

/-- Normalized inherited arrays and native grade-zero arrays yield phase-invariant source means
at every physical time read by a nonzero transfer cutoff. -/
theorem phaseNormalized_source_flux_phase_window (N : ℕ) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hb : 0 < b) (hgen : WeakHolGen G)
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (s : WeakSource G) (k : ℤ) (A B : RealChain)
    (hphase : WeakChainPhaseLatticeEquivalent A B) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) :
    s.fluxOp (D.eps (G.level - 1)) (phaseNormalizedLifts Cc s)
      (nativeWeakEddyLiftFamily D Dm b j₀ G.level hΛ hζ hband N) k t A =
    s.fluxOp (D.eps (G.level - 1)) (phaseNormalizedLifts Cc s)
      (nativeWeakEddyLiftFamily D Dm b j₀ G.level hΛ hζ hband N) k t B := by
  classical
  cases s with
  | eddy v w n => exact native_weak_eddy_source_phase_lattice N hΛ hζ hband v w n _ k A B hphase t
  | inherited w h π n =>
    by_cases hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k
    · have hB : IsAdmissibleChain D b j₀ G.level k B ∧ Odd k :=
        ⟨hphase.admissible D b j₀ G.level k hA.1, hA.2⟩
      simp only [WeakSource.fluxOp, dite_eq_left hA, dite_eq_left hB,
        phaseNormalizedLifts, phaseRepresentative_eq hphase]
      let QA := familyLiftData D G.level k A (D.eps (G.level - 1))
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)
      let QB := familyLiftData D G.level k B (D.eps (G.level - 1))
        (pathEdges G π ⟨k, hB.2⟩ ⟨B, hB.1⟩)
      have he := weakHolGen_lifted_edges_phase_lattice hΛ hζ hband hb G hgen π k hA.2
        (D.eps (G.level - 1)) A B hA.1 hB.1 hphase _
        (physical_pulse_cell_time hΛ hζ hband G.level k t ht)
      have hQ : {QA with edge := QB.edge} = QB :=
        familyLiftData_geometry_congr D G.level k A B hA.1.2.2.1 hB.1.2.2.1
          (hphase.geom D hΛ hB.1.2.2.2.2.1) _ (pathEdges G π ⟨k, hB.2⟩ ⟨B, hB.1⟩)
      have hh := pathMeanFlux_edge_time_congr D G.level (D.eps (G.level - 1)) QA QB.edge
        (Cc (.inherited w h π n) k (phaseRepresentative B)) n t he
      rw [hQ] at hh
      exact hh
    · have hB : ¬ (IsAdmissibleChain D b j₀ G.level k B ∧ Odd k) := by
        rintro ⟨hB, hk⟩
        exact hA ⟨hphase.symm.admissible D b j₀ G.level k hB, hk⟩
      simp only [WeakSource.fluxOp, dite_eq_right hA, dite_eq_right hB]

end AVRegularity.Providers.WeakGen
end
end

section
/-! Transfer periodicity needs phase invariance only on the active pulse window. -/
@[expose] public noncomputable section
namespace AVRegularity.Providers.WeakGen
open AVRegularity.WeakEntryProofs
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.EntryWeakProofs

theorem transferAt_periodic_of_phase_window (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (pc : ℤ) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp)
    (A : RealChain) (hf : ∀ k t, t ∈ ocPulseWindow D.α D.q D.Λ (A.ctxLevel + 1) k →
      ∀ A B, WeakChainPhaseLatticeEquivalent A B → fop k t A = fop k t B)
    (hA : A.WellSlotted) (hslot : Odd A.slot)
    (t : ℝ) (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    IsZ2Periodic (fun z => transferAt D (A.ctxLevel + 1) pc lam Dγ fop t A z d word) := by
  intro n z
  simp only [transferAt, Nat.add_sub_cancel]
  apply congrArg (fun w : Vec 2 => ((D.kap A.ctxLevel * D.eps A.ctxLevel ^ (d - 2))⁻¹ * lam) • w)
  apply finsum_congr
  intro k
  apply finsum_congr
  intro hk
  by_cases hcut : ocCutoff D.α D.q D.Λ (A.ctxLevel + 1) k t = 0
  · simp only [hcut, zero_smul]
  have ht := GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos hΛ) hcut
  apply congrArg (fun w : Vec 2 => ocCutoff D.α D.q D.Λ (A.ctxLevel + 1) k t • w)
  have hE : D.eps A.ctxLevel ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hK : (fun x => (childTransition D k t (A.recenter D x)
      (z + latticeShift n + (D.eps A.ctxLevel)⁻¹ • x))⁻¹) =
      (fun x => (childTransition D k t (A.recenter D x)
        (z + (D.eps A.ctxLevel)⁻¹ • x))⁻¹) := by
    funext x a b
    have he := weak_transfer_matrix_joint_fast_periodic D hΛ hζ A hA hslot k t
      ((D.eps A.ctxLevel)⁻¹ • x) a b n z
    simpa only [smul_inv_smul₀ hE] using he
  have hF := hf k t ht _ _ (weak_appendChild_phase_lattice D hΛ A hslot k t z n)
  rw [hK, hF]

/-- Normalized inherited lifts give periodic transferred coefficients of a weak successor. -/
theorem phaseNormalized_transferred_flux_periodic {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm b j₀) (N : ℕ) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hb : 0 < b) (hgen : WeakHolGen G) (hlevel : 1 ≤ G.level)
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (η : ℝ) (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p)
    (s : WeakSource G) (d : ℕ) (word : DerivativeWord2 (d - 1)) (t : ℝ) (X : Vec 2) :
    IsZ2Periodic (weakSourceTransferredFlux G η (phaseNormalizedLifts Cc)
      (nativeWeakEddyLiftFamily D Dm b j₀ G.level hΛ hζ hband N) p c s d word t X) := by
  classical
  let fop := s.fluxOp (D.eps (G.level - 1)) (phaseNormalizedLifts Cc s)
    (nativeWeakEddyLiftFamily D Dm b j₀ G.level hΛ hζ hband N)
  let A := c.1.recenter D (D.eps (G.level - 1 - 1) • X)
  change IsZ2Periodic (fun z => if IsAdmissibleChain D b j₀ (G.level - 1) p.1 A then
    transferAt D G.level p.1 (s.lam G.level η) s.degree fop t A z d word else 0)
  by_cases hX : IsAdmissibleChain D b j₀ (G.level - 1) p.1 A
  · have hctx : A.ctxLevel + 1 = G.level := by have := hX.1; omega
    have hslot : Odd A.slot := by rw [hX.2.2.2.1]; exact p.2
    have hf : ∀ k t, t ∈ ocPulseWindow D.α D.q D.Λ (A.ctxLevel + 1) k →
        ∀ A B, WeakChainPhaseLatticeEquivalent A B → fop k t A = fop k t B := by
      rw [hctx]
      intro k t ht A B hp
      exact phaseNormalized_source_flux_phase_window N hΛ hζ hband hb hgen Cc s k A B hp t ht
    have he := transferAt_periodic_of_phase_window D hΛ hζ p.1
      (s.lam G.level η) s.degree fop A hf hX.2.2.1 hslot t d word
    rw [hctx] at he
    simpa only [ite_eq_left hX] using he
  · intro n z
    simp only [ite_eq_right hX]

end AVRegularity.Providers.WeakGen
end
end
end

section
section
/-! Holomorphic generation supplies genuinely reserved local models of every lifted path edge.
One common slow cutoff works for all edges; each finite jet budget may depend on the fixed path. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology Metric
namespace AVRegularity.Providers.WeakGen
open AVRegularity.Sobolev AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem

/-- Assemble finitely many scalar forcing reserves into a vector forcing reserve. -/
def vectorJointReserve (H : ℕ) (f : ℝ → Vec 2 → Vec 2 → Vec 2)
    (Q : ∀ c, JointSourceReserve H (fun t z Y => f t z Y c)) : JointSourceReserve H f where
  regular t := contDiff_pi.mpr (fun c => (Q c).regular t)
  periodic t Y k z := funext (fun c => (Q c).periodic t Y k z)
  measurable Y := Measurable.of_eval (fun c => (Q c).measurable Y)
  budget n := ∑ c, (Q c).budget n
  budget_nonneg n := Finset.sum_nonneg (fun c _ => (Q c).budget_nonneg n)
  derivative_bound n hn t X :=
    (Construction.Preservation.FullLift.norm_iteratedFDeriv_vector_le_sum 2 n
      (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2)
      (fun c => ((Q c).regular t).of_le (by exact_mod_cast hn)) X).trans
        (Finset.sum_le_sum (fun c _ => (Q c).derivative_bound n hn t X))

/-- Smoothness, window measurability, and local compact jets of a lifted path coefficient. -/
theorem weak_path_edge_local_data {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge v u d)
    (β : DerivativeWord2 (d.1 - 1)) (c : Fin 2) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    (∀ t ∈ T, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => γ.coeff β t X.2 X.1 c) {X | X.2 ∈ Ω}) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : T × Vec 2 => γ.coeff β Z.1 Y Z.2 c)) ∧
    (∀ K : Set (Vec 2 × Vec 2), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => γ.coeff β t Z.2 Z.1 c) X‖ ≤ B) := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  simp only [familyLiftData, liftEdges, List.mem_map] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  simp only [pathEdges] at hγ₀
  split_ifs at hγ₀ with hvu hd
  · simp only [List.mem_singleton] at hγ₀
    subst hγ₀
    obtain ⟨f, F, hF, hval⟩ := hgen _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 β c
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    let Ω := ladderOmega D b j₀ G.level k A ρ
    have hclock : MapsTo (fun t => D.cellScaleSq G.level * t) T
        (ocPulseWindow D.α D.q D.Λ G.level k) :=
      fun _ ht => cellScaleSq_mul_mem_ocPulseWindow hc ht
    obtain ⟨hr, hm, hj⟩ := holomorphic_recenter_data hΛ hb (hF ⟨k, hk⟩).2 A ρ T
      (fun t => D.cellScaleSq G.level * t) (continuous_const.mul continuous_id) hclock
    have he t (ht : t ∈ T) (X : Vec 2 × Vec 2) (hX : X.2 ∈ Ω) :
        G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X.2) X.1 c =
          f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • X.2)) X.1 := by
      rw [hval ⟨k, hk⟩ ⟨A, hA⟩ _ (hclock ht), smul_smul, mul_div_cancel₀ _ hε]
      simp only [show IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • X.2)) from hX,
        ↓reduceIte]
    refine ⟨fun t ht => (hr t ht).congr (fun X hX => he t ht X hX), ?_, ?_⟩
    · intro Y hY
      convert hm Y hY using 1
      funext Z
      exact he Z.1 Z.1.2 (Z.2, Y) hY
    · intro K hK hKO n
      obtain ⟨B, hB, hbound⟩ := hj K hK hKO n
      refine ⟨B, hB, fun t ht X hX => ?_⟩
      have heq : (fun Z : Vec 2 × Vec 2 =>
          G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • Z.2) Z.1 c) =ᶠ[𝓝 X]
          (fun Z => f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • Z.2)) Z.1) := by
        filter_upwards [((isOpen_ladderOmega D b j₀ G.level k A ρ).preimage
          continuous_snd).mem_nhds (hKO hX)] with Z hZ
        exact he t ht Z hZ
      rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
      exact hbound t ht X hX
  · simp at hγ₀
  · simp at hγ₀

/-- One common cutoff gives reserved edge models on a neighborhood of each admissible offset. -/
theorem weak_path_local_reserves {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
    ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b₁, SlowOpenEdgeEq V t edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
  classical
  dsimp only
  intro H Y₀ hY
  let Ω := ladderOmega D b j₀ G.level k A ρ
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp (isOpen_ladderOmega D b j₀ G.level k A ρ) Y₀ hY
  let U := ball Y₀ (r / 2)
  have hU : IsOpen U := isOpen_ball
  have hsub : closure U ⊆ Ω := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    intro Y hY
    exact hrΩ (mem_ball.mpr ((mem_closedBall.mp hY).trans_lt (half_lt_self hr)))
  have hK : IsCompact (closure U) := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    exact isCompact_closedBall _ _
  obtain ⟨χ, Qχ, hs, hχ⟩ := local_slow_cutoff_reserve_exists H U hU Y₀
    (mem_ball_self (div_pos hr (by norm_num)))
  obtain ⟨δ, hδ, hδχ⟩ := Metric.mem_nhds_iff.mp hχ
  let V := ball Y₀ δ
  let edge' := weakCutoffEdges χ (weakTimeClampEdges a b₁ edge)
  refine ⟨V, edge', isOpen_ball, mem_ball_self hδ, ?_, ?_⟩
  · intro t ht v u d
    have ht' : t ∈ Icc a b₁ := ht
    dsimp only [edge', weakCutoffEdges, weakTimeClampEdges]
    rw [List.map_map, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun γ _ => ⟨rfl, fun β Y hY z => by
      simp only [Function.comp_apply, min_eq_right ht'.2, max_eq_right ht'.1,
        show χ Y = 1 from hδχ hY, one_smul]⟩
  · have hres : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        Nonempty (JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
      intro v u d γ hγ β
      obtain ⟨γ₁, hγ₁, rfl⟩ := List.mem_map.mp hγ
      obtain ⟨γ₀, hγ₀, rfl⟩ := List.mem_map.mp hγ₁
      have hQ (c : Fin 2) : Nonempty (JointSourceReserve H
          (fun t z Y => χ Y * γ₀.coeff β (max a (min b₁ t)) Y z c)) := by
        obtain ⟨hf, hm, hj⟩ := weak_path_edge_local_data hΛ hζ hκ hb G hgen π k hk ρ A hA
          v u d γ₀ hγ₀ β c
        exact compact_window_cutoff_reserve H a b₁
          (weakData_lift_window D hΛ hζ hκ G.level k) Ω U hU hK hsub χ hs Qχ
          (fun t z Y => γ₀.coeff β t Y z c)
          (fun t ht => (hf t ht).of_le (by exact_mod_cast (show (H : ℕ∞) ≤ ⊤ from le_top)))
          (fun t Y j z => congrFun (γ₀.periodic β t Y j z) c) hm hj
      exact ⟨vectorJointReserve H _ (fun c => (hQ c).some)⟩
    exact ⟨fun v u d γ hγ β => (hres v u d γ hγ β).some⟩

end AVRegularity.Providers.WeakGen
end
end

section
/-! **Weak entry: the carrier calculus with the drift constant of one level**
(`weakLevelComplexContext`). At the passage of level `i` of a weak construction, the standing facts of the carrier calculus
hold with the drift constant `weakCd c i = ε_i^{1+α}/√(κ_iκ_{i-1})` (`ComplexContext.complexContextBase_of_data`,
whose letter profiles are `weakKappa c i`). The drift bound is needed only at the levels `≥ i` of
the drift letters of the expressions of the weak ledger (`ComplexContext.DriftIn`), where it holds with the
constant of the level `i` (`weakCd_spec_ge`: terminal diffusivity, decreasing wavelengths). The induction of the carrier calculus (`ComplexContext.genInv_of_denotes`) then gives each expression a
holomorphic extension whose mode suprema at fixed time are below its majorant. With the trimmed
extension (`ComplexContext.trimExt`) the context size is below the weighted sum of the ledger. The plan
conditions `WeakComplexContextPlanOK` are the carrier constants `CarrierOK 100 CH Υ` of the carrier calculus, and a level
threshold above `j₀ + 2`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

/-- The plan conditions of the carrier calculus at one level: its carrier constants and a level threshold above the
starting level. -/
def WeakComplexContextPlanOK (plan : WeakCoefficientPlan) : Prop :=
  (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
    CarrierOK 100 (plan.constants R).CH (plan.constants R).Υ) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A)
    (j₀ : ℕ), j₀ + 2 ≤ plan.levelThreshold R j₀

variable {plan : WeakCoefficientPlan}

theorem case_Lambda_ge (c : WeakCoefficientInstance plan) : 128 ≤ c.physical.Λ :=
  (plan.baseThreshold_ge _).trans c.base_large

/-- The standing facts of the carrier calculus at a case, with any drift constant. -/
theorem case_complexContextBase (hplan : WeakComplexContextPlanOK plan) (c : WeakCoefficientInstance plan) (Cd : ℝ) :
    ComplexContext.ComplexContextBase c.D c.physical.bw (plan.constants c.request).CH
      (plan.constants c.request).Υ c.j₀ (ComplexContext.complexContextKappa c.physical.bw Cd) Cd :=
  ComplexContext.complexContextBase_of_data c.base.hα₀ c.base.hα₁ c.base.hs₀ c.base.hs₁
    c.base.hq c.base.hζ (case_Lambda_ge c) Cd c.physical.bw_pos
    c.physical.bw_small (hplan.1 c.request) c.carrier c.D c.hα c.hq
    c.hΛ c.hζ c.stream c.M c.band c.term

/-- The drift bound at the level of the passage is an equality. -/
theorem weakCd_spec (c : WeakCoefficientInstance plan) (i : ℕ) :
    c.D.eps i ^ (1 + c.D.α) =
      weakCd c i * Real.sqrt (c.D.kap i * c.D.kap (i - 1)) := by
  have hΛ1 : 1 ≤ c.D.Λ := by rw [c.hΛ]; have := case_Lambda_ge c; omega
  have hζ : IsFastProfile c.D.ζ := by rw [c.hζ]; exact c.base.hζ
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term
      c.D.κ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.term]; exact c.band
  have hk := EntryWeakProofs.weakData_kap_pos c.D hΛ1 hζ hband
  have hs : 0 < Real.sqrt (c.D.kap i * c.D.kap (i - 1)) :=
    Real.sqrt_pos.mpr (mul_pos (hk i) (hk (i - 1)))
  unfold weakCd
  rw [div_mul_cancel₀ _ hs.ne']

/-- **The drift bound at every finer weak level**, with the constant of the level `i > M`: the
diffusivities are the terminal one and the wavelengths decrease. -/
theorem weakCd_spec_ge (c : WeakCoefficientInstance plan) {i i' : ℕ} (hi : c.M < i)
    (hii' : i ≤ i') :
    c.D.eps i' ^ (1 + c.D.α) ≤
      weakCd c i * Real.sqrt (c.D.kap i' * c.D.kap (i' - 1)) := by
  have hkap : ∀ j, c.M ≤ j → c.D.kap j = c.D.κ c.M := by
    intro j hj
    unfold OCData.kap
    rw [c.term, Nat.min_eq_right hj]
  have hsq : c.D.kap i' * c.D.kap (i' - 1) = c.D.kap i * c.D.kap (i - 1) := by
    rw [hkap i' (by omega), hkap (i' - 1) (by omega), hkap i (by omega), hkap (i - 1) (by omega)]
  rw [hsq, ← weakCd_spec c i]
  have hq : 1 < c.D.q := by rw [c.hq]; exact c.base.hq.1
  have hΛ : 128 ≤ c.D.Λ := by rw [c.hΛ]; exact case_Lambda_ge c
  have hα : 0 ≤ 1 + c.D.α := by rw [c.hα]; linarith [c.base.hα₀]
  exact Real.rpow_le_rpow (Applications.eps_pos hq hΛ).le (Applications.eps_antitone hq hΛ hii') hα

/-- **The carrier calculus with the drift constant of one level.** -/
theorem weakLevelComplexContext (hplan : WeakComplexContextPlanOK plan) : WeakLevelComplexContextStatement plan := by
  intro x C mres L hm0 hm2 hled v u γ d I k
  obtain ⟨e, Δ, leaf, hE, ⟨f, hden, hco⟩, hΔ, hL, hSF, hDr, hsum⟩ := hled v u γ d I k
  have hi := x.hi
  have hiJ := x.hiJ
  have hlev : (x.stage (x.i - 1)).level = x.i - 1 := x.pc.level (x.i - 1) le_rfl (by omega)
  have hthr := hplan.2 x.inst.request x.inst.j₀
  have hlarge := x.inst.level_large
  have hj : x.inst.j₀ ≤ (x.stage (x.i - 1)).level := by rw [hlev]; omega
  have hi1 : 1 ≤ (x.stage (x.i - 1)).level := by rw [hlev]; omega
  have hB := case_complexContextBase hplan x.inst (weakCd x.inst x.i)
  have hP := ComplexContext.complexContextInputs hB hΔ
  have hCd : ∀ i', (x.i ≤ ·) i' → 1 ≤ i' →
      x.inst.D.eps i' ^ (1 + x.inst.D.α) ≤
        weakCd x.inst x.i * Real.sqrt (x.inst.D.kap i' * x.inst.D.kap (i' - 1)) :=
    fun i' hi' _ => weakCd_spec_ge x.inst hi hi'
  have hF := fun p : OddSlot =>
    ComplexContext.genInv_of_denotes hB hP hL (x.i ≤ ·) hCd (hden p) (hE p).1 (hSF p) (hDr p) hj hi1 p.2
  choose F hF using hF
  have hbw0 := x.inst.physical.bw_pos
  have hΛ1 : 1 ≤ x.inst.D.Λ := by rw [x.inst.hΛ]; have := case_Lambda_ge x.inst; omega
  refine ⟨f, fun p => ComplexContext.trimExt x.inst.D x.inst.physical.bw (F p),
    fun p => ⟨⟨e p, (hE p).1, (hE p).2, hden p⟩, (hF p).isHolExtension hΛ1 hbw0⟩, hco, ?_⟩
  refine le_trans ?_ hsum
  unfold ctxSize
  refine ENNReal.tsum_le_tsum fun h => ?_
  gcongr with p
  exact (GenStage.ctxModeSup_le_iSup_ctxModeSupAt _ _ _ _ p.1 _ _ h).trans
    (iSup₂_mono fun t ht => (hF p).ctxModeSupAt_trim_le hbw0 hm0 hm2 h ht)

end AVRegularity.Providers.WeakGen
end
end

section
/-! **Facts of one weak passage** (weak entry, inherited ledger). For a passage `i → i - 1` of a partial
construction (`WeakPassageAt`):
* the stages have word ranks at most `(M + J_w - j) R_w`, and every identity raises the rank
  (`IsPartialWeakConstruction.rank`, from `EntryWeakProofs.weakPassage_strict_rank`); so every
  path of the incoming stage has at most `J_w R_w` edges (`WeakPassageAt.pathLen_le`);
* the orders of the incoming and the outgoing identities are at most `N₀ = 1 + J_w N_w`
  (`incoming_maxOrder_le`, `outgoing_maxOrder_le`), a cap independent of the stage cap `Dm`;
* the records are the tags: the incoming lengths are at most `ε_i` (`incoming_length_le`), and an
  inherited identity of a path `π` of degree `n` has the size `∏_j Θ̂_{π_j}`, the length `ε_i` and
  the maximal order `n` (`inherited_record`);
* a stage holomorphically generated with no export is slotwise transverse
  (`WeakHolGen.isSlotTransverse`, generation with no export), and its re-capped stage with no export
  is generated (`WeakHolGen.recap_isGenerated`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
  AVRegularity.EntryWeakProofs

namespace AVRegularity.Providers.WeakGen

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A stage holomorphically generated with no export is slotwise transverse. -/
theorem WeakHolGen.isSlotTransverse {G : GenStage D ScalarH Dm b j₀} (hG : WeakHolGen G)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2))) :
    G.IsSlotTransverse := by
  intro p ctx v u γ d I t ht X z s
  funext c
  obtain ⟨f, F, hf, hc⟩ := hG v u γ d I c
  rw [hc p ctx t ht X (z + s • basisVec (slotParallel p.1)), hc p ctx t ht X z]
  split_ifs with hA
  · exact GenSem.slotTransverse_of_generated hΛ hζ hb hstart (fun _ he _ _ => False.elim he)
      (hf p).1 t ht _ hA z s
  · rfl

/-- The re-capped stage with no export of a stage holomorphically generated is generated. -/
theorem WeakHolGen.recap_isGenerated {G : GenStage D ScalarH Dm b j₀} (hG : WeakHolGen G)
    (N : ℕ) (hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N) :
    (G.recap N hN noExports).IsGenerated := by
  intro p v u γ d I k
  obtain ⟨f, F, hf, hc⟩ := hG v u γ d I k
  exact ⟨f p, (hf p).1, fun c t ht X z => hc p c t ht X z⟩

/-- The records of the outgoing identities of a weak passage have the incoming wavelength as
length. -/
theorem IsWeakPassage.length_eq {P : ProvParams} {Mn : WeakMenu} {rW : ℝ} {Din : ℕ}
    {G G' : GenStage D ScalarH Dm b j₀} (hp : IsWeakPassage D P Mn rW Din G G')
    (ht : G'.HasTags P) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) :
    (G'.fam.identity v u γ).record.length = D.eps G.level := by
  obtain ⟨w⟩ := IsWeakPassage.witness hp
  have h1 := (ht v u γ).1.2.2.2.1
  rw [w.prov v u γ] at h1
  rw [h1]
  generalize (w.e v u γ).1 = s
  cases s <;> rfl

variable {plan : WeakCoefficientPlan}

/-- The order cap of the weak stages, `N₀ = 1 + J_w N_w`. -/
abbrev weakCap (x : WeakCoefficientInstance plan) : ℕ := 1 + x.physical.Jw * x.physical.Nw

/-- **The word ranks of a partial construction.** -/
theorem IsPartialWeakConstruction.rank {x : WeakCoefficientInstance plan} {i : ℕ}
    {stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀}
    (h : IsPartialWeakConstruction x i stage) :
    ∀ n, n ≤ x.M + x.physical.Jw - i →
      (∀ c ∈ (stage (x.M + x.physical.Jw - n)).comps,
        weakComponentRank c ≤ n * x.physical.Rw) ∧
      ∀ v u, (stage (x.M + x.physical.Jw - n)).fam.Γ v u →
        weakComponentRank u.1 < weakComponentRank v.1 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    obtain ⟨-, hcomps, hempty, -⟩ := h.1
    refine ⟨fun c hc => ?_, fun v u γ => ((hempty v u).false γ).elim⟩
    rw [hcomps, Finset.mem_singleton] at hc
    subst hc
    simp [weakComponentRank]
  | succ n ih =>
    intro hn
    obtain ⟨hC, hR⟩ := ih (by omega)
    have hp := (h.2 (x.M + x.physical.Jw - n) (by omega) (by omega)).1
    rw [show x.M + x.physical.Jw - (n + 1) = x.M + x.physical.Jw - n - 1 by omega]
    refine ⟨fun c hc => ?_, weakPassage_strict_rank _ _ _ _ _ _ hp hR⟩
    rw [hp.2.2.2.1] at hc
    have h1 := weakExtComps_rank_bound _ _ _ _ _ hC c hc
    rw [Nat.succ_mul]
    exact h1

namespace WeakPassageAt

variable (x : WeakPassageAt plan)

theorem passage :
    IsWeakPassage x.inst.D x.inst.P x.inst.menu (x.inst.D.termRW x.inst.physical.σw x.inst.M)
        (1 + (x.inst.M + x.inst.physical.Jw - x.i) * x.inst.menu.N) (x.stage x.i)
        (x.stage (x.i - 1)) ∧
      (x.stage (x.i - 1)).HasTags x.inst.P :=
  x.pc.2 x.i (by have := x.hi; omega) x.hiJ

/-- **The paths of the incoming stage have at most `J_w R_w` edges.** -/
theorem pathLen_le {h : ℕ} (π : StagePath (x.stage x.i) h) :
    h ≤ x.inst.physical.Jw * x.inst.physical.Rw := by
  have hi := x.hi
  have hiJ := x.hiJ
  have hr := x.pc.rank (x.inst.M + x.inst.physical.Jw - x.i) (by omega)
  rw [show x.inst.M + x.inst.physical.Jw - (x.inst.M + x.inst.physical.Jw - x.i) = x.i by
    omega] at hr
  exact (stagePath_length_le_rank_bound _ (fun v u γ => hr.2 v u γ) _ hr.1 h π).trans
    (Nat.mul_le_mul_right _ (by omega))

/-- The orders of the incoming identities are at most `N₀`. -/
theorem incoming_maxOrder_le (v u : CompIn (x.stage x.i).comps)
    (γ : (x.stage x.i).fam.Γ v u) :
    ((x.stage x.i).fam.identity v u γ).maxOrder ≤ weakCap x.inst := by
  refine (x.passage.1.2.2.1 v u γ).trans ?_
  have := x.hi
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) 1

/-- The maximal order of an outgoing identity is the degree of its source. -/
theorem outgoing_maxOrder (w : CaseWitness x) (v' u' : CompIn (x.stage (x.i - 1)).comps)
    (γ' : (x.stage (x.i - 1)).fam.Γ v' u') :
    ((x.stage (x.i - 1)).fam.identity v' u' γ').maxOrder = (w.e v' u' γ').1.degree := by
  rw [(x.passage.2 v' u' γ').2, w.prov v' u' γ']
  generalize (w.e v' u' γ').1 = s
  cases s <;> rfl

/-- The orders of the outgoing identities are at most `N₀`. -/
theorem outgoing_maxOrder_le (w : CaseWitness x) (v' u' : CompIn (x.stage (x.i - 1)).comps)
    (γ' : (x.stage (x.i - 1)).fam.Γ v' u') :
    ((x.stage (x.i - 1)).fam.identity v' u' γ').maxOrder ≤ weakCap x.inst := by
  rw [x.outgoing_maxOrder w]
  have hV := (w.e v' u' γ').2.1
  have hi := x.hi
  have hiJ := x.hiJ
  have hJ := x.inst.physical.Jw_pos
  have hm : (x.inst.M + x.inst.physical.Jw - x.i) * x.inst.physical.Nw + x.inst.physical.Nw ≤
      x.inst.physical.Jw * x.inst.physical.Nw := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hN := x.inst.physical.Nw_pos
  generalize (w.e v' u' γ').1 = s at hV
  cases s with
  | inherited wd h π n =>
    simp only [WeakSource.Valid] at hV
    simp only [WeakSource.degree, weakCap]
    omega
  | eddy v wd n =>
    simp only [WeakSource.Valid] at hV
    simp only [WeakSource.degree, weakCap]
    have : x.inst.physical.Nw ≤ x.inst.physical.Jw * x.inst.physical.Nw :=
      Nat.le_mul_of_pos_left _ x.inst.physical.Jw_pos
    omega

/-- The incoming stage has the tags of its records (vacuously at the root). -/
theorem incoming_hasTags : (x.stage x.i).HasTags x.inst.P := by
  by_cases hT : x.i = x.inst.M + x.inst.physical.Jw
  · intro v u γ
    have hroot := x.pc.1
    rw [← hT] at hroot
    exact ((hroot.2.2.1 v u).false γ).elim
  · have hiJ := x.hiJ
    have := (x.pc.2 (x.i + 1) (by omega) (by omega)).2
    simpa only [Nat.add_sub_cancel] using this

/-- The lengths of the incoming records are at most the incoming wavelength. -/
theorem incoming_length_le (v u : CompIn (x.stage x.i).comps) (γ : (x.stage x.i).fam.Γ v u) :
    ((x.stage x.i).fam.identity v u γ).record.length ≤ x.inst.D.eps (x.stage x.i).level := by
  by_cases hT : x.i = x.inst.M + x.inst.physical.Jw
  · have hroot := x.pc.1
    rw [← hT] at hroot
    exact ((hroot.2.2.1 v u).false γ).elim
  · have hi := x.hi
    have hiJ := x.hiJ
    have hp := x.pc.2 (x.i + 1) (by omega) (by omega)
    have hlen := IsWeakPassage.length_eq hp.1 hp.2
    have hlev := x.pc.level
    rw [show x.i + 1 - 1 = x.i by omega] at hlen
    rw [hlen v u γ, hlev (x.i + 1) (by omega) (by omega), hlev x.i (by omega) hiJ]
    have hq : 1 < x.inst.D.q := by rw [x.inst.hq]; exact x.inst.base.hq.1
    have hΛ : 128 ≤ x.inst.D.Λ := by rw [x.inst.hΛ]; exact case_Lambda_ge x.inst
    exact Applications.eps_antitone hq hΛ (Nat.le_succ _)

/-- **The record of an inherited identity**: the product of the incoming record sizes along its
path, the incoming wavelength, and its degree. -/
theorem inherited_record (w : CaseWitness x) (v' u' : CompIn (x.stage (x.i - 1)).comps)
    (γ' : (x.stage (x.i - 1)).fam.Γ v' u') {wd : List WordLetter} {h : ℕ}
    {π : StagePath (x.stage x.i) h} {n : ℕ} (hs : (w.e v' u' γ').1 = .inherited wd h π n) :
    ((x.stage (x.i - 1)).fam.identity v' u' γ').record.size =
        ∏ j : Fin h, ((x.stage x.i).fam.identity _ _ (π.step j).2.2).record.size ∧
      ((x.stage (x.i - 1)).fam.identity v' u' γ').record.length =
        x.inst.D.eps (x.stage x.i).level ∧
      ((x.stage (x.i - 1)).fam.identity v' u' γ').maxOrder = n := by
  have ht := x.passage.2 v' u' γ'
  rw [w.prov v' u' γ', hs] at ht
  obtain ⟨⟨hsz, -, -, hlen, -, -⟩, hord⟩ := ht
  refine ⟨?_, hlen, hord⟩
  rw [hsz]
  change (π.provList.map fun y => (y.2.2.tags x.inst.P).witness).prod = _
  simp only [StagePath.provList, List.map_ofFn, List.prod_ofFn]
  exact Finset.prod_congr rfl fun j _ => ((x.incoming_hasTags _ _ (π.step j).2.2).1.1).symm

end WeakPassageAt

end AVRegularity.Providers.WeakGen
end
end
end
