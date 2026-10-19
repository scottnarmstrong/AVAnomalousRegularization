-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.CoordinateWordFiniteWindowHigherProduction
import AVRegularity.EntryWeakAssembly.CoordinateWordRawHilbertCurves
import AVRegularity.EntryWeak.IndependentFreshAppendPhasePeriodicity
public import AVRegularity.EntryWeak.IndependentCenteredChildReanchorCoordinates
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

/-! Genuine primitive reserves produce uniform higher carriers of every literal inverse-word quotient. -/

open AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_window_quotient_carrier_exists {a b : ℝ} (hab : a < b)
    (N L : ℕ) (hH : N + L + 1 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbG : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (hGs : ∀ t Y, (G t Y).IsSymm)
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (P : Vec d → MolecularData)
    (hP : ∀ Y, dataCoefficients (P Y) = ⟨(fun t _ => G t Y), (P Y).v, 0, 0⟩)
    (v : ℝ → Vec 2 → Vec 2)  (hPv : ∀ Y, (P Y).v = v)
    (Cv : ℕ → ℝ) (hCv : ∀ K, 0 ≤ Cv K)
    (hv : ∀ Y K, K ≤ H → ∀ t, ContDiff ℝ (K : ℕ∞) ((P Y).v t))
    (hpv : ∀ Y t, AVenhance.IsZ2Periodic ((P Y).v t))
    (hvb : ∀ Y K, K ≤ H → ∀ t j, j ≤ K → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => (P Y).v t z k) x‖ ≤ Cv K)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hi : ∀ Y w, w.length ≤ N →
      cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : List (Fin d)) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ L) (i : Fin d) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (Y : Vec d) (h : ℝ), h ≠ 0 → ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (h⁻¹ • (c w (Y + h • basisVec i) - c w Y)) t := by
  let T := Vec d × NonzeroIncrement
  let Y1 := fun y : T => y.1 + y.2.val • basisVec i
  let G0 := fun y : T => fun p : List (Fin d) =>
    fun t => independentMetricWordJet G p.length (coordinateWordDirections p) y.1 t
  let G1 := fun y : T => fun p : List (Fin d) =>
    fun t => independentMetricWordJet G p.length (coordinateWordDirections p) (Y1 y) t
  let f0 := fun y : T => fun p : List (Fin d) => fun t => cellQ0 (coordinateSourceWord f p y.1 t)
  let f1 := fun y : T => fun p : List (Fin d) => fun t => cellQ0 (coordinateSourceWord f p (Y1 y) t)
  let F0 := fun y : T => fun p : List (Fin d) => coordinateSourceWord F p y.1
  let F1 := fun y : T => fun p : List (Fin d) => coordinateSourceWord F p (Y1 y)
  let D0 := fun y : T => fun p : List (Fin d) => c p y.1
  let D1 := fun y : T => fun p : List (Fin d) => c p (Y1 y)
  have hc Y p (hp : p.length ≤ N) : IsCellSolution (Icc a b) ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f p Y t))
      (coordinateSourceWord F p Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) p) (c p Y) := by
    have hh := hsol Y p hp
    rw [hP Y, hPv Y] at hh
    exact hh
  have hnil (Y : Vec d) (t : ℝ) :
      independentMetricWordJet G 0 (coordinateWordDirections []) Y t = G t Y := by
    ext a b
    exact iteratedFDeriv_zero_apply _
  have hP0 (y : T) : dataCoefficients (P y.1) = ⟨fun t _ => G0 y [] t, (P y.1).v, 0, 0⟩ := by
    have he : (fun t (_ : Vec 2) => G0 y [] t) = fun t _ => G t y.1 := by
      funext t z
      exact hnil y.1 t
    rw [he]
    exact hP y.1
  have hD (y : T) (p : List (Fin d)) (hp : p.length ≤ N) :
      IsCellSolution (Icc a b) (dataCoefficients (P y.1)) (f0 y p)
        (F0 y p + independentWordMetricFlux (fun q t _ => G0 y q t) (D0 y) p) (D0 y p) :=
    hsol y.1 p hp
  have hE (y : T) (p : List (Fin d)) (hp : p.length ≤ N) :
      IsCellSolution (Icc a b) ⟨fun t _ => G1 y [] t, (P y.1).v, 0, 0⟩ (f1 y p)
        (F1 y p + independentWordMetricFlux (fun q t _ => G1 y q t) (D1 y) p) (D1 y p) := by
    have he : (fun t (_ : Vec 2) => G1 y [] t) = fun t _ => G t (Y1 y) := by
      funext t z
      exact hnil (Y1 y) t
    rw [he, hPv y.1]
    exact hc (Y1 y) p hp
  let Ns := fun (p : List (Fin d)) (r : ℕ) =>
    ∑ j : JetIndex2 r, 2 * (Qf.budget (p.length + (j.1.val + 1)) * ‖basisVec (0 : Fin 2)‖)
  let Nf := fun (p : List (Fin d)) (r : ℕ) =>
    ∑ j : JetIndex2 r, QF.budget (p.length + (j.1.val + 1)) * ‖basisVec (0 : Fin 2)‖
  let Q := fun (y : T) (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hr : r ≤ L) =>
    coordinateWordQuotientHigherSourceData Qf QF p r (by omega) a b y.1 i y.2.val y.2.property
  have hcar (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hrL : r ≤ L + 1) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y : T, ∃ u : ℝ → TorusHk r ℂ,
        StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (D1 y p) t := by
    obtain ⟨R, hR, hh⟩ := coordinate_word_finite_window_higher_carrier_exists hab N (by omega)
      hr hm B hB hbG Qf QF P Cv hCv hv hpv hvb c hsol hi p hp r (by omega)
    exact ⟨R, hR, fun y => hh (Y1 y)⟩
  obtain ⟨R, hR, hq⟩ := uniform_word_window_difference_higher_carrier_exists hab N L
    (fun y : T => P y.1) G0 G1 hP0 f0 f1 F0 F1 D0 D1 (fun y => y.2.val⁻¹)
    (fun y t => by
      change (independentMetricWordJet G 0 (coordinateWordDirections []) y.1 t).IsSymm
      rw [hnil]
      exact hGs t y.1)
    (fun y t => by
      change (independentMetricWordJet G 0 (coordinateWordDirections []) (Y1 y) t).IsSymm
      rw [hnil]
      exact hGs t (Y1 y)) hD hE
    Cv hCv (fun y r hr => hv y.1 r (by omega)) (fun y => hpv y.1)
    (fun y r hr => hvb y.1 r (by omega)) Q Ns Nf
    (fun p r => Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num)
      (mul_nonneg (Qf.budget_nonneg _) (norm_nonneg _)))
    (fun p r => Finset.sum_nonneg fun j _ => mul_nonneg (QF.budget_nonneg _) (norm_nonneg _))
    (fun y p hp r hr => le_refl _) (fun y p hp r hr => le_refl _)
    (fun p => B p.length) (fun p => B (p.length + 1) * ‖(basisVec i : Vec d)‖)
    (fun p _ => hB _) (fun p _ => mul_nonneg (hB _) (norm_nonneg _))
    (fun y p hp t a b => general_metric_word_entry_bound hr B hbG p.length (by omega) _ (coordinateWordDirections_norm p) y.1 t a b)
    (fun y p _ a b => general_metric_word_entry_measurable hr hm p.length _ y.1 a b)
    (fun y p hp t a b => general_metric_word_quotient_entry_bound hr B hbG p.length (by omega) _
      (coordinateWordDirections_norm p) y.1 (basisVec i) y.2.val y.2.property t a b)
    (fun y p _ a b => ((general_metric_word_entry_measurable hr hm p.length _ (Y1 y) a b).sub
      (general_metric_word_entry_measurable hr hm p.length _ y.1 a b)).const_mul _)
    hcar (fun y p hp => hi y.1 p hp) (fun y p hp => hi (Y1 y) p hp) w hw K hK
  exact ⟨R, hR, fun Y h hh => hq (Y, ⟨h, hh⟩)⟩

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Native positive metrics and the genuine pulse combine with local incoming edge models. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift
variable {ι : Type*} {Dm : ℕ}

theorem native_local_primitive_source_model (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (m : ℕ) (hν : 0 < D.kap m) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a ≤ b) (H : ℕ) (Y₀ : Vec 2)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (edge' : ConstituentEdges Dm (fun _ : ι => ℝ))
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t
      (familyLiftData D m slot A ρ edge).edge edge')
    (Qedge : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
      JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) :
    ∃ (Q' : LiftOperatorData ι (fun _ => ℝ) Dm) (U : Set (Vec 2)),
      IsOpen U ∧ Y₀ ∈ U ∧
      (familyLiftData D m slot A ρ edge).η = Q'.η ∧
      (familyLiftData D m slot A ρ edge).v = Q'.v ∧
      (∀ t ∈ Icc a b, ∀ Y ∈ U, (familyLiftData D m slot A ρ edge).G t Y = Q'.G t Y) ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq U t
        (familyLiftData D m slot A ρ edge).edge Q'.edge) ∧
      Nonempty (∀ i j, JointSourceReserve H (fun t _ Y => Q'.G t Y i j)) ∧
      Nonempty (∀ i, JointSourceReserve H (fun t z _ => Q'.v t z i)) ∧
      Nonempty (∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) ∧
      ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0 := by
  obtain ⟨G, W, hW, hYW, ⟨QG⟩, hG⟩ :=
    native_local_metric_joint_reserve D hζ m slot A hl ρ edge a b hab H Y₀
  let Q' : LiftOperatorData ι (fun _ => ℝ) Dm :=
    { familyLiftData D m slot A ρ edge with G := G, edge := edge' }
  refine ⟨Q', W ∩ V, hW.inter hV, ⟨hYW, hYV⟩, rfl, rfl,
    (fun t ht Y hY => (hG t ht Y hY.1).symm),
    (fun t ht => (he t ht).mono (fun _ hY => hY.2)), ⟨QG⟩, ?_, ⟨Qedge⟩, ?_⟩
  · refine ⟨fun i => (pulseJointSourceReserve H hΛ hν hζ hslot).map
      (ContinuousLinearMap.proj i)⟩
  · exact normalizedPulseDrift_mean_zero hΛ hν hslot
end

/-! Integer changes of stored child phases preserve native geometry and admissibility. -/

section
open Homogenization AVenhance AVRegularity.EntryWeakProofs

structure WeakChainPhaseLatticeEquivalent (A B : RealChain) : Prop where
  baseLevel_eq : A.baseLevel = B.baseLevel
  slots_eq : A.slots = B.slots
  base_eq : A.base = B.base
  children_rel : List.Forall₂ childPhaseLatticeEquivalent A.children B.children

theorem childPhaseLatticeEquivalent_symm {c d : ChainChild}
    (h : childPhaseLatticeEquivalent c d) : childPhaseLatticeEquivalent d c := by
  obtain ⟨hc, n, hn⟩ := h
  refine ⟨hc.symm, -n, ?_⟩
  have hneg : latticeShift (-n) = -latticeShift n := by
    funext i
    change (((-n i) : ℤ) : ℝ) = -((n i : ℤ) : ℝ)
    exact Int.cast_neg _
  rw [hn, hneg]
  abel

namespace WeakChainPhaseLatticeEquivalent
variable {A B : RealChain}

theorem refl (A : RealChain) : WeakChainPhaseLatticeEquivalent A A := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  induction A.children with
  | nil => exact .nil
  | cons c cs ih => exact .cons (childPhaseLatticeEquivalent_refl c) ih

theorem symm (h : WeakChainPhaseLatticeEquivalent A B) : WeakChainPhaseLatticeEquivalent B A := by
  refine ⟨h.baseLevel_eq.symm, h.slots_eq.symm, h.base_eq.symm, ?_⟩
  exact (h.children_rel.imp (fun _ _ hc => childPhaseLatticeEquivalent_symm hc)).flip

theorem children_length (h : WeakChainPhaseLatticeEquivalent A B) :
    A.children.length = B.children.length := h.children_rel.length_eq

theorem ctxLevel (h : WeakChainPhaseLatticeEquivalent A B) : A.ctxLevel = B.ctxLevel := by
  simp only [RealChain.ctxLevel, RealChain.lastLevel, h.baseLevel_eq, h.children_length]

theorem slot (h : WeakChainPhaseLatticeEquivalent A B) : A.slot = B.slot := by
  simp only [RealChain.slot, h.slots_eq]

theorem wellSlotted (h : WeakChainPhaseLatticeEquivalent A B) (hA : A.WellSlotted) : B.WellSlotted := by
  change B.slots.length = B.children.length + 1
  rw [← h.slots_eq, ← h.children_length]
  exact hA

theorem geom (h : WeakChainPhaseLatticeEquivalent A B) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hp : ∀ p ∈ B.slots, Odd p) : A.geom D = B.geom D :=
  realChain_geom_eq_of_phase_lattice D hΛ A B h.baseLevel_eq h.slots_eq h.base_eq hp h.children_rel

theorem admissible (h : WeakChainPhaseLatticeEquivalent A B) (D : OCData)
    (bw : ℝ) (j₀ level : ℕ) (slot : ℤ) (hA : IsAdmissibleChain D bw j₀ level slot A) :
    IsAdmissibleChain D bw j₀ level slot B := by
  obtain ⟨hctx, hbase, hlen, hslot, hodd, hsched, hchild⟩ := hA
  refine ⟨h.ctxLevel.symm.trans hctx, ?_, h.wellSlotted hlen, h.slot.symm.trans hslot, ?_, ?_, ?_⟩
  · rw [← h.baseLevel_eq]
    exact hbase
  · intro p hp
    exact hodd p (by rw [h.slots_eq]; exact hp)
  · intro k hk
    have hkA : k + 1 < A.slots.length := by rw [h.slots_eq]; exact hk
    have he := hsched k hkA
    simpa only [h.baseLevel_eq, h.slots_eq] using he
  · intro k hk
    have hkA : k < A.children.length := by rw [h.children_length]; exact hk
    have hc : A.children[k].center = B.children[k].center := by
      simpa only [List.get_eq_getElem] using (h.children_rel.get hkA hk).1
    have hb := hchild k hkA
    simpa only [hc, h.baseLevel_eq] using hb

theorem admissible_iff (h : WeakChainPhaseLatticeEquivalent A B) (D : OCData)
    (bw : ℝ) (j₀ level : ℕ) (slot : ℤ) :
    IsAdmissibleChain D bw j₀ level slot A ↔ IsAdmissibleChain D bw j₀ level slot B :=
  ⟨h.admissible D bw j₀ level slot, h.symm.admissible D bw j₀ level slot⟩

end WeakChainPhaseLatticeEquivalent
end

/-! An integer shift of the final phase changes only the phase class of the appended child. -/

section
open Homogenization AVenhance AVRegularity.EntryWeakProofs

theorem weak_appendChild_phase_lattice (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (hslot : Odd A.slot) (slot : ℤ) (t : ℝ) (z : Vec 2) (n : Fin 2 → ℤ) :
    WeakChainPhaseLatticeEquivalent (A.appendChild D slot t (z + latticeShift n))
      (A.appendChild D slot t z) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change List.Forall₂ childPhaseLatticeEquivalent (A.children ++ _) (A.children ++ _)
  apply List.rel_append (WeakChainPhaseLatticeEquivalent.refl A).children_rel
  refine .cons ?_ .nil
  have hd := weak_relative_displacement_periodic D hΛ A.ctxLevel A.slot hslot
    (D.slotAnchor (A.ctxLevel + 1) slot) t n z
  refine ⟨?_, n, ?_⟩
  · dsimp only
    rw [hd]
  · dsimp only
    rw [hd]
    exact add_right_comm z (latticeShift n)
      (D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t z)
end

/-! Integer phase equivalence descends to the parent and splits into its last child and preceding history. -/

section
open Homogenization AVRegularity.EntryWeakProofs

namespace WeakChainPhaseLatticeEquivalent
variable {A B : RealChain}

theorem dropLastChild (h : WeakChainPhaseLatticeEquivalent A B) :
    WeakChainPhaseLatticeEquivalent A.dropLastChild B.dropLastChild := by
  refine ⟨h.baseLevel_eq, congrArg List.dropLast h.slots_eq, h.base_eq, ?_⟩
  change List.Forall₂ childPhaseLatticeEquivalent A.children.dropLast B.children.dropLast
  rw [List.dropLast_eq_take, List.dropLast_eq_take, ← h.children_length]
  exact List.forall₂_take _ h.children_rel

theorem snoc_relation (h : WeakChainPhaseLatticeEquivalent A B)
    (cs ds : List ChainChild) (c d : ChainChild)
    (hA : A.children = cs ++ [c]) (hB : B.children = ds ++ [d]) :
    List.Forall₂ childPhaseLatticeEquivalent cs ds ∧ childPhaseLatticeEquivalent c d := by
  have hr := List.rel_reverse h.children_rel
  rw [hA, hB] at hr
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
  cases hr with
  | cons hc ht =>
    refine ⟨?_, hc⟩
    simpa only [List.reverse_reverse] using List.rel_reverse ht

end WeakChainPhaseLatticeEquivalent
end

/-! Recentering preserves integer phase equivalence, hence the full admissible slow carrier. -/

section
open Homogenization AVenhance AVRegularity.EntryWeakProofs

namespace WeakChainPhaseLatticeEquivalent
variable {A B : RealChain}

theorem recenter (h : WeakChainPhaseLatticeEquivalent A B) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hp : ∀ p ∈ B.slots, Odd p) (x : Vec 2) :
    WeakChainPhaseLatticeEquivalent (A.recenter D x) (B.recenter D x) := by
  rcases List.eq_nil_or_concat A.children with hA | ⟨cs, c, hA⟩
  · have hB : B.children = [] := by
      have hl := h.children_length
      rw [hA, List.length_nil] at hl
      exact List.length_eq_zero_iff.mp hl.symm
    rw [Providers.GenSem.recenter_nil D A hA, Providers.GenSem.recenter_nil D B hB]
    refine ⟨h.baseLevel_eq, h.slots_eq, congrArg (fun v : Vec 2 => v + x) h.base_eq, ?_⟩
    change List.Forall₂ childPhaseLatticeEquivalent A.children B.children
    rw [hA, hB]
    exact .nil
  · rw [List.concat_eq_append] at hA
    have hB : ∃ ds d, B.children = ds ++ [d] := by
      rcases List.eq_nil_or_concat B.children with hb | ⟨ds, d, hb⟩
      · have hl := h.children_length
        rw [hA, hb, List.length_append, List.length_singleton, List.length_nil] at hl
        omega
      · exact ⟨ds, d, by simpa only [List.concat_eq_append] using hb⟩
    obtain ⟨ds, d, hB⟩ := hB
    obtain ⟨hprefix, hlast⟩ := h.snoc_relation cs ds c d hA hB
    have hll : A.lastLevel = B.lastLevel := by
      simp only [RealChain.lastLevel, h.baseLevel_eq, h.children_length]
    have hg := h.dropLastChild.geom D hΛ (fun p hmem => hp p (List.mem_of_mem_dropLast hmem))
    have hR : Providers.GenSem.recenterShift D A c x = Providers.GenSem.recenterShift D B d x := by
      dsimp only [Providers.GenSem.recenterShift]
      rw [hg, hll, h.slot, hlast.1]
    rw [Providers.GenSem.recenter_snoc D A cs c hA x, Providers.GenSem.recenter_snoc D B ds d hB x]
    refine ⟨h.baseLevel_eq, h.slots_eq, h.base_eq, ?_⟩
    apply List.rel_append hprefix
    refine .cons ?_ .nil
    refine ⟨?_, ?_⟩
    · rw [hR, hlast.1]
    · obtain ⟨_, n, hn⟩ := hlast
      refine ⟨n, ?_⟩
      rw [hn, hR, hll]
      exact add_right_comm d.phase (latticeShift n)
        ((D.eps B.lastLevel)⁻¹ • Providers.GenSem.recenterShift D B d x)

theorem ladderOmega (h : WeakChainPhaseLatticeEquivalent A B) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hp : ∀ p ∈ B.slots, Odd p) (bw : ℝ) (j₀ level : ℕ) (slot : ℤ) (ρ : ℝ) :
    AVRegularity.ladderOmega D bw j₀ level slot A ρ = AVRegularity.ladderOmega D bw j₀ level slot B ρ := by
  ext X
  exact (h.recenter D hΛ hp (ρ • X)).admissible_iff D bw j₀ level slot

end WeakChainPhaseLatticeEquivalent
end

/-! The degree-one means vanish from centered drift and genuine regular edges. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVenhance.Infra.Torus
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem weakLiftMean_first_diagonal_zero
    (Q : LiftOperatorData ι h D) (t : ℝ)
    (hv : Continuous (Q.v t))
    (hm : ∀ k, (∫ z in AVenhance.unitCube, Q.v t z k) = 0)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : Vec 2 → ∀ i, h i) (X : Vec 2)
    (he : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y) :
    liftMean Q Cc (fun _ => f) 0 1 t X = 0 := by
  have hb := fieldCellMean_cellB1_independent Q.η Q.G Q.v t hv hm f X
  simpa [liftMean, liftA, he] using hb

theorem weakLiftMean_first_positive_zero
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth D D (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hh : ℕ) (hhpos : 1 ≤ hh) (X : Vec 2)
    (hinit : ∀ h₀, liftApply 0 (Cc h₀ 0) (fun _ => f) t =
      fun Y _ => if h₀ = 0 then f Y else 0)
    (hPhi : ContDiff ℝ (D : ℕ∞)
      (liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t X))
    (hper : AVenhance.IsZ2Periodic
      (liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t X)) :
    liftMean Q Cc (fun _ => f) hh 1 t X = 0 := by
  let Φ := liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t
  let Ψ := liftApply 0 (Cc (hh - 1) 0) (fun _ => f) t
  have hc := fun v u d γ hγ α => (hΓ v u d γ hγ α).1 X
  have hfast : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X,
      ContDiff ℝ 1 (γ.coeff α t X) := fun v u d γ hγ α X =>
    ((hΓ v u d γ hγ α).1 X).of_le (by exact_mod_cast hD)
  have hslow : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    (boxSmooth_slow_contDiff (hΓ v u d γ hγ α) z).of_le (by exact_mod_cast hD)
  have hm0 := fieldCellMean_sourceCoeff_zero Q.edge Q.η t Φ X hPhi hper hc
  have hi0 := Calculus.continuous_integrableOn_unitCell
    (sourceCoeff_zero_continuous Q.edge Q.η t Φ X hPhi hc)
  have hepos : liftApply 0 (Cc hh 0) (fun _ => f) t = 0 := by
    simpa only [ite_eq_right (by omega : hh ≠ 0)] using! hinit hh
  have hB1 : cellB1 Q.η Q.G Q.v t (liftApply 0 (Cc hh 0) (fun _ => f) t) = 0 := by
    rw [hepos]
    exact cellB1_zero_input Q.η Q.G Q.v t
  have heA : liftA Q Cc (fun _ => f) hh 1 t = fun X z =>
      -(sourceCoeff Q.edge Q.η 0 t Φ X z + sourceCoeff Q.edge Q.η 1 t Ψ X z) := by
    have hD : min D 1 = 1 := Nat.min_eq_right hD
    funext Y z
    simp [liftA, hB1, show hh ≠ 0 by omega, hD, Finset.sum_range_succ, Φ, Ψ]
  have hΨ : Ψ = if hh = 1 then (fun (X : Vec 2) (_ : Vec 2) => f X) else 0 := by
    dsimp only [Ψ]
    rw [hinit (hh - 1)]
    by_cases h1 : hh = 1
    · subst hh
      simp
    · simp only [ite_eq_right h1, ite_eq_right (by omega : hh - 1 ≠ 0)]
      rfl
  have hm1 : fieldCellMean (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact fieldCellMean_sourceCoeff_one_independent Q.edge Q.η t f (hf.of_le (by simp)) hfast hslow X
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input, fieldCellMean]
  have hi1 : IntegrableOn (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) (unitCell 2) := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact Calculus.continuous_integrableOn_unitCell
        (sourceCoeff_one_independent_continuous Q.edge Q.η t f (hf.of_le (by simp))
          hfast hslow X)
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input]
  have hm0' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 0 t Φ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm0
  have hm1' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm1
  simp only [liftMean, heA, fieldCellMean, ← integral_unitCell_eq_unitCube,
    integral_neg, integral_add hi0 hi1, hm0', hm1', add_zero, neg_zero]
end

end AVRegularity.WeakEntryProofs
end
