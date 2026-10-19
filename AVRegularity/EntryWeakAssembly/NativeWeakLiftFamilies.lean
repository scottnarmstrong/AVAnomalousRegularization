-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.NativeFullLiftRankCentering
public import AVRegularity.EntryWeakAssembly.ReadoutLinearLevel
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
public import AVRegularity.EntryWeakAssembly.WindowListL2Representative
import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
public import AVRegularity.EntryWeakAssembly.FirstMeanZero
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
/-! Each genuine native response retains precisely the data needed at later full-cell ranks. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ContDiff

structure LocalFullLiftRankProperties (R : ℕ) (a b : ℝ) (Ω : Set (Vec 2))
    (c : Vec 2 → ℝ → Vec 2 → ℝ) : Prop where
  initial_zero : ∀ Y ∈ Ω, ∀ z, c Y a z = 0
  mean_zero : ∀ Y ∈ Ω, ∀ t, (∫ z in AVenhance.unitCube, c Y t z) = 0
  regular : ∀ q, q ≤ R → ∀ t ∈ Icc a b,
    ContDiffOn ℝ (q : ℕ∞) (fun X : Vec 2 × Vec 2 => c X.1 t X.2) {X | X.1 ∈ Ω}
  local_reserve : ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (c' : Vec 2 → ℝ → Vec 2 → ℝ),
    IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (IndependentParameterSourceReserve R
      (independentTimeWindowSource (Ioc a b) (fun t z Y => c' Y t z))) ∧
    ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, c' Y t z = c Y t z

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm H : ℕ}

theorem native_full_lift_rank_production_step (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (R K : ℕ) (hrR : r ≤ R) (hH : R + (K + R) + 1 ≤ H)
    (hR : R + 2 ≤ H) (hK : R + 4 ≤ K)
    (N hh n m : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : ι) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hsource : let Q := familyLiftData D level slot A ρ edge
      let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
      let Cc := weakLiftInverseCoefficients Q inv N
      ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
        IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H g') ∧
        (∀ t Y, ∫ z in AVenhance.unitCube, g' t z Y = 0) ∧
        ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
          g' t z Y = weakLiftCoefficientForcing Q Cc hh n m α v u t z Y) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    let Cc := weakLiftInverseCoefficients Q inv N
    LocalFullLiftRankProperties R a b Ω (fun Y t z => Cc hh n m α t Y z v u 1) := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv N
  obtain ⟨hc, hj, hloc⟩ := native_full_lift_rank_response D hζ hΛ level hν slot hslot A hl
    ρ edge a b hab r hr R K hrR hH hR hK N hh n m hn hnN hm α v u Ω hΩ hsource
  have hcenter Y (hY : Y ∈ Ω) := native_full_lift_rank_centering D hζ level slot hslot A
    ρ edge r hr a b hab.le N hh n m hn hnN hm α Y v u
    ⟨_, cellFieldInverse_order_mono _ _ R r hrR a b 0 _ _ (hc Y hY)⟩
  refine ⟨fun Y hY => (hcenter Y hY).1, ?_, hj, hloc⟩
  intro Y hY t
  have hm := (hcenter Y hY).2.1 t 1
  exact hm

end AVRegularity.WeakEntryProofs
end
end

section
/-! Produced positive rank properties supply every predecessor premise of the literal full-cell identities. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*}

structure LocalFullLiftPredecessorData (S : ℕ) (a b : ℝ) (Ω : Set (Vec 2)) (Y₀ : Vec 2)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (N hh n : ℕ) : Prop where
  initial_zero : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
    ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
      ∀ z, Cc p q m α a Y z v u 1 = 0
  local_reserve : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
    ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
      ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
        IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve S
          (independentTimeWindowSource (Ioc a b) f')) ∧
        ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, f' t z Y = Cc p q m α t Y z v u 1
  mean_zero : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
    ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
      fieldCellMean (fun z => Cc p q l β t Y z v u ξ) = 0

theorem localFullLiftPredecessors_of_rank_properties
    (S : ℕ) (a b : ℝ) (Ω : Set (Vec 2)) (Y₀ : Vec 2) (hY : Y₀ ∈ Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (N hh n : ℕ)
    (R : ℕ → ℕ → ℕ)
    (hR : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N → S ≤ R p q)
    (hp : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        LocalFullLiftRankProperties (R p q) a b Ω (fun Y t z => Cc p q m α t Y z v u 1))
    (hzero : ∀ p, p ≠ 0 → Cc p 0 = 0) (hcut : ∀ p q, N < q → Cc p q = 0) :
    LocalFullLiftPredecessorData S a b Ω Y₀ Cc N hh n := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q hpq hq hqN m hm α v u Y hY z
    exact (hp p q hpq hq hqN m hm α v u).initial_zero Y hY z
  · intro p q hpq hq hqN m hm α v u
    obtain ⟨U, c', hU, hYU, _hUΩ, ⟨Qc⟩, he⟩ :=
      (hp p q hpq hq hqN m hm α v u).local_reserve Y₀ hY
    exact ⟨U, (fun t z Y => c' Y t z), hU, hYU,
      ⟨Qc.restrictOrder S (hR p q hpq hq hqN)⟩, he⟩
  · intro p q hpq hne l hl β t _ht Y hY v u ξ
    by_cases hq0 : q = 0
    · subst q
      have hz : (fun z => Cc p 0 l β t Y z v u ξ) = 0 := by
        funext z
        rw [hzero p (by omega)]
        rfl
      rw [hz]
      exact fieldCellMean_zero
    · by_cases hqN : q ≤ N
      · have hs : (fun z => Cc p q l β t Y z v u ξ) =
            fun z => ξ • Cc p q l β t Y z v u 1 := by
          funext z
          simpa only [smul_eq_mul, mul_one] using (Cc p q l β t Y z v u).map_smul ξ (1 : ℝ)
        rw [hs, fieldCellMean_smul]
        have hm := (hp p q hpq (by omega) hqN l hl β v u).mean_zero Y hY t
        change ξ • (∫ z in AVenhance.unitCube, Cc p q l β t Y z v u 1) = 0
        rw [hm, smul_zero]
      · have hz : (fun z => Cc p q l β t Y z v u ξ) = 0 := by
          funext z
          rw [hcut p q (by omega)]
          rfl
        rw [hz]
        exact fieldCellMean_zero

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual native full inverse solves the finite coefficient action of the cell source. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_finite_cell_equation (D : OCData) (hζ : IsFastProfile D.ζ)
    (level : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Y : Vec 2) (v : ι)
    (hsource : let Q := familyLiftData D level slot A ρ edge
      let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
        nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
      let Cc := weakLiftInverseCoefficients Q inv N
      ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
        ∃ c, IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v r a b 0
          (fun t z => weakLiftCoefficientForcing Q Cc hh n m α v u t z Y) c) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
    let Cc := weakLiftInverseCoefficients Q inv N
    IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v r a b 0
      (fun t z => leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f Y z)
      (fun t z => liftApply n (Cc hh n) (fun _ => f) t Y z v) := by
  let Q := familyLiftData D level slot A ρ edge
  let R := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
  let Cc := weakLiftInverseCoefficients Q (fun Y => R Y) N
  have hsolv := fullCellFiniteSource_mem_windowSolvableForcing (fun t => Matrix.of (Q.G t Y))
    Q.v r hr a b hab Q Cc hh n hn f hf Y v hsource
  have hc := nativeWindowResponseLinear_isInverse D hζ level slot hslot A ρ edge r hr
    a b hab Y (fun t z => leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f Y z) hsolv
  convert hc using 1
  funext t z
  exact weakLiftInverseCoefficients_finite_action Q R N hh n hn hnN f hf t Y z v

end AVRegularity.WeakEntryProofs
end
end

section
/-! Local mixed reserves give the actual interior box regularity and periodicity, including initial time. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open scoped ContDiff

theorem LocalFullLiftRankProperties.periodic_on_window {R : ℕ} {a b : ℝ} {Ω : Set (Vec 2)}
    {c : Vec 2 → ℝ → Vec 2 → ℝ} (P : LocalFullLiftRankProperties R a b Ω c)
    (Y : Vec 2) (hY : Y ∈ Ω) (t : ℝ) (ht : t ∈ Icc a b) :
    AVenhance.IsZ2Periodic (c Y t) := by
  by_cases ha : t = a
  · subst t
    intro k z
    rw [P.initial_zero Y hY, P.initial_zero Y hY]
  · obtain ⟨U, c', _hU, hYU, _hUΩ, ⟨Q⟩, he⟩ := P.local_reserve Y hY
    have ht' : t ∈ Ioc a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ha), ht.2⟩
    have hp := Q.periodic t Y
    simp only [independentTimeWindowSource, ite_eq_left ht'] at hp
    intro k z
    rw [← he t ht Y hYU, ← he t ht Y hYU]
    exact hp k z

end AVRegularity.WeakEntryProofs
end
end

section
/-! Actual scalar rank reserves control the map-valued coefficients used by the lift relation. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open scoped ContDiff

theorem LocalFullLiftRankProperties.map_boxSmoothOn {R : ℕ} {a b : ℝ} {Ω : Set (Vec 2)}
    (hΩ : IsOpen Ω) (c : Vec 2 → ℝ → Vec 2 → ℝ →L[ℝ] ℝ)
    (P : LocalFullLiftRankProperties R a b Ω (fun Y t z => c Y t z 1))
    (sX sZ : ℕ) (hs : sX + sZ ≤ R) (t : ℝ) (ht : t ∈ Icc a b) :
    IsBoxSmoothOn Ω sX sZ (fun Y z => c Y t z) := by
  have hscale Y s z : c Y s z = c Y s z 1 • ContinuousLinearMap.id ℝ ℝ := by
    apply DFunLike.ext
    intro ξ
    simpa only [smul_eq_mul, mul_one, smul_apply, ContinuousLinearMap.id_apply, mul_comm] using
      (c Y s z).map_smul ξ (1 : ℝ)
  by_cases ha : t = a
  · subst t
    apply boxSmoothOn_congr hΩ sX sZ
      (boxSmoothOn_of_boxSmooth Ω sX sZ (fun _ _ => (0 : ℝ →L[ℝ] ℝ))
        (Weighted.isBoxSmooth_of_joint_contDiff sX sZ _ contDiff_const))
    intro Y hY z
    change (0 : ℝ →L[ℝ] ℝ) = c Y a z
    rw [hscale]
    have hz : c Y a z 1 = 0 := P.initial_zero Y hY z
    rw [hz, zero_smul]
  · apply boxSmoothOn_of_local_boxes Ω sX sZ
    intro Y hY
    obtain ⟨U, c', hU, hYU, _hUΩ, ⟨Q⟩, he⟩ := P.local_reserve Y hY
    have ht' : t ∈ Ioc a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ha), ht.2⟩
    let f := fun Y z => independentTimeWindowSource (Ioc a b) (fun t z Y => c' Y t z) t z Y
      • ContinuousLinearMap.id ℝ ℝ
    have hf : ContDiff ℝ ((sX + sZ : ℕ) : ℕ∞) (fun X : Vec 2 × Vec 2 => f X.1 X.2) :=
      (((Q.regular t).of_le (by exact_mod_cast hs)).comp
        (contDiff_snd.prodMk contDiff_fst)).smul contDiff_const
    refine ⟨U, hU, hYU, ?_⟩
    apply boxSmoothOn_congr hU sX sZ
      (boxSmoothOn_of_boxSmooth U sX sZ f (Weighted.isBoxSmooth_of_joint_contDiff sX sZ f hf))
    intro X hX z
    dsimp only [f]
    rw [hscale X t z]
    simp only [independentTimeWindowSource, ite_eq_left ht', he t ht X hX z]

theorem LocalFullLiftRankProperties.map_periodic_on_window {R : ℕ} {a b : ℝ} {Ω : Set (Vec 2)}
    (c : Vec 2 → ℝ → Vec 2 → ℝ →L[ℝ] ℝ)
    (P : LocalFullLiftRankProperties R a b Ω (fun Y t z => c Y t z 1))
    (Y : Vec 2) (hY : Y ∈ Ω) (t : ℝ) (ht : t ∈ Icc a b) :
    AVenhance.IsZ2Periodic (c Y t) := by
  have hp := P.periodic_on_window Y hY t ht
  intro k z
  apply DFunLike.ext
  intro ξ
  have hs y : c Y t y ξ = ξ • c Y t y 1 := by
    simpa only [smul_eq_mul, mul_one] using (c Y t y).map_smul ξ (1 : ℝ)
  rw [hs, hs]
  exact congrArg (fun x : ℝ => ξ • x) (hp k z)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Genuine positive rank data and the actual cell equations assemble the carrier-local lift relation. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem weakLiftInverseCoefficients_carrier_sequence_assembly
    (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (N height sX r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (R : ℕ → ℕ → ℕ)
    (hR : ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N → sX + r ≤ R hh n)
    (P : ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      LocalFullLiftRankProperties (R hh n) a b Ω
        (fun Y t z => weakLiftInverseCoefficients Q inv N hh n m α t Y z v u 1))
    (hcell : let Cc := weakLiftInverseCoefficients Q inv N
      ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N →
        ∀ f : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ∀ Y ∈ Ω, ∀ v,
          IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v r a b 0
            (fun t z => liftCellSource Q Cc (fun _ => f) hh n t Y z v)
            (fun t z => liftApply n (Cc hh n) (fun _ => f) t Y z v)) :
    IsLiftSequenceOn Ω Q sX r a b N height
      (weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients Q inv N)) := by
  let Cc := weakLiftInverseCoefficients Q inv N
  have hbox hh (hhh : hh ≤ height) n m (α : DerivativeWord2 m) v u t (ht : t ∈ Icc a b) :
      IsBoxSmoothOn Ω sX r (fun Y z => Cc hh n m α t Y z v u) := by
    by_cases hn0 : n = 0
    · subst n
      have he : (fun Y z => Cc hh 0 m α t Y z v u) =
          fun _ _ => if hh = 0 ∧ m = 0 then blockIdentityEntry (fun _ : ι => ℝ) v u else 0 := by
        funext Y z
        exact weakLiftInverseCoefficients_zero_degree Q inv N hh m α t Y z v u
      rw [he]
      exact boxSmoothOn_of_boxSmooth Ω sX r _
        (Weighted.isBoxSmooth_of_joint_contDiff sX r _ contDiff_const)
    · by_cases hnN : n ≤ N
      · by_cases hm : m ≤ n
        · exact (P hh n hhh (by omega) hnN m hm α v u).map_boxSmoothOn hΩ
            (fun Y t z => Cc hh n m α t Y z v u) sX r (hR hh n hhh (by omega) hnN) t ht
        · have he : (fun Y z => Cc hh n m α t Y z v u) = 0 := by
            funext Y z
            exact weakLiftInverseCoefficients_above_order Q inv N hh n m (by omega) α t Y z v u
          rw [he]
          exact boxSmoothOn_of_boxSmooth Ω sX r _
            (Weighted.isBoxSmooth_of_joint_contDiff sX r _ contDiff_const)
      · have he : (fun Y z => Cc hh n m α t Y z v u) = 0 := by
          funext Y z
          change weakLiftInverseCoefficients Q inv N hh n m α t Y z v u = 0
          rw [weakLiftInverseCoefficients_cutoff Q inv N hh n (by omega)]
          rfl
        rw [he]
        exact boxSmoothOn_of_boxSmooth Ω sX r _
          (Weighted.isBoxSmooth_of_joint_contDiff sX r _ contDiff_const)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f _ t _ Y z
    have he : weakLiftCarrierRestriction Ω Cc 0 0 = Cc 0 0 := by
      funext m α t Y z v u
      simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inl rfl)]
    rw [he]
    exact weakLiftInverseCoefficients_identity Q inv N (fun _ => f) t Y z
  · intro hh hhh _ m α t Y z v u
    simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inl rfl)]
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N hh hhh m α t Y z v u
  · intro hh _ n hn m α t Y z v u
    unfold weakLiftCarrierRestriction
    split_ifs
    · change weakLiftInverseCoefficients Q inv N hh n m α t Y z v u = 0
      rw [weakLiftInverseCoefficients_cutoff Q inv N hh n hn]
      rfl
    · rfl
  · intro hh _ n m hm α t Y z v u
    unfold weakLiftCarrierRestriction
    split_ifs
    · exact weakLiftInverseCoefficients_above_order Q inv N hh n m hm α t Y z v u
    · rfl
  · intro hh _ n m α σ
    funext t Y z v u
    unfold weakLiftCarrierRestriction
    dsimp only [Cc]
    rw [weakLiftInverseCoefficients_perm Q inv N hh n m α σ]
  · intro hh hhh n m α v u t ht
    refine ⟨weakLiftCarrierRestriction_box Ω hΩ Cc hh n m α t v u sX r
      (hbox hh hhh n m α v u t ht), ?_⟩
    intro Y
    by_cases hn0 : n = 0
    · subst n
      intro k z
      simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inl rfl),
        weakLiftInverseCoefficients_zero_degree]
    · apply weakLiftCarrierRestriction_positive_periodic Ω Cc hh n m hn0 α t Y v u
      intro hY
      by_cases hnN : n ≤ N
      · by_cases hm : m ≤ n
        · exact (P hh n hhh (by omega) hnN m hm α v u).map_periodic_on_window
            (fun Y t z => Cc hh n m α t Y z v u) Y hY t ht
        · intro k z
          dsimp only [Cc]
          rw [weakLiftInverseCoefficients_above_order Q inv N hh n m (by omega),
            weakLiftInverseCoefficients_above_order Q inv N hh n m (by omega)]
      · intro k z
        dsimp only [Cc]
        rw [weakLiftInverseCoefficients_cutoff Q inv N hh n (by omega)]
        rfl
  · intro hh hhh n hn hnN f hf Y hY
    apply weakLiftCarrierRestriction_isInverse Ω hΩ Q Cc (fun _ => f) hh n r hn a b hab Y hY
    apply cellFieldInverse_dependent_pi _ _ r hr a b hab
    intro v
    exact hcell hh n hhh hn hnN f hf Y hY v

end AVRegularity.WeakEntryProofs
end
end

section
/-! Strict full-cell rank induction with local bounded models for arbitrary native histories. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_rank_induction (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (base N height : ℕ) (hDm : 1 ≤ Dm) (hbase : 2 * Dm + r + 4 ≤ base)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    let Cc := weakLiftInverseCoefficients Q inv N
    ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      LocalFullLiftRankProperties (weakLiftRankReserve Dm base N height hh n) a b Ω
        (fun Y t z => Cc hh n m α t Y z v u 1) := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv N
  suffices hall : ∀ rank hh n, ambientRecurrenceRank N hh n = rank →
      hh ≤ height → 1 ≤ n → n ≤ N → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      LocalFullLiftRankProperties (weakLiftRankReserve Dm base N height hh n) a b Ω
        (fun Y t z => Cc hh n m α t Y z v u 1) by
    exact fun hh n => hall _ hh n rfl
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
    intro hh n he hhh hn hnN m hm α v u
    let R := weakLiftRankReserve Dm base N height hh n
    have hRb : base + 1 ≤ R := weakLiftRankReserve_base Dm base N height hh n
    have hprior p q (hq : q ≤ N) (hpq : p < hh ∨ (p = hh ∧ q < n)) :
        ambientRecurrenceRank N p q < rank := by
      rw [← he]
      rcases hpq with hp | ⟨rfl, hq'⟩
      · exact ambientRecurrenceRank_height N hh n p q hp hq
      · unfold ambientRecurrenceRank
        omega
    have hph p q (hpq : p < hh ∨ (p = hh ∧ q < n)) : p ≤ height := by
      rcases hpq with hp | ⟨rfl, _⟩ <;> omega
    have prior p q (hpq : p < hh ∨ (p = hh ∧ q < n)) (hq : 1 ≤ q) (hqN : q ≤ N)
        l (hl : l ≤ q) (β : DerivativeWord2 l) (v u : ι) :=
      ih _ (hprior p q hqN hpq) p q rfl (hph p q hpq) hq hqN l hl β v u
    have hsource Y₀ (hY : Y₀ ∈ Ω) : ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
        IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (4 * R + 5) g') ∧
        (∀ t Y, ∫ z in AVenhance.unitCube, g' t z Y = 0) ∧
        ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
          g' t z Y = weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
      obtain ⟨V, edge', hV, hYV, heV, ⟨Qedge⟩⟩ := hedge ((4 * R + 5) + n + 1) Y₀ hY
      have hz p q hpq hq hqN l hl β v u Y hY z :=
        (prior p q hpq hq hqN l hl β v u).initial_zero Y hY z
      have hloc (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n))
          (hq : 1 ≤ q) (hqN : q ≤ N) (l : ℕ) (hl : l ≤ q) (β : DerivativeWord2 l) (v u : ι) :
          ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
            IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve
              ((4 * R + 5) + n + Dm + 2) (independentTimeWindowSource (Ioc a b) f')) ∧
            ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, f' t z Y = Cc p q l β t Y z v u 1 := by
        obtain ⟨U, c', hU, hYU, _hUΩ, ⟨Qc⟩, hc⟩ :=
          (prior p q hpq hq hqN l hl β v u).local_reserve Y₀ hY
        have hroom := weakLiftRankReserve_source_room Dm base N height hh n p q hhh hnN hqN hpq
        refine ⟨U, (fun t z Y => c' Y t z), hU, hYU, ⟨Qc.restrictOrder _ (by dsimp only [R]; omega)⟩, hc⟩
      have hmean p q (hpq : p < hh ∨ (p = hh ∧ q < n)) (hne : p ≠ 0 ∨ q ≠ 0)
          l (hl : l ≤ q) (β : DerivativeWord2 l) t (_ht : t ∈ Icc a b)
          Y (hY : Y ∈ Ω) v u ξ : fieldCellMean (fun z => Cc p q l β t Y z v u ξ) = 0 := by
        by_cases hq0 : q = 0
        · subst q
          have hp : 1 ≤ p := by omega
          have hz : (fun z => Cc p 0 l β t Y z v u ξ) = 0 := by
            funext z
            change weakLiftInverseCoefficients Q inv N p 0 l β t Y z v u ξ = 0
            rw [weakLiftInverseCoefficients_positive_grade_zero Q inv N p hp]
            rfl
          rw [hz]
          exact fieldCellMean_zero
        · by_cases hqN : q ≤ N
          · have hs : (fun z => Cc p q l β t Y z v u ξ) =
                fun z => ξ • Cc p q l β t Y z v u 1 := by
              funext z
              simpa only [smul_eq_mul, mul_one] using (Cc p q l β t Y z v u).map_smul ξ (1 : ℝ)
            rw [hs, fieldCellMean_smul]
            have hm := (prior p q hpq (by omega) hqN l hl β v u).mean_zero Y hY t
            change ξ • (∫ z in AVenhance.unitCube, Cc p q l β t Y z v u 1) = 0
            rw [hm, smul_zero]
          · have hz : (fun z => Cc p q l β t Y z v u ξ) = 0 := by
              funext z
              change weakLiftInverseCoefficients Q inv N p q l β t Y z v u ξ = 0
              rw [weakLiftInverseCoefficients_cutoff Q inv N p q (by omega)]
              rfl
            rw [hz]
            exact fieldCellMean_zero
      obtain ⟨U, g', hU, hYU, _hUΩ, hg, hgm, heq⟩ :=
        native_full_cell_source_local_reserve D hζ hΛ level hν slot hslot A hl ρ edge
          (4 * R + 5) (by omega) hDm a b hab.le Ω hΩ Y₀ hY inv N hh n hn hnN
          (by omega) V hV hYV edge' heV Qedge hz hloc hmean m hm α v u
      exact ⟨U, g', hU, hYU, hg, hgm, heq⟩
    exact native_full_lift_rank_production_step D hζ hΛ level hν slot hslot A hl ρ edge
      a b hab r hr R (R + 4) (by omega) (by omega) (by omega) (by omega)
      N hh n m hn hnN hm α v u Ω hΩ hsource

end AVRegularity.WeakEntryProofs
end
end

section
/-! Produced predecessor reserves certify each native coefficient as an actual cell inverse. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_rank_inverse (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (base N height : ℕ) (hDm : 1 ≤ Dm) (hbase : 8 * Dm + 8 * r + N + 40 ≤ base)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    let Cc := weakLiftInverseCoefficients Q inv N
    ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u Y,
      Y ∈ Ω → IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v r a b 0
        (fun t z => weakLiftCoefficientForcing Q Cc hh n m α v u t z Y)
        (fun t z => Cc hh n m α t Y z v u 1) := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv N
  have P := native_full_lift_rank_induction D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height hDm (by omega) Ω hΩ hedge
  dsimp only
  intro hh n hhh hn hnN m hm α v u Y hY
  have hzero p (hp : p ≠ 0) : Cc p 0 = 0 := by
    funext l β t X z v u
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N p (by omega) l β t X z v u
  have hsource Y₀ (hY₀ : Y₀ ∈ Ω) : ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (4 * r + 2 * Dm + 5) g') ∧
      (∀ t Y, ∫ z in AVenhance.unitCube, g' t z Y = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        g' t z Y = weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
    have Pd := localFullLiftPredecessors_of_rank_properties ((4 * r + 2 * Dm + 5) + n + Dm + 2)
      a b Ω Y₀ hY₀ Cc N hh n (weakLiftRankReserve Dm base N height)
      (fun p q _ _ _ => by have hb := weakLiftRankReserve_base Dm base N height p q; omega)
      (fun p q hpq hq hqN l hl β v u => P p q
        (by rcases hpq with hpq | ⟨rfl, _⟩ <;> omega) hq hqN l hl β v u)
      hzero (weakLiftInverseCoefficients_cutoff Q inv N)
    obtain ⟨V, edge', hV, hYV, he, ⟨Qe⟩⟩ := hedge ((4 * r + 2 * Dm + 5) + n + 1) Y₀ hY₀
    obtain ⟨U, g', hU, hYU, _hUΩ, hg, hgm, heq⟩ :=
      native_full_cell_source_local_reserve D hζ hΛ level hν slot hslot A hl ρ edge
        (4 * r + 2 * Dm + 5) (by omega) hDm a b hab.le Ω hΩ Y₀ hY₀ inv N hh n hn hnN
        (by omega) V hV hYV edge' he Qe Pd.initial_zero Pd.local_reserve Pd.mean_zero m hm α v u
    exact ⟨U, g', hU, hYU, hg, hgm, heq⟩
  exact (native_full_lift_rank_response D hζ hΛ level hν slot hslot A hl ρ edge a b hab
    r hr r (r + 4) le_rfl (by omega) (by omega) (by omega)
    N hh n m hn hnN hm α v u Ω hΩ hsource).1 Y hY

end AVRegularity.WeakEntryProofs
end
end

section
/-! Produced native ranks identify finite coefficient forcing with the literal full-cell source. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_finite_source_identity (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (base N height : ℕ) (hDm : 1 ≤ Dm) (hbase : 8 * Dm + 8 * r + N + 40 ≤ base)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    let Cc := weakLiftInverseCoefficients Q inv N
    ∀ hh n, hh ≤ height → 1 ≤ n → n ≤ N →
      ∀ f : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z v,
        leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f Y z =
          liftCellSource Q Cc (fun _ => f) hh n t Y z v := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv N
  have P := native_full_lift_rank_induction D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height hDm (by omega) Ω hΩ hedge
  dsimp only
  intro hh n hhh hn hnN f hf t ht Y hY z v
  let S := 2 * Dm + N + 4
  have hzero p (hp : p ≠ 0) : Cc p 0 = 0 := by
    funext l β t X z v u
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N p (by omega) l β t X z v u
  have Pd := localFullLiftPredecessors_of_rank_properties (S + Dm + 2)
    a b Ω Y hY Cc N hh n (weakLiftRankReserve Dm base N height)
    (fun p q _ _ _ => by have hb := weakLiftRankReserve_base Dm base N height p q; dsimp only [S]; omega)
    (fun p q hpq hq hqN l hl β v u => P p q
      (by rcases hpq with hpq | ⟨rfl, _⟩ <;> omega) hq hqN l hl β v u)
    hzero (weakLiftInverseCoefficients_cutoff Q inv N)
  obtain ⟨V, edge', hV, hYV, he, ⟨Qe⟩⟩ := hedge S Y hY
  exact native_full_cell_finite_source_action D hζ hΛ level hν slot hslot A hl ρ edge
    S hDm (by dsimp only [S]; omega) a b hab.le Ω hΩ Y hY inv N hh n hn hnN
    (by dsimp only [S]; omega) V hV hYV edge' he Qe
    Pd.initial_zero Pd.local_reserve Pd.mean_zero f hf t ht z v

end AVRegularity.WeakEntryProofs
end
end

section
/-! Genuine local incoming models produce the full native carrier-local lift sequence. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_sequence_on (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (base N height sX : ℕ) (hDm : 1 ≤ Dm) (hbase : 8 * Dm + 8 * r + N + sX + 40 ≤ base)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
      nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    IsLiftSequenceOn Ω Q sX r a b N height
      (weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients Q inv N)) := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv N
  have P := native_full_lift_rank_induction D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height hDm (by omega) Ω hΩ hedge
  have hinv := native_full_lift_rank_inverse D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height hDm (by omega) Ω hΩ hedge
  have hid := native_full_lift_finite_source_identity D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height hDm (by omega) Ω hΩ hedge
  apply weakLiftInverseCoefficients_carrier_sequence_assembly Q inv N height sX r hr a b hab.le Ω hΩ
    (weakLiftRankReserve Dm base N height)
    (fun hh n _ _ _ => by have hb := weakLiftRankReserve_base Dm base N height hh n; omega) P
  dsimp only
  intro hh n hhh hn hnN f hf Y hY v
  have hc := native_full_lift_finite_cell_equation D hζ level slot hslot A ρ edge r hr a b hab.le
    N hh n hn hnN f hf Y v
    (fun m hm α u => ⟨_, hinv hh n hhh hn hnN m hm α v u Y hY⟩)
  exact cellFieldInverse_source_congr_on _ _ r a b 0 _ _ _
    (fun t ht => funext (fun z => hid hh n hhh hn hnN f hf t ht Y hY z v)) hc

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Native carrier-pinned lifts are independent of the finite regularity orders used to produce them. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_order_coherence (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r r' : ℕ) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (base base' N height sX sX' : ℕ) (hDm : 1 ≤ Dm)
    (hbase : 8 * Dm + 8 * r + N + sX + 40 ≤ base)
    (hbase' : 8 * Dm + 8 * r' + N + sX' + 40 ≤ base')
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let Cc := weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients Q
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y) N)
    let Dc := weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients Q
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r' hr' a b hab.le Y) N)
    ∀ hh, hh ≤ height → ∀ n m (α : DerivativeWord2 m) t, t ∈ Icc a b → ∀ Y z v u,
      Cc hh n m α t Y z v u = Dc hh n m α t Y z v u := by
  have hc := native_full_lift_sequence_on D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr base N height sX hDm hbase Ω hΩ hedge
  have hd := native_full_lift_sequence_on D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r' hr' base' N height sX' hDm hbase' Ω hΩ hedge
  have he := native_family_lift_coefficients_unique D hζ level slot hslot A ρ edge Ω hΩ
    a b hab.le N height sX r sX' r' _ _ hc hd
  dsimp only
  intro hh hhh n m α t ht Y z v u
  by_cases hY : Y ∈ Ω
  · exact he hh hhh n m α t ht Y hY z v u
  · by_cases hn : n = 0
    · subst n
      simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inl rfl),
        weakLiftInverseCoefficients_zero_degree]
    · simp only [weakLiftCarrierRestriction, ite_eq_right (not_or.mpr ⟨hn, hY⟩)]

end AVRegularity.WeakEntryProofs
end
end

section
/-! The complete carrier-pinned native array is canonical across every finite regularity choice. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_array_order_coherence (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r r' : ℕ) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (N : ℕ) (hDm : 1 ≤ Dm)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y) N) =
    weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r' hr' a b hab.le Y) N) := by
  funext hh n m α t Y z v u
  by_cases ht : t ∈ Icc a b
  · exact native_full_lift_order_coherence D hζ hΛ level hν slot hslot A hl ρ edge a b hab
      r r' hr hr' (8 * Dm + 8 * r + N + 0 + 40) (8 * Dm + 8 * r' + N + 0 + 40)
      N hh 0 0 hDm le_rfl le_rfl Ω hΩ hedge hh le_rfl n m α t ht Y z v u
  · by_cases hn : n = 0
    · subst n
      simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inl rfl),
        weakLiftInverseCoefficients_zero_degree]
    · by_cases hY : Y ∈ Ω
      · simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inr hY)]
        rw [native_full_lift_coefficient_zero_off_window D hζ level slot hslot A ρ edge r hr
          a b hab.le N hh n m (by omega) α t ht Y z v u,
          native_full_lift_coefficient_zero_off_window D hζ level slot hslot A ρ edge r' hr'
          a b hab.le N hh n m (by omega) α t ht Y z v u]
      · simp only [weakLiftCarrierRestriction, ite_eq_right (not_or.mpr ⟨hn, hY⟩)]

end AVRegularity.WeakEntryProofs
end
end

section
/-! One canonical native lift array has every finite interior slow and fast regularity order. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_all_orders (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (N height : ℕ) (hDm : 1 ≤ Dm)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hedge : ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : ι => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t (familyLiftData D level slot A ρ edge).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))) :
    let Q := familyLiftData D level slot A ρ edge
    let Cc := weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients Q
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge 1 le_rfl a b hab.le Y) N)
    ∀ sX sZ, IsLiftSequenceOn Ω Q sX sZ a b N height Cc := by
  dsimp only
  intro sX sZ
  let r := max 1 sZ
  have hr : 1 ≤ r := le_max_left _ _
  have hZ : sZ ≤ r := le_max_right _ _
  have hc := native_full_lift_sequence_on D hζ hΛ level hν slot hslot A hl ρ edge a b hab
    r hr (8 * Dm + 8 * r + N + sX + 40) N height sX hDm le_rfl Ω hΩ hedge
  have he := native_full_lift_array_order_coherence D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab 1 r le_rfl hr N hDm Ω hΩ hedge
  rw [he]
  exact liftSequenceOn_order_mono Ω _ le_rfl hZ a b N height _ hc

end AVRegularity.WeakEntryProofs
end
end

section
/-! Eddy histories have canonical genuine full-cell lifts at every finite order, without a smallness premise. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_empty_full_lift_all_orders (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1) (ρ : ℝ)
    (a b : ℝ) (hab : a < b) (N : ℕ) (hDm : 1 ≤ Dm) :
    let edge : ConstituentEdges Dm (fun _ : ι => ℝ) := fun _ _ _ => []
    let Q := familyLiftData D level slot A ρ edge
    let Cc := weakLiftInverseCoefficients Q
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge 1 le_rfl a b hab.le Y) N
    ∀ sX sZ, IsLiftSequence Q sX sZ a b N 0 Cc := by
  let edge : ConstituentEdges Dm (fun _ : ι => ℝ) := fun _ _ _ => []
  let Q := familyLiftData D level slot A ρ edge
  have hEmpty : Q.edge = edge :=
    liftEdges_empty (D.cellScaleSq level) (ρ / D.eps (level - 1))
  have hc := native_full_lift_all_orders D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab N 0 hDm univ isOpen_univ (by
      intro H Y₀ _hY
      refine ⟨univ, edge, isOpen_univ, mem_univ Y₀, ?_, ?_⟩
      · intro t _ht
        change SlowOpenEdgeEq univ t Q.edge edge
        rw [hEmpty]
        intro v u d
        exact List.Forall₂.nil
      · refine ⟨fun v u d γ hγ _ => ?_⟩
        exact (List.not_mem_nil hγ).elim)
  dsimp only
  intro sX sZ
  have hs := liftSequence_of_on_univ Q sX sZ a b N 0 _ (hc sX sZ)
  have he (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) : weakLiftCarrierRestriction univ Cc = Cc := by
    funext hh n m α t Y z v u
    exact weakLiftCarrierRestriction_copy univ Cc hh n m α t Y (mem_univ Y) z v u
  rw [he] at hs
  exact hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! One canonical eddy lift array works for every finite slow and fast order. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open scoped Classical
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

def nativeWeakEddyLiftFamily (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ level : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (N : ℕ) :
    ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ) :=
  fun k A => if hA : IsAdmissibleChain D bw j₀ level k A ∧ Odd k then
    let edge : ConstituentEdges Dm (fun _ : Fin 1 => ℝ) := fun _ _ _ => []
    let ρ := D.eps (level - 1)
    let a := D.slotStart level k / D.cellScaleSq level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level
    weakLiftInverseCoefficients (familyLiftData D level k A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level k hA.2 A ρ edge 1 le_rfl a b
        (weakData_lift_window_strict D hΛ hζ hband level k).le Y) N
  else 0

theorem native_weak_eddy_lift_family (D : OCData) (Dm : ℕ) (hDm : 1 ≤ Dm)
    (bw : ℝ) (j₀ level : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (N sX sZ : ℕ)
    (k : ℤ) (A : RealChain) (hslot : Odd k)
    (hA : IsAdmissibleChain D bw j₀ level k A) :
    IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ)
      D level k A (D.eps (level - 1)) (fun _ _ _ => [])) sX sZ
      (D.slotStart level k / D.cellScaleSq level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level) N 0
      (nativeWeakEddyLiftFamily D Dm bw j₀ level hΛ hζ hband N k A) := by
  simp only [nativeWeakEddyLiftFamily, dite_eq_left (show _ ∧ Odd k from ⟨hA, hslot⟩)]
  exact native_empty_full_lift_all_orders D hζ hΛ level
    (weakData_kap_pos D hΛ hζ hband level) k hslot A hA.2.2.1
    (D.eps (level - 1)) _ _ (weakData_lift_window_strict D hΛ hζ hband level k)
    N hDm sX sZ

end AVRegularity.WeakEntryProofs
end
end

section
/-! Canonical native lifts preserve identical stored geometries and parallel child-phase shifts. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

theorem native_full_lift_geometry_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Dm : ℕ} (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A B : RealChain)
    (hA : A.WellSlotted) (hB : B.WellSlotted) (hg : A.geom D = B.geom D)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    weakLiftInverseCoefficients (familyLiftData D m slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y) N =
    weakLiftInverseCoefficients (familyLiftData D m slot B ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ m slot hslot B ρ edge r hr a b hab Y) N := by
  have hQ := familyLiftData_geometry_congr D m slot A B hA hB hg ρ edge
  have hI : (fun Y g => nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y g) =
      (fun Y g => nativeWindowResponseLinear D hζ m slot hslot B ρ edge r hr a b hab Y g) := by
    funext Y g
    exact congrArg (fun L : (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ) => L g)
      (nativeWindowResponseLinear_geometry_congr D hζ m slot hslot A B hA hB hg
        ρ edge r hr a b hab Y)
  rw [hQ, hI]

theorem native_weak_eddy_lift_family_geometry_congr (D : OCData) (Dm : ℕ)
    (bw : ℝ) (j₀ level : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (N : ℕ)
    (k : ℤ) (hslot : Odd k) (A B : RealChain)
    (hA : IsAdmissibleChain D bw j₀ level k A)
    (hB : IsAdmissibleChain D bw j₀ level k B) (hg : A.geom D = B.geom D) :
    nativeWeakEddyLiftFamily D Dm bw j₀ level hΛ hζ hband N k A =
      nativeWeakEddyLiftFamily D Dm bw j₀ level hΛ hζ hband N k B := by
  simp only [nativeWeakEddyLiftFamily, dite_eq_left (show _ ∧ Odd k from ⟨hA, hslot⟩),
    dite_eq_left (show _ ∧ Odd k from ⟨hB, hslot⟩)]
  exact native_full_lift_geometry_congr D hζ level k hslot A B hA.2.2.1 hB.2.2.1 hg
    (D.eps (level - 1)) (fun _ _ _ => []) 1 le_rfl _ _ _ N

end AVRegularity.WeakEntryProofs
end
end

section
/-! Eddy mean fluxes inherit the stored-geometry and parallel child-phase invariance of their lifts. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

theorem native_weak_eddy_mean_geometry_congr (D : OCData) (Dm : ℕ)
    (bw : ℝ) (j₀ level : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (N : ℕ)
    (k : ℤ) (hslot : Odd k) (A B : RealChain)
    (hA : IsAdmissibleChain D bw j₀ level k A)
    (hB : IsAdmissibleChain D bw j₀ level k B) (hg : A.geom D = B.geom D)
    (n : ℕ) (t : ℝ) :
    weakEddyFlux D level (D.eps (level - 1))
      (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D level k A
        (D.eps (level - 1)) (fun _ _ _ => []))
      (nativeWeakEddyLiftFamily D Dm bw j₀ level hΛ hζ hband N k A) n t =
    weakEddyFlux D level (D.eps (level - 1))
      (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D level k B
        (D.eps (level - 1)) (fun _ _ _ => []))
      (nativeWeakEddyLiftFamily D Dm bw j₀ level hΛ hζ hband N k B) n t := by
  rw [familyLiftData_geometry_congr D level k A B hA.2.2.1 hB.2.2.1 hg,
    native_weak_eddy_lift_family_geometry_congr D Dm bw j₀ level hΛ hζ hband N k hslot A B hA hB hg]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Eddy source operators preserve integer phase equivalence without any incoming passage. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem native_weak_eddy_source_phase_lattice (N : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (v : CompIn G.comps) (w : List WordLetter) (n : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (k : ℤ) (A B : RealChain) (hphase : WeakChainPhaseLatticeEquivalent A B) (t : ℝ) :
    (WeakSource.eddy v w n).fluxOp (D.eps (G.level - 1)) Cc
      (nativeWeakEddyLiftFamily D Dm bw j₀ G.level hΛ hζ hband N) k t A =
    (WeakSource.eddy v w n).fluxOp (D.eps (G.level - 1)) Cc
      (nativeWeakEddyLiftFamily D Dm bw j₀ G.level hΛ hζ hband N) k t B := by
  classical
  by_cases hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k
  · have hB : IsAdmissibleChain D bw j₀ G.level k B ∧ Odd k :=
      ⟨hphase.admissible D bw j₀ G.level k hA.1, hA.2⟩
    simp only [WeakSource.fluxOp, dite_eq_left hA, dite_eq_left hB]
    exact native_weak_eddy_mean_geometry_congr D Dm bw j₀ G.level hΛ hζ hband N k hA.2 A B
      hA.1 hB.1 (hphase.geom D hΛ hB.1.2.2.2.2.1) n t
  · have hB : ¬ (IsAdmissibleChain D bw j₀ G.level k B ∧ Odd k) := by
      rintro ⟨hB, hk⟩
      exact hA ⟨(hphase.admissible_iff D bw j₀ G.level k).mpr hB, hk⟩
    simp only [WeakSource.fluxOp, dite_eq_right hA, dite_eq_right hB]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Canonical native path arrays form the exact inherited weak lift family on every admissible history. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open scoped Classical
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀} {h : ℕ}

def nativeWeakPathLiftFamily (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (π : StagePath G' h) (N : ℕ) :
    ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ) :=
  fun k A => if hA : IsAdmissibleChain D bw j₀ G'.level k A ∧ Odd k then
    let edge := pathEdges G' π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let ρ := D.eps (G'.level - 1)
    let Ω := ladderOmega D bw j₀ G'.level k A ρ
    let a := D.slotStart G'.level k / D.cellScaleSq G'.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G'.level) / D.cellScaleSq G'.level
    weakLiftCarrierRestriction Ω (weakLiftInverseCoefficients (familyLiftData D G'.level k A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ G'.level k hA.2 A ρ edge 1 le_rfl a b
        (weakData_lift_window_strict D hΛ hζ hband G'.level k).le Y) N)
  else 0

end AVRegularity.WeakEntryProofs
end
end

section
/-! Simultaneous all-order lift witnesses for the actual weak sources of one passage. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

def nativeWeakSourceLiftFamily (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (N : ℕ) :
    (s : WeakSource G') → ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)
  | .inherited _ _ π _ => nativeWeakPathLiftFamily hΛ hζ hband π N
  | .eddy .. => fun _ _ => 0

end AVRegularity.WeakEntryProofs
end
end
end
