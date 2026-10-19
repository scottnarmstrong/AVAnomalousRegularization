-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.CycleComparison.Lift.CellB1LeftTerms
public import AVRegularity.EntryWeak.MolecularDualNormBounds
public import Mathlib.Algebra.Order.Star.Real

section
section
section
/-! Positive clock changes preserve the complete integrable cell weak identity. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.CycleEvolution Set

theorem cellWeakIdentity_comp_mul (C : CellCoefficients) (s t c : ℝ)
    (hc : 0 < c) (hst : s ≤ t)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C (c * s) (c * t) u0 u1 ψ dψ u du src F) :
    CellWeakIdentity (cellClockCoefficients C c) s t u0 u1 ψ dψ
      (fun r => u (c * r)) (fun r => du (c * r))
      (fun r => c • src (c * r)) (fun r => c • F (c * r)) := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS (cellClockCoefficients C c) r
    (u (c * r)) (du (c * r)) ψ dψ (c • src (c * r)) (c • F (c * r))
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc (c * s) (c * t)), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc (c * s) (c * t))) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc (c * s) (c * t), ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he (r : ℝ) : R' r = c • R (c * r) := by
    funext x
    exact cellLiteralRHS_clock C c r (u (c * r)) (du (c * r)) ψ dψ
      (src (c * r)) (F (c * r)) x
  have hint (r : ℝ) : (∫ x, R' r x ∂μ) = c • ∫ x, R (c * r) x ∂μ := by
    rw [he]
    exact integral_smul c (fun x => R (c * r) x)
  have hi := h.2.2.1
  rw [restrict_Ioc_eq_restrict_Icc] at hi
  have hi' := ae_window_comp_mul s t c hc hi
  rw [← restrict_Ioc_eq_restrict_Icc] at hi'
  have hm := h.2.2.2.1
  rw [restrict_Ioc_eq_restrict_Icc, ← memLp_one_iff_integrable] at hm
  have hm' := memLp_window_comp_mul s t c hc hm
  rw [memLp_one_iff_integrable, ← restrict_Ioc_eq_restrict_Icc] at hm'
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · filter_upwards [hi'] with r hr
    rw [he]
    exact hr.smul c
  · simp_rw [hint]
    exact hm'.smul c
  · rw [h.2.2.2.2]
    simp_rw [hint]
    rw [integral_smul, ← intervalIntegral.integral_of_le hst,
      intervalIntegral.smul_integral_comp_mul_left (fun r => ∫ x, R r x ∂μ) c,
      intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hst hc.le)]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Agreement of cell generators on the solving window preserves the complete weak solution. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter AVRegularity.CycleEvolution

theorem cellWeakIdentity_coefficients_congr_sections (C C' : CellCoefficients) (s t : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hθ : C.θ = C'.θ)
    (hG : ∀ᵐ r ∂volume.restrict (Ioc s t),
      (∀ x, C.G r x = C'.G r x) ∧ (∀ x, C.v r x = C'.v r x) ∧ C.κ r = C'.κ r)
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C' s t u0 u1 ψ dψ u du src F := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS C' r (u r) (du r) ψ dψ (src r) (F r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t), R r =ᵐ[μ] R' r := by
    filter_upwards [hG] with r hr
    exact Eventually.of_forall (fun x => by
      simp only [R, R', cellLiteralRHS, hr.1 x, hr.2.1 x, hθ, hr.2.2])
  have hint : (fun r => ∫ x, R r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => ∫ x, R' r x ∂μ := he.mono fun r hr => integral_congr_ae hr
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1.congr hint, ?_⟩
  · filter_upwards [h.2.2.1, he] with r hr her
    exact hr.congr her
  · exact h.2.2.2.2.trans (integral_congr_ae hint)

theorem cellSolution_coefficients_congr_on (I : Set ℝ) (C C' : CellCoefficients)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (hθ : C.θ = C'.θ)
    (hG : ∀ r ∈ I, (∀ x, C.G r x = C'.G r x) ∧
      (∀ x, C.v r x = C'.v r x) ∧ C.κ r = C'.κ r)
    (h : IsCellSolution I C src F D) : IsCellSolution I C' src F D := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  intro s hs t ht hst ψ
  have hsub : Ioc s t ⊆ I := fun r hr => h.1.out hs ht ⟨hr.1.le, hr.2⟩
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t),
      (∀ x, C.G r x = C'.G r x) ∧ (∀ x, C.v r x = C'.v r x) ∧ C.κ r = C'.κ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hG r (hsub hr)
  exact cellWeakIdentity_coefficients_congr_sections C C' s t _ _ _ _ _ _ src F hθ he
    (h.2.2.2.2.2.2 s hs t ht hst ψ)

end AVRegularity.WeakEntryProofs
end
end

section
/-! A positive clock change preserves the raw periodic energy solution. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology Set

theorem cellSolution_comp_mul (a b c : ℝ) (hc : 0 < c)
    (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc (c * a) (c * b)) C src F D) :
    IsCellSolution (Icc a b) (cellClockCoefficients C c)
      (fun t => c • src (c * t)) (fun t => c • F (c * t)) (fun t => D (c * t)) := by
  have hmaps : MapsTo (fun t : ℝ => c * t) (Icc a b) (Icc (c * a) (c * b)) := by
    intro t ht
    exact ⟨mul_le_mul_of_nonneg_left ht.1 hc.le, mul_le_mul_of_nonneg_left ht.2 hc.le⟩
  refine ⟨ordConnected_Icc, ae_window_comp_mul a b c hc h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact h.2.2.1 _ (hmaps ht)
  · intro k
    exact window_prod_comp_mul_aestronglyMeasurable (volume.restrict AVenhance.unitCube)
      a b c hc (fun p => D p.1 k p.2) (h.2.2.2.1 k)
  · intro t ht
    exact (h.2.2.2.2.1 _ (hmaps ht)).comp
      ((continuous_const.mul continuous_id).continuousWithinAt.tendsto_nhdsWithin hmaps)
  · intro s hs t ht
    exact lintegral_window_comp_mul_lt_top s t c hc
      (fun r => cellL2Norm (cellGradient (D r)) ^ 2)
      (h.2.2.2.2.2.1 _ (hmaps hs) _ (hmaps ht))
  · intro s hs t ht hst ψ
    have hid : CellWeakIdentity C (c * s) (c * t)
        (cellValue D (c * s)) (cellValue D (c * t)) (ψ.jet (valueIndex2 1))
        (fun k => ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) (cellValue D)
        (fun r k => cellGradComp (D r) k) src F :=
      h.2.2.2.2.2.2 _ (hmaps hs) _ (hmaps ht)
        (mul_le_mul_of_nonneg_left hst hc.le) ψ
    exact cellWeakIdentity_comp_mul C s t c hc hst
      (cellValue D (c * s)) (cellValue D (c * t)) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (cellValue D) (fun r k => cellGradComp (D r) k) src F hid

end AVRegularity.WeakEntryProofs
end
end

section
/-! Strong actual word derivatives and bounded higher quotients upgrade every reserved fast jet. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
variable {d : ℕ}

theorem higher_trace_word_classical_contDiff (N K : ℕ)
    (u : List (Fin d) → Vec d → ComplexCellL2)
    (w : List (Fin d) → Vec d → TorusHk K ℂ)
    (hw : ∀ p, p.length ≤ N → ∀ Y, torusHkValueCLM (w p Y) = u p Y)
    (hc : ∀ p, p.length ≤ N → Continuous (u p))
    (hd : ∀ p, p.length < N → ∀ Y i,
      Tendsto (fun h : ℝ => h⁻¹ • (u p (Y + h • basisVec i) - u p Y) - u (i :: p) Y)
        (𝓝[≠] 0) (𝓝 0))
    (R : List (Fin d) → ℝ) (hb : ∀ p, p.length ≤ N → ∀ Y, ‖w p Y‖ ≤ R p)
    (hq : ∀ p, p.length < N → ∀ i : Fin d, ∃ B : ℝ, ∀ Y (h : ℝ), h ≠ 0 →
      ∃ q : TorusHk K ℂ,
        torusHkValueCLM q = h⁻¹ • (u p (Y + h • basisVec i) - u p Y) ∧ ‖q‖ ≤ B) :
    ∀ p r, p.length + r ≤ N → ∀ n, n + 4 ≤ K → ∀ z : Vec 2,
      ContDiff ℝ (r : ℕ∞) (fun Y => iteratedFDeriv ℝ n
        (realClassicalLift K (mapTorusHk Complex.reCLM (w p Y))) z) := by
  intro p r hpr n hn z
  apply finite_coordinate_word_family_contDiff d N
    (fun p Y => iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w p Y))) z)
    _ _ p r hpr
  · intro p hp
    exact molecular_higher_trace_fast_jet_continuous K n hn (w p) (u p) (hc p hp)
      (hw p hp) (R p) (hb p hp) z
  · intro p hp i Y
    obtain ⟨B, hB⟩ := hq p hp i
    have hpi : (i :: p).length ≤ N := by simp only [List.length_cons]; omega
    apply molecular_higher_trace_jet_hasDerivAt K n hn
      (fun h => w p (Y + h • basisVec i)) (w (i :: p) Y)
      (fun h => u p (Y + h • basisVec i)) (u (i :: p) Y)
      (fun h => hw p (by omega) _) (hw (i :: p) hpi Y)
    · simpa only [zero_smul, add_zero] using hd p hp Y i
    · filter_upwards [self_mem_nhdsWithin] with h hh
      obtain ⟨q, hq, hqb⟩ := hB Y h hh
      have he : h⁻¹ • (w p (Y + h • basisVec i) - w p Y) = q := by
        apply TorusHk.ext_value
        change torusHkValueCLM (h⁻¹ • (w p (Y + h • basisVec i) - w p Y)) = torusHkValueCLM q
        rw [map_smul, map_sub, hw p (by omega), hw p (by omega)]
        exact hq.symm
      simpa only [zero_smul, add_zero, he] using hqb

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Positive coefficients may be pinned to zero off their carrier without changing any interior germ. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
open scoped Classical

def weakLiftCarrierRestriction (Ω : Set (Vec 2))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) : LiftCoeff ι h :=
  fun m α t X z v u => if n = 0 ∨ X ∈ Ω then Cc hh n m α t X z v u else 0

omit [Fintype ι] in
theorem weakLiftCarrierRestriction_copy (Ω : Set (Vec 2))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) (v u : ι) :
    weakLiftCarrierRestriction Ω Cc hh n m α t X z v u = Cc hh n m α t X z v u := by
  simp only [weakLiftCarrierRestriction, ite_eq_left (Or.inr hX)]

omit [Fintype ι] in
theorem weakLiftCarrierRestriction_box (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (v u : ι) (sX sZ : ℕ)
    (hc : IsBoxSmoothOn Ω sX sZ (fun X z => Cc hh n m α t X z v u)) :
    IsBoxSmoothOn Ω sX sZ
      (fun X z => weakLiftCarrierRestriction Ω Cc hh n m α t X z v u) := by
  apply boxSmoothOn_congr hΩ sX sZ hc
  intro X hX z
  exact (weakLiftCarrierRestriction_copy Ω Cc hh n m α t X hX z v u).symm

omit [Fintype ι] in
theorem weakLiftCarrierRestriction_positive_periodic (Ω : Set (Vec 2))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (hn : n ≠ 0)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι)
    (hp : X ∈ Ω → AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) :
    AVenhance.IsZ2Periodic
      (fun z => weakLiftCarrierRestriction Ω Cc hh n m α t X z v u) := by
  by_cases hX : X ∈ Ω
  · simpa only [weakLiftCarrierRestriction, ite_eq_left (Or.inr hX)] using hp hX
  · intro k z
    simp only [weakLiftCarrierRestriction, ite_eq_right (fun h : n = 0 ∨ X ∈ Ω => h.elim hn hX)]

theorem weakLiftCarrierRestriction_source (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) :
    liftCellSource Q (weakLiftCarrierRestriction Ω Cc) f hh n t X z =
      liftCellSource Q Cc f hh n t X z := by
  exact liftCellSource_slow_open_congr_predecessors hΩ Q
    (weakLiftCarrierRestriction Ω Cc) Cc f hh n hn t
    (fun p q _ m _ α Y hY z v u => weakLiftCarrierRestriction_copy Ω Cc p q m α t Y hY z v u)
    X hX z

theorem weakLiftCarrierRestriction_apply (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) :
    liftApply n (weakLiftCarrierRestriction Ω Cc hh n) f t X z =
      liftApply n (Cc hh n) f t X z := by
  exact liftApply_slow_open_congr hΩ n t (weakLiftCarrierRestriction Ω Cc hh n)
    (Cc hh n) f f
    (fun m _ α Y hY z v u => weakLiftCarrierRestriction_copy Ω Cc hh n m α t Y hY z v u)
    (fun _ _ => rfl) X hX z

end AVRegularity.WeakEntryProofs
end
end

section
/-! Genuine field inverses depend only on the metric on their solving window. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set

theorem cellFieldInverse_metric_congr_on {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G G' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ) (a b : ℝ) (c₀ : Vec 2 → E) (g u : ℝ → Vec 2 → E)
    (he : ∀ t ∈ Icc a b, G t = G' t)
    (h : IsCellFieldInverse G v r a b c₀ g u) :
    IsCellFieldInverse G' v r a b c₀ g u := by
  refine ⟨h.1, fun ℓ => ?_⟩
  obtain ⟨hs, hm, hi, hn⟩ := h.2 ℓ
  refine ⟨?_, hm, hi, hn⟩
  exact cellSolution_coefficients_congr_on (Icc a b)
    ⟨fun t _ => G t, v, 0, 0⟩ ⟨fun t _ => G' t, v, 0, 0⟩
    (fun t x => (ℓ (g t x) : ℂ)) (fun _ _ => 0) (cellJetOfField ℓ u) rfl
    (fun t ht => ⟨fun _ => he t ht, fun _ => rfl, rfl⟩) hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! The diagonal mean formulas require regular metric and drift fields, with no transverse setting. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem weakLiftMean_diagonal_second
    (Q : LiftOperatorData ι h D) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X : Vec 2)
    (hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hΦ : GoodField 2 (liftApply 1 (Cc 0 1) (fun _ => f) t)) :
    liftMean Q Cc (fun _ => f) 0 2 t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) • liftApply 1 (Cc 0 1) (fun _ => f) t Y z) -
          Q.η • ∑ j : Fin 2, Q.G t Y q j • fderiv ℝ f Y (basisVec j)) X (basisVec q) := by
  have he : liftMean Q Cc (fun _ => f) 0 2 t X =
      fieldCellMean (fun z =>
        cellB1 Q.η Q.G Q.v t (liftApply 1 (Cc 0 1) (fun _ => f) t) X z +
        cellB2 Q.η Q.G t (fun Y _ => f Y) X z) := by
    simp only [liftMean, liftA, show 2 ≤ (2 : ℕ) by omega, ite_true, sub_zero]
    norm_num only
    rw [hid]
  rw [he]
  exact fieldCellMean_diagonal_second_cross Q.η Q.G Q.v t
    hG hw
    _ hΦ
    f (hf.of_le (by simp)) X


theorem weakLiftMean_diagonal_ge_three
    (Q : LiftOperatorData ι h D) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : 3 ≤ n) (X : Vec 2)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 2 (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t)) :
    liftMean Q Cc (fun _ => f) 0 n t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) •
          liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y z)) X (basisVec q) := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun q => (hw q).continuous) Φ hΦ X
  have he : liftMean Q Cc (fun _ => f) 0 n t X =
      fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t Φ X z + cellB2 Q.η Q.G t Ψ X z) := by
    simp only [liftMean, liftA, Φ, Ψ, show 2 ≤ n by omega, ite_true, sub_zero]
  rw [he, AVRegularity.fieldCellMean_add hB1 (hB2.1.continuous_slice X),
    hB2.2 trivial X, add_zero]
  exact fieldCellMean_cellB1_formula Q.η Q.G Q.v t hG hw Φ hΦ X


end AVRegularity.WeakEntryProofs
end
end

section
/-! A finite weak component family can be labeled injectively by fresh roots. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

open scoped Classical

def weakRootLabel (S : Finset Comp) (v : CompIn S) : ℕ :=
  (Fintype.equivFin (CompIn S) v).val

def weakRootComp (S : Finset Comp) (v : CompIn S) : Comp := ⟨weakRootLabel S v, []⟩

theorem weakRootLabel_injective (S : Finset Comp) : Function.Injective (weakRootLabel S) := by
  intro v u h
  apply (Fintype.equivFin (CompIn S)).injective
  exact Fin.ext h

theorem weakRootComp_injective (S : Finset Comp) : Function.Injective (weakRootComp S) := by
  intro v u h
  exact weakRootLabel_injective S (congrArg Comp.root h)

def weakRootComps (S : Finset Comp) : Finset Comp :=
  Finset.univ.image (weakRootComp S)

def weakRootEquiv (S : Finset Comp) : CompIn S ≃ CompIn (weakRootComps S) :=
  Equiv.ofBijective (fun v => ⟨weakRootComp S v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => weakRootComp_injective S (congrArg Subtype.val h), by
      intro u
      obtain ⟨v, _hv, he⟩ := Finset.mem_image.mp u.2
      exact ⟨v, Subtype.ext he⟩⟩

@[simp] theorem weakRootEquiv_val (S : Finset Comp) (v : CompIn S) :
    (weakRootEquiv S v).1 = weakRootComp S v := rfl

@[simp] theorem weakRootEquiv_births (S : Finset Comp) (v : CompIn S) :
    (weakRootEquiv S v).1.births = [] := rfl

end AVRegularity.WeakEntryProofs
end
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! A common local cutoff preserves the literal initial array and every coefficient identity. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs Set Filter Topology
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
open scoped Classical

def fullLiftLocalCutoff (χ : Vec 2 → ℝ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) : LiftCoeff ι h :=
  fun m α t X z v u => if n = 0 then Cc hh n m α t X z v u
    else χ X • Cc hh n m α (max a (min b t)) X z v u

omit [Fintype ι] in
theorem fullLiftLocalCutoff_zero_degree (χ : Vec 2 → ℝ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) :
    fullLiftLocalCutoff χ a b Cc hh 0 = Cc hh 0 := by
  funext m α t X z v u
  exact ite_eq_left rfl

omit [Fintype ι] in
theorem fullLiftLocalCutoff_copy (χ : Vec 2 → ℝ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Icc a b) (X : Vec 2) (hχ : χ X = 1) (z : Vec 2) (v u : ι) :
    fullLiftLocalCutoff χ a b Cc hh n m α t X z v u = Cc hh n m α t X z v u := by
  by_cases hn : n = 0
  · simp only [fullLiftLocalCutoff, ite_eq_left hn]
  · simp only [fullLiftLocalCutoff, ite_eq_right hn, min_eq_right ht.2,
      max_eq_right ht.1, hχ, one_smul]

omit [Fintype ι] in
theorem fullLiftLocalCutoff_perm (χ : Vec 2 → ℝ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (α : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) (hp : Cc hh n m (α ∘ σ) = Cc hh n m α) :
    fullLiftLocalCutoff χ a b Cc hh n m (α ∘ σ) = fullLiftLocalCutoff χ a b Cc hh n m α := by
  funext t X z v u
  simp only [fullLiftLocalCutoff, hp]

omit [Fintype ι] in
theorem fullLiftLocalCutoff_zero (χ : Vec 2 → ℝ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hc : Cc hh n = 0) :
    fullLiftLocalCutoff χ a b Cc hh n = 0 := by
  funext m α t X z v u
  simp only [fullLiftLocalCutoff, hc, Pi.zero_apply, smul_zero, ite_self]
end

/-! Positive root weights extending the prescribed weights on a finite weak family. -/

def weakRootWeight (S : Finset Comp) (w : CompIn S → ℝ) (r : ℕ) : ℝ :=
  if hr : r < Fintype.card (CompIn S) then
    w ((Fintype.equivFin (CompIn S)).symm ⟨r, hr⟩) else 1

@[simp] theorem weakRootWeight_label (S : Finset Comp) (w : CompIn S → ℝ) (v : CompIn S) :
    weakRootWeight S w (weakRootLabel S v) = w v := by
  simp only [weakRootWeight, weakRootLabel, Fin.is_lt, ↓reduceDIte,
    Fin.eta, Equiv.symm_apply_apply]

 theorem weakRootWeight_pos (S : Finset Comp) (w : CompIn S → ℝ)
    (hw : ∀ v, 0 < w v) (r : ℕ) : 0 < weakRootWeight S w r := by
  unfold weakRootWeight
  split
  · exact hw _
  · exact zero_lt_one

end AVRegularity.WeakEntryProofs
end
end
end

section
section
section
/-! Actual local coefficient cutoffs retain the zero cell mean at positive ranks. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem fullLiftLocalCutoff_positive_mean_zero (χ : Vec 2 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hχ : tsupport χ ⊆ Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : n ≠ 0)
    (m : ℕ) (α : DerivativeWord2 m) (v u : ι)
    (hm : ∀ t ∈ Icc a b, ∀ X ∈ Ω, ∀ ξ,
      fieldCellMean (fun z => Cc hh n m α t X z v u ξ) = 0)
    (t : ℝ) (X : Vec 2) (ξ : h u) :
    fieldCellMean (fun z => fullLiftLocalCutoff χ a b Cc hh n m α t X z v u ξ) = 0 := by
  by_cases hX : X ∈ Ω
  · simp only [fullLiftLocalCutoff, ite_eq_right hn, smul_apply]
    change (∫ z in AVenhance.unitCube, χ X • Cc hh n m α (max a (min b t)) X z v u ξ) = 0
    rw [integral_smul]
    change χ X • fieldCellMean (fun z => Cc hh n m α (max a (min b t)) X z v u ξ) = 0
    rw [hm _ (metric_clamp_mem a b hab t) X hX ξ, smul_zero]
  · have hz : χ X = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hX (hχ hs))
    simp only [fullLiftLocalCutoff, ite_eq_right hn, hz, zero_smul, zero_apply]
    exact fieldCellMean_zero

omit [Fintype ι] in
theorem fullLiftLocalCutoff_rank_mean_zero (χ : Vec 2 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hχ : tsupport χ ⊆ Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hne : hh ≠ 0 ∨ n ≠ 0)
    (hzero : hh ≠ 0 → Cc hh 0 = 0)
    (m : ℕ) (α : DerivativeWord2 m) (v u : ι)
    (hm : ∀ t ∈ Icc a b, ∀ X ∈ Ω, ∀ ξ,
      fieldCellMean (fun z => Cc hh n m α t X z v u ξ) = 0)
    (t : ℝ) (X : Vec 2) (ξ : h u) :
    fieldCellMean (fun z => fullLiftLocalCutoff χ a b Cc hh n m α t X z v u ξ) = 0 := by
  by_cases hn : n = 0
  · subst n
    have hp : hh ≠ 0 := hne.resolve_right (not_not.mpr rfl)
    rw [fullLiftLocalCutoff_zero_degree, hzero hp]
    exact fieldCellMean_zero
  · exact fullLiftLocalCutoff_positive_mean_zero χ a b hab Ω hχ Cc hh n hn m α v u hm t X ξ


end AVRegularity.WeakEntryProofs
end
end

section
/-! Ordered finite composition preserves the local germs of both its factors. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem leftTermSlowEq_fieldPostcompose (Ω : Set (Vec 2))
    {c d : LeftTerm E F} (he : LeftTermSlowEq Ω c d)
    (a b : Vec 2 → Vec 2 → F →L[ℝ] G) (hab : SlowOpenFieldEq Ω a b) :
    LeftTermSlowEq Ω (c.fieldPostcompose a) (d.fieldPostcompose b) := by
  refine ⟨he.order, he.word, ?_⟩
  intro X hX z
  exact congrArg₂ (fun T S => T.comp S) (hab X hX z) (he.coeff X hX z)

theorem leftTermComposition_slow_local_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    {a b : LeftTerm F G} (hab : LeftTermSlowEq Ω a b)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermComposition a l) (leftTermComposition b r) := by
  rcases a with ⟨n, w, f⟩
  rcases b with ⟨n', w', g⟩
  rcases hab with ⟨ho, hw, hf⟩
  dsimp only at ho hw hf
  subst n'
  have hww : w = w' := eq_of_heq hw
  subst w'
  unfold leftTermComposition
  exact List.rel_map (fun _ _ hh => leftTermSlowEq_fieldPostcompose Ω hh f g hf)
    (covariantLeftTermList_slow_local_congr hΩ 1 (List.ofFn w) l r he n)

theorem leftTermsComposition_slow_local_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (a b : List (LeftTerm F G)) (hab : List.Forall₂ (LeftTermSlowEq Ω) a b)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermsComposition a l) (leftTermsComposition b r) :=
  List.rel_flatMap hab (fun _ _ hh => leftTermComposition_slow_local_congr Ω hΩ hh l r he)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Positive ellipticity can be normalized by changing the cell clock, without a metric upper normalization. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs

def ellipticRescaledMolecularData
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (lo CG V : ℝ) (hlo : 0 < lo)
    (hGm : ∀ i j, Measurable (fun t => G t i j))
    (hGb : ∀ t i j, |G t i j| ≤ CG)
    (hGe : ∀ t (ξ : Vec 2), lo * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (hvm : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) : MolecularData where
  G t := lo⁻¹ • G (lo⁻¹ * t)
  v t z := lo⁻¹ • v (lo⁻¹ * t) z
  CG := |lo⁻¹| * CG
  V := lo⁻¹ * V
  metric_measurable i j := measurable_const.mul
    ((hGm i j).comp (measurable_const.mul measurable_id))
  metric_bounded t i j := by
    change |lo⁻¹ * G (lo⁻¹ * t) i j| ≤ |lo⁻¹| * CG
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hGb _ i j) (abs_nonneg _)
  metric_coercive t ξ := by
    have hs : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have he := mul_le_mul_of_nonneg_left (hGe (lo⁻¹ * t) ξ) (inv_nonneg.mpr hlo.le)
    rw [← mul_assoc, inv_mul_cancel₀ hlo.ne', one_mul] at he
    calc
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ξ i ^ 2 := by linarith only [hs]
      _ ≤ lo⁻¹ * ∑ i, ∑ j, G (lo⁻¹ * t) i j * ξ i * ξ j := he
      _ = ∑ i, ∑ j, (lo⁻¹ • G (lo⁻¹ * t)) i j * ξ i * ξ j := by
        simp only [Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  drift_measurable := by
    have hclock : Measurable (fun p : ℝ × Vec 2 => (lo⁻¹ * p.1, p.2)) :=
      (measurable_const.mul measurable_fst).prodMk measurable_snd
    exact (measurable_const : Measurable (fun _ : ℝ × Vec 2 => lo⁻¹)).smul
      (hvm.comp hclock)
  drift_bounded t z := by
    have hb := mul_le_mul_of_nonneg_left (hvb (lo⁻¹ * t) z) (sq_nonneg lo⁻¹)
    calc
      (∑ i, (lo⁻¹ • v (lo⁻¹ * t) z) i ^ 2) = lo⁻¹ ^ 2 * ∑ i, v (lo⁻¹ * t) z i ^ 2 := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      _ ≤ lo⁻¹ ^ 2 * V ^ 2 := hb
      _ = (lo⁻¹ * V) ^ 2 := (mul_pow _ _ _).symm

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual bounded admissible drift defines a molecular bundle with the identity metric. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.EntryWeakProofs

def driftMolecularData (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) : MolecularData where
  G := fun _ => 1
  v := v
  CG := 1
  V := Classical.choose hv.2.1
  metric_measurable := fun _ _ => measurable_const
  metric_bounded := by
    intro t i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  metric_coercive := by
    intro t ξ
    have hs : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ 1) hs
    simpa [Matrix.one_apply, pow_two] using hh
  drift_measurable := hv.1
  drift_bounded := Classical.choose_spec hv.2.1

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual molecular Riesz derivative is linear in the state and the forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularDual_smul (P : MolecularData) (t c : ℝ) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    dataDualDerivative P t (c • u) (c • S) (fun k => c • F k) =
      c • dataDualDerivative P t u S F := by
  apply ext_inner_right ℝ
  intro z
  rw [real_inner_smul_left, dataDualDerivative_pairing, dataDualDerivative_pairing]
  have hl := congrArg (fun L : TorusHk 1 ℂ →L[ℝ] ℝ => L z)
    ((dataGeneratorForm P t).map_smul c u)
  simp only [smul_apply, smul_eq_mul] at hl
  have hs : cellSourceFunctional 0 (c • S) (fun k => c • F k) z =
      c * cellSourceFunctional 0 S F z := by
    simp only [cellSourceFunctional, Fin.sum_univ_two, sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_smul_left]
    ring
  rw [hs, hl]
  ring

end AVRegularity.WeakEntryProofs
end
end

section
/-! Changing the molecular metric is exactly a divergence forcing on the previous state. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational

def molecularMetricHilbertFlux (M : Matrix (Fin 2) (Fin 2) ℝ) (u : TorusHk 1 ℂ) :
    Fin 2 → ComplexCellL2 := fun k => ∑ j, M j k • cellDerivativeCLM j u

theorem molecularGeneratorForm_metric_difference
    (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    molecularGeneratorForm G v V hv hb t u z - molecularGeneratorForm H v V hv hb t u z =
      cellSourceFunctional 0 0 (molecularMetricHilbertFlux (G t - H t) u) z := by
  have hd (k : Fin 2) : cellDriftEntryCLM (molecularCoefficients G v) V hv hb t k =
      cellDriftEntryCLM (molecularCoefficients H v) V hv hb t k := rfl
  have hz (k : Fin 2) : cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) k =
      cellDerivativeCLM k := by simp [cellShiftedDerivativeCLM, cellScalarCLM]
  simp only [molecularGeneratorForm, cellSourceFunctional, Fin.sum_univ_two,
    sub_apply, add_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply,
    molecularDiffusionForm_apply, innerSL_apply_apply, inner_zero_left,
    molecularMetricHilbertFlux, inner_add_left, real_inner_smul_left, Matrix.sub_apply, hd, hz]
  ring

end AVRegularity.WeakEntryProofs
end
end

section
/-! Literal finite source coefficients preserve the open slow germs of their term lists. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem leftTermsBlockCoefficient_slow_local_congr
    (Ω : Set (Vec 2)) (l r : ∀ v, List (LeftTerm (∀ i, h i) (h v)))
    (he : ∀ v, List.Forall₂ (LeftTermSlowEq Ω) (l v) (r v))
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ)
    (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) (v u : ι) :
    leftTermsBlockCoefficient l m α t X z v u =
      leftTermsBlockCoefficient r m α t X z v u := by
  exact congrArg (fun f => f.comp (ContinuousLinearMap.single ℝ h u))
    (leftTermsSymmetricCoefficient_slow_local_congr (l v) (r v) (he v) m α X hX z)

end AVRegularity.WeakEntryProofs
end
end

section
/-! A matrix-entry perturbation bound controls its actual Hilbert divergence flux. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_norm_le
    (M : Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ) (hb : ∀ j k, |M j k| ≤ C)
    (u : TorusHk 1 ℂ) (k : Fin 2) :
    ‖molecularMetricHilbertFlux M u k‖ ≤ C * ∑ j, ‖cellDerivativeCLM j u‖ := by
  have hj (j : Fin 2) : ‖M j k • cellDerivativeCLM j u‖ ≤ C * ‖cellDerivativeCLM j u‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb j k) (norm_nonneg _)
  simp only [molecularMetricHilbertFlux, Fin.sum_univ_two]
  exact (norm_add_le _ _).trans (by simpa only [mul_add] using add_le_add (hj 0) (hj 1))

theorem molecularMetricHilbertFlux_norm_sq_le
    (M : Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ) (hb : ∀ j k, |M j k| ≤ C)
    (u : TorusHk 1 ℂ) (k : Fin 2) :
    ‖molecularMetricHilbertFlux M u k‖ ^ 2 ≤
      2 * C ^ 2 * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg (M 0 0)).trans (hb 0 0)
  have hn := molecularMetricHilbertFlux_norm_le M C hb u k
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  simp only [Fin.sum_univ_two] at hs ⊢
  have he := mul_nonneg (sq_nonneg C)
    (sq_nonneg (‖cellDerivativeCLM 0 u‖ - ‖cellDerivativeCLM 1 u‖))
  nlinarith

end AVRegularity.WeakEntryProofs
end
end

section
/-! Separate metric and state variations in the actual differentiated forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_difference (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : TorusHk 1 ℂ) (k : Fin 2) :
    molecularMetricHilbertFlux M u k - molecularMetricHilbertFlux N v k =
      molecularMetricHilbertFlux M (u - v) k + molecularMetricHilbertFlux (M - N) v k := by
  simp only [molecularMetricHilbertFlux, Fin.sum_univ_two, map_sub, Matrix.sub_apply,
    sub_smul, smul_sub]
  abel

end AVRegularity.WeakEntryProofs
end
end

section
/-! Matrix Taylor remainders pass literally through the Hilbert metric flux. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_smul_sub (M D : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) (u : TorusHk 1 ℂ) (k : Fin 2) :
    c • molecularMetricHilbertFlux M u k - molecularMetricHilbertFlux D u k =
      molecularMetricHilbertFlux (c • M - D) u k := by
  simp only [molecularMetricHilbertFlux, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, smul_add, sub_smul, smul_smul]
  abel

theorem molecularMetricHilbertFlux_quotient_residual
    (M D : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (u v : TorusHk 1 ℂ)
    (F F' F₁ : Fin 2 → ComplexCellL2) (k : Fin 2) :
    c • (F k - F' k + molecularMetricHilbertFlux M u k) -
        (F₁ k + molecularMetricHilbertFlux D u k) + molecularMetricHilbertFlux M v k =
      (c • (F k - F' k) - F₁ k) +
        molecularMetricHilbertFlux (c • M - D) u k + molecularMetricHilbertFlux M v k := by
  rw [smul_add, ← molecularMetricHilbertFlux_smul_sub]
  abel

end AVRegularity.WeakEntryProofs
end
end

section
/-! Bounded measurable metric perturbations preserve the square-integrable gradient forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_memLp (μ : Measure ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ)
    (hm : ∀ j k, Measurable (fun t => M t j k))
    (hb : ∀ t j k, |M t j k| ≤ C)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 μ) (k : Fin 2) :
    MemLp (fun t => molecularMetricHilbertFlux (M t) (u t) k) 2 μ := by
  have hj (j : Fin 2) : MemLp (fun t => M t j k • cellDerivativeCLM j (u t)) 2 μ := by
    have hd := (cellDerivativeCLM j).comp_memLp' hu
    apply hd.of_le_mul (c := C) ((hm j k).aestronglyMeasurable.smul hd.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun t => by
      change ‖M t j k • cellDerivativeCLM j (u t)‖ ≤ C * ‖cellDerivativeCLM j (u t)‖
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb t j k) (norm_nonneg _))
  simpa only [molecularMetricHilbertFlux, Fin.sum_univ_two, Pi.add_apply] using! (hj 0).add (hj 1)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Parameter metric replacement retains the identical drift data and its finite bounds. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

def molecularMetricReplacement (P : MolecularData)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℝ)
    (hgm : ∀ i j, Measurable (fun t => G t i j))
    (hgb : ∀ t i j, |G t i j| ≤ CG)
    (hge : ∀ t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j) :
    MolecularData where
  G := G
  v := P.v
  CG := CG
  V := P.V
  metric_measurable := hgm
  metric_bounded := hgb
  metric_coercive := hge
  drift_measurable := P.drift_measurable
  drift_bounded := P.drift_bounded

theorem molecularMetricReplacement_generator_difference (P : MolecularData)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℝ)
    (hgm : ∀ i j, Measurable (fun t => G t i j))
    (hgb : ∀ t i j, |G t i j| ≤ CG)
    (hge : ∀ t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    dataGeneratorForm (molecularMetricReplacement P G CG hgm hgb hge) t u z -
      dataGeneratorForm P t u z = cellSourceFunctional 0 0
        (molecularMetricHilbertFlux (G t - P.G t) u) z := by
  exact molecularGeneratorForm_metric_difference G P.G P.v P.V P.drift_measurable
    P.drift_bounded t u z

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual Riesz time derivative obeys the metric resolvent difference identity. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularDual_metric_difference (P : MolecularData)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℝ)
    (hgm : ∀ i j, Measurable (fun t => G t i j))
    (hgb : ∀ t i j, |G t i j| ≤ CG)
    (hge : ∀ t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (t : ℝ) (u v : TorusHk 1 ℂ) (S S' : ComplexCellL2) (F F' : Fin 2 → ComplexCellL2) :
    let Q := molecularMetricReplacement P G CG hgm hgb hge
    dataDualDerivative Q t u S F - dataDualDerivative P t v S' F' =
      dataDualDerivative Q t (u - v) (S - S')
        (fun k => F k - F' k + molecularMetricHilbertFlux (G t - P.G t) v k) := by
  let Q := molecularMetricReplacement P G CG hgm hgb hge
  apply ext_inner_right ℝ
  intro z
  rw [inner_sub_left, dataDualDerivative_pairing, dataDualDerivative_pairing,
    dataDualDerivative_pairing]
  have hlin := congrArg (fun L : TorusHk 1 ℂ →L[ℝ] ℝ => L z)
    ((dataGeneratorForm Q t).map_sub u v)
  simp only [sub_apply] at hlin
  have hd := molecularMetricReplacement_generator_difference P G CG hgm hgb hge t v z
  have hs : cellSourceFunctional 0 (S - S')
      (fun k => F k - F' k + molecularMetricHilbertFlux (G t - P.G t) v k) z =
      cellSourceFunctional 0 S F z - cellSourceFunctional 0 S' F' z +
        cellSourceFunctional 0 0 (molecularMetricHilbertFlux (G t - P.G t) v) z := by
    simp only [cellSourceFunctional, Fin.sum_univ_two, sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_left,
      inner_add_left, inner_zero_left]
    ring
  rw [hs]
  linarith only [hlin, hd]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniform entry bounds control the time-integrated metric perturbation forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_integral_le {a b : ℝ} (hab : a ≤ b)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ)
    (hm : ∀ j k, Measurable (fun t => M t j k))
    (hb : ∀ t j k, |M t j k| ≤ C)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    (∫ s in a..b, ∑ k, ‖molecularMetricHilbertFlux (M s) (u s) k‖ ^ 2) ≤
      4 * C ^ 2 * ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2 := by
  have hf (k : Fin 2) := cellTime_normSq_intervalIntegrable hab
    (molecularMetricHilbertFlux_memLp _ M C hm hb u hu k)
  have hi : IntervalIntegrable (fun s => ∑ k,
      ‖molecularMetricHilbertFlux (M s) (u s) k‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using (hf 0).add (hf 1)
  have hg := cellTime_gradientSq_intervalIntegrable hab u hu
  have hp (s : ℝ) : (∑ k, ‖molecularMetricHilbertFlux (M s) (u s) k‖ ^ 2) ≤
      4 * C ^ 2 * ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2 := by
    have h0 := molecularMetricHilbertFlux_norm_sq_le (M s) C (hb s) (u s) 0
    have h1 := molecularMetricHilbertFlux_norm_sq_le (M s) C (hb s) (u s) 1
    simp only [Fin.sum_univ_two] at h0 h1 ⊢
    linarith
  have h := intervalIntegral.integral_mono_on hab hi (hg.const_mul (4 * C ^ 2))
    (fun s _ => hp s)
  simpa only [intervalIntegral.integral_const_mul] using h

end AVRegularity.WeakEntryProofs
end
end

section
/-! Ordered-word metric forcing in the actual Hilbert variational equations. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {I : Type*}

def molecularWordHilbertFlux
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → ℝ → TorusHk 1 ℂ) (w : List I) : ℝ → Fin 2 → ComplexCellL2 :=
  ((independentWordForcing w).map (fun p t => molecularMetricHilbertFlux (G p.1 t) (u p.2 t))).sum

def molecularWordHilbertFluxDerivative
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → ℝ → TorusHk 1 ℂ) (i : I) (w : List I) : ℝ → Fin 2 → ComplexCellL2 :=
  ((independentWordForcing w).map (fun p t =>
    molecularMetricHilbertFlux (G (i :: p.1) t) (u p.2 t) +
      molecularMetricHilbertFlux (G p.1 t) (u (i :: p.2) t))).sum

theorem molecularWordHilbertFlux_cons
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → ℝ → TorusHk 1 ℂ) (i : I) (w : List I) :
    molecularWordHilbertFlux G u (i :: w) =
      (fun t => molecularMetricHilbertFlux (G [i] t) (u w t)) +
        molecularWordHilbertFluxDerivative G u i w :=
  independentWordForcing_cons_sum i w (fun a b t => molecularMetricHilbertFlux (G a t) (u b t))

theorem molecularWordHilbertFlux_memLp {a b : ℝ}
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → ℝ → TorusHk 1 ℂ) (w : List I) (B : List I → ℝ)
    (hm : ∀ p ∈ independentWordForcing w, ∀ j k, Measurable (fun t => G p.1 t j k))
    (hb : ∀ p ∈ independentWordForcing w, ∀ t j k, |G p.1 t j k| ≤ B p.1)
    (hu : ∀ p ∈ independentWordForcing w, MemLp (u p.2) 2 (volume.restrict (Icc a b)))
    (k : Fin 2) :
    MemLp (fun t => molecularWordHilbertFlux G u w t k) 2 (volume.restrict (Icc a b)) := by
  have hp (p : List I × List I) (h : p ∈ independentWordForcing w) :=
    molecularMetricHilbertFlux_memLp _ (G p.1) (B p.1) (hm p h) (hb p h) (u p.2) (hu p h) k
  unfold molecularWordHilbertFlux
  generalize independentWordForcing w = l at hp ⊢
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil, Pi.zero_apply] using!
      (MemLp.zero (ε := ComplexCellL2) (p := 2) (μ := volume.restrict (Icc a b)))
  | cons p l ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using!
      (hp p List.mem_cons_self).add (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Taylor remainder fluxes need perturbation bounds only eventually along the punctured parameter filter. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_component_integral_tendsto_zero_of_eventually_bound
    {A : Type*} (l : Filter A) {a b : ℝ} (hab : a ≤ b)
    (M : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (C : A → ℝ)
    (hm : ∀ X j k, Measurable (fun t => M X t j k))
    (hb : ∀ᶠ X in l, ∀ t j k, |M X t j k| ≤ C X)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hc : Tendsto C l (𝓝 0)) (k : Fin 2) :
    Tendsto (fun X => ∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2) l (𝓝 0) := by
  have hn (X : A) : 0 ≤ ∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
  have he : ∀ᶠ X in l, (∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2) ≤
      4 * C X ^ 2 * ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2 := by
    filter_upwards [hb] with X hX
    have hf (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
      (molecularMetricHilbertFlux_memLp _ (M X) (C X) (hm X) hX u hu j)
    have hi : IntervalIntegrable (fun s => ∑ j,
        ‖molecularMetricHilbertFlux (M X s) (u s) j‖ ^ 2) volume a b := by
      simpa only [Fin.sum_univ_two, Pi.add_apply] using (hf 0).add (hf 1)
    exact (intervalIntegral.integral_mono_on hab (hf k) hi (fun s _ =>
      Finset.single_le_sum (fun j _ =>
        sq_nonneg ‖molecularMetricHilbertFlux (M X s) (u s) j‖) (Finset.mem_univ k))).trans
      (molecularMetricHilbertFlux_integral_le hab (M X) (C X) (hm X) hX u hu)
  have hs : Tendsto (fun X => 4 * C X ^ 2 *
      ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using
      ((hc.pow 2).const_mul 4).mul_const
        (∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2)
  exact squeeze_zero' (Eventually.of_forall hn) he hs

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Literal raw metric forcing and its actual Hilbert divergence class agree on genuine slices. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem cellH1Slice_derivative_ae (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) (j : Fin 2) :
    cellDerivativeCLM j (cellH1Slice D t) =ᵐ[volume.restrict AVenhance.unitCube] cellGradComp (D t) j := by
  rw [cellH1Slice_eq_toHk D t ht]
  exact torusJetToL2_ae (D t) ht.2.1 ⟨⟨1, by decide⟩, fun _ => j⟩

theorem cellMetricFlux_Hilbert_ae
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) (k : Fin 2) :
    molecularMetricHilbertFlux (M t).transpose (cellH1Slice D t) k =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => cellMetricFlux (fun t _ => M t) D t x k := by
  unfold molecularMetricHilbertFlux
  simp only [Fin.sum_univ_two, Matrix.transpose_apply]
  filter_upwards [Lp.coeFn_add (M t k 0 • cellDerivativeCLM 0 (cellH1Slice D t))
    (M t k 1 • cellDerivativeCLM 1 (cellH1Slice D t)),
    Lp.coeFn_smul (M t k 0) (cellDerivativeCLM 0 (cellH1Slice D t)),
    Lp.coeFn_smul (M t k 1) (cellDerivativeCLM 1 (cellH1Slice D t)),
    cellH1Slice_derivative_ae D t ht 0, cellH1Slice_derivative_ae D t ht 1] with x ha h0 h1 hd0 hd1
  rw [ha, Pi.add_apply, h0, h1, Pi.smul_apply, Pi.smul_apply, hd0, hd1]
  simp only [cellMetricFlux, cellMetricFluxVector, cellGradient,
    Fin.sum_univ_two, Complex.real_smul]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Fixed-length paths of a finite charted stage form a finite type. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem stagePath_step_injective (G : GenStage D hr Dm b j₀) (h : ℕ) :
    Function.Injective (StagePath.step (G := G) (h := h)) := by
  intro π π' he
  cases π
  cases π'
  cases he
  rfl

instance weakEntryStagePathFinite (G : GenStage D hr Dm b j₀) (h : ℕ) :
    Finite (StagePath G h) :=
  Finite.of_injective StagePath.step (stagePath_step_injective G h)

end AVRegularity.WeakEntryProofs
end
end
end
end
