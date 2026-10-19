-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.EntryWeakAssembly.CoordinateWordRawHilbertCurves
public import AVRegularity.EntryWeak.IndependentCenteredChildReanchorCoordinates

@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs

/-- Head-class cache: the normed group of the periodic Sobolev carrier. -/
local instance quietScalarTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
/-- Head-class cache: the inner product space of the periodic Sobolev carrier. -/
local instance quietScalarTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
/-- Head-class cache: the normed space of the periodic Sobolev carrier. -/
local instance quietScalarTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

end AVRegularity.WeakEntryProofs
end

attribute [local instance] AVRegularity.WeakEntryProofs.quietScalarTorusNormed
  AVRegularity.WeakEntryProofs.quietScalarTorusInner
  AVRegularity.WeakEntryProofs.quietScalarTorusSpace

section
/-! Native scalar torus energy, restarted and truncated without a new PDE
existence theorem. These are the positive-order inputs for quiet margin propagation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The homogeneous scalar torus equation, as the literal singleton zero-coupled
energy solution. No estimate or regularity conclusion is included. -/
abbrev WeakScalarTorusSolution (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (K : ℕ)
    (f : TorusHk K E) (u : ℝ → TorusHk K E) (w : ℝ → TorusHk (K + 1) E) : Prop :=
  Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 K f
    (fun _ => 0) (fun _ => 0) u w

/-- Finite drift jets and the two radius conditions of the coupled energy estimate
`coupled_energy_torus`. Global measurability is available for the stream drift; all bounds are
local. -/
structure WeakScalarTorusDrift (ν ρ a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (Q : ℕ) where
  nu_pos : 0 < ν
  radius_pos : 0 < ρ
  measurable : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)
  bounded : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ C
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)
  div : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0
  periodic : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t)
  amplitude : ℝ
  amplitude_nonneg : 0 ≤ amplitude
  base : ℝ
  base_ge : 1 ≤ base
  length : ℝ
  length_pos : 0 < length
  jets : ∀ l : ℕ, 1 ≤ l → l ≤ Q → ∀ t ∈ Set.Icc a b, ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      amplitude * base ^ l * (l.factorial : ℝ) * length ^ ((1 : ℤ) - l)
  scale : base * ρ / length ≤ 1 / 2
  strain : amplitude * base * ρ ^ 2 ≤ ν / 8

/-- Truncating a scalar trajectory preserves its exact weak equation. -/
theorem weak_scalar_torus_solution_truncate {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K L : ℕ} (hKL : K ≤ L) {f : TorusHk L E}
    {u : ℝ → TorusHk L E} {w : ℝ → TorusHk (L + 1) E}
    (hs : WeakScalarTorusSolution ν a b v L f u w) :
    WeakScalarTorusSolution ν a b v K (truncateTorusHk hKL f)
      (fun t => truncateTorusHk hKL (u t))
      (fun t => truncateTorusHk (Nat.succ_le_succ hKL) (w t)) := by
  simpa only [ContinuousLinearMap.map_zero] using
    Providers.WeakGen.Comparison.torusForcedRow_truncate hKL hs

/-- Existence and uniqueness for the actual homogeneous scalar equation at any
finite reserve. These are specializations of `coupled_energy_torus` (Proposition 7.6 of the
paper). -/
theorem weak_scalar_torus_exists_unique {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (f : TorusHk K E) :
    (∃ (u : ℝ → TorusHk K E) (w : ℝ → TorusHk (K + 1) E),
      WeakScalarTorusSolution ν a b v K f u w) ∧
    (∀ (u u' : ℝ → TorusHk K E) (w w' : ℝ → TorusHk (K + 1) E),
      WeakScalarTorusSolution ν a b v K f u w →
      WeakScalarTorusSolution ν a b v K f u' w' →
      ∀ t ∈ Set.Icc a b, u t = u' t) := by
  obtain ⟨V, hV⟩ := hd.bounded
  have hg := Providers.coupled_energy_torus (h := fun _ : Fin 1 => E) a b hab ρ hd.radius_pos
    ν hd.nu_pos v ⟨V, fun z hz x => hV z hz x⟩
    (hd.measurable.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    hd.smooth hd.div
    hd.periodic hd.amplitude hd.base hd.length
    hd.amplitude_nonneg hd.base_ge hd.length_pos Q
    hd.jets hd.scale hd.strain 2 (by norm_num)
    (fun _ => 1) (fun _ => zero_lt_one) (fun _ => K) (fun _ => hK) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ => by simp only [CycleComparison.Coarse.coefficientSeminorm_const_zero, ne_eq,
      ENNReal.zero_ne_top, not_false_eq_true])
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ (fun _ : Fin 1 => 1) (fun _ => K) 2 a b)
    (fun _ => f) (fun _ _ => 0) (fun _ => CoupledEnergy.Variational.timeMemLp_zero _ _)
    (fun _ _ => 0) (fun _ => CoupledEnergy.Variational.timeIntegrable_zero _)
  constructor
  · obtain ⟨u, w, hsol⟩ := hg.1
    have hu : u = fun _ => u 0 := funext fun j => congrArg u (Subsingleton.elim j 0)
    have hw : w = fun _ => w 0 := funext fun j => congrArg w (Subsingleton.elim j 0)
    rw [hu, hw] at hsol
    exact ⟨u 0, w 0, hsol⟩
  · intro u u' w w' hsol hsol' t ht
    exact hg.2.1 (fun _ => u) (fun _ => u') (fun _ => w) (fun _ => w') hsol hsol' 0 t ht

/-- The energy estimate of `coupled_energy_torus` restarts at any time of the scalar trajectory.
The integral is over the whole chosen subwindow, as required by smoothing. -/
theorem weak_scalar_torus_restarted_energy {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    {f : TorusHk K E} {u : ℝ → TorusHk K E} {w : ℝ → TorusHk (K + 1) E}
    (hs : WeakScalarTorusSolution ν a b v K f u w)
    (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    factorialNormSq ρ (u t).val + ν / 2 * (∫ z in s..t, gradFactorialNormSq ρ (w z).val) ≤
      2 * factorialNormSq ρ (u s).val := by
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc has htb
  have hsol := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left htb hs
  have hsol' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right has hst hsol
  obtain ⟨V, hV⟩ := hd.bounded
  have he := (Providers.coupled_energy_torus (h := fun _ : Fin 1 => E) s t hst ρ hd.radius_pos
    ν hd.nu_pos v ⟨V, fun z hz x => hV z (hsub hz) x⟩
    (hd.measurable.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (fun z hz => hd.smooth z (hsub hz)) (fun z hz => hd.div z (hsub hz))
    (fun z hz => hd.periodic z (hsub hz)) hd.amplitude hd.base hd.length
    hd.amplitude_nonneg hd.base_ge hd.length_pos Q
    (fun l hl hlQ z hz => hd.jets l hl hlQ z (hsub hz)) hd.scale hd.strain 2 (by norm_num)
    (fun _ => 1) (fun _ => zero_lt_one) (fun _ => K) (fun _ => hK) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ => by simp only [CycleComparison.Coarse.coefficientSeminorm_const_zero, ne_eq,
      ENNReal.zero_ne_top, not_false_eq_true])
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ (fun _ : Fin 1 => 1) (fun _ => K) 2 s t)
    (fun _ => u s) (fun _ _ => 0) (fun _ => CoupledEnergy.Variational.timeMemLp_zero _ _)
    (fun _ _ => 0) (fun _ => CoupledEnergy.Variational.timeIntegrable_zero _)).2.2
      (fun _ => u) (fun _ => w) hsol' t ⟨hst, le_rfl⟩
  simp only [massNormSq, massGradNormSq, Fin.sum_univ_one,
    inv_one, one_mul] at he
  simp only [ZeroMemClass.coe_zero, CycleComparison.Coarse.factorialNormSq_zero_jet,
    integral_zero, Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at he
  rw [intervalIntegral.integral_of_le hst]
  rw [← integral_Icc_eq_integral_Ioc]
  exact he

end AVRegularity.WeakEntryProofs
end
end

section
/-! Every fixed native history has a global positive metric extension agreeing near any slow label. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Metric AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem native_local_metric_production (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm h) (a b : ℝ) (hab : a ≤ b) (Y₀ : Vec 2) :
    ∃ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (lo : ℝ) (B : ℕ → ℝ)
      (U : Set (Vec 2)),
      0 < lo ∧ (∀ n, 0 ≤ B n) ∧ IsOpen U ∧ Y₀ ∈ U ∧
      (∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j)) ∧
      (∀ Y i j, Measurable (fun t => G t Y i j)) ∧
      (∀ t Y, (G t Y).IsSymm) ∧
      (∀ n t Y i j, ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n) ∧
      (∀ t Y (ξ : Vec 2), lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, G t Y = (familyLiftData D m slot A ρ edge).G t Y := by
  let G₀ : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t Y => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y)
  let χ : ContDiffBump Y₀ := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let S := tsupport (χ : Vec 2 → ℝ)
  have hS : IsCompact S := χ.hasCompactSupport
  have hG i j : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => G₀ p.1 p.2 i j) :=
    familyLiftData_metric_spacetime_smooth D hζ m slot A hl ρ edge i j
  obtain ⟨lo, hlo, he⟩ := native_metric_compact_elliptic D hζ m slot A hl ρ edge a b S hS
  obtain ⟨B, hB, hb⟩ := compact_cutoff_metric_jet_budget G₀ hG χ χ.contDiff χ.hasCompactSupport
    S hS (subset_refl _) a b
  let G := clampedParameterMetric (cutoffParameterMetric χ G₀) a b
  have hcl t : max a (min b t) ∈ Icc a b := metric_clamp_mem a b hab t
  have hχrange Y : χ Y ∈ Icc 0 1 := ⟨χ.nonneg, χ.le_one⟩
  refine ⟨G, min lo 1, B, ball Y₀ (1 / 4), lt_min hlo zero_lt_one, hB,
    isOpen_ball, mem_ball_self (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i j
    change ContDiff ℝ ∞ (fun X => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      χ X * (G₀ (max a (min b t)) X i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    exact contDiff_const.add (χ.contDiff.mul
      (((hG i j).comp₂ contDiff_const contDiff_id).sub contDiff_const))
  · intro Y i j
    have hm : Measurable (fun t => G₀ t Y i j) :=
      ((hG i j).continuous.comp (continuous_id.prodMk continuous_const)).measurable
    change Measurable (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      χ Y * (G₀ (max a (min b t)) Y i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    exact measurable_const.add (measurable_const.mul
      ((hm.comp (measurable_const.max (measurable_const.min measurable_id))).sub measurable_const))
  · intro t Y
    apply cutoffParameterMetric_isSymm
    ext i j
    exact familyLiftData_metric_symmetric D m slot A ρ edge _ Y j i
  · intro n t Y i j
    exact hb n _ (hcl t) Y i j
  · intro t Y ξ
    exact positive_cutoff_metric_lower χ hχrange G₀ lo (max a (min b t)) Y
      (fun hY => he _ (hcl t) Y hY) ξ
  · intro t ht Y hY
    have hc : χ Y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hY)
    change cutoffParameterMetric χ G₀ (max a (min b t)) Y = G₀ t Y
    rw [min_eq_right ht.2, max_eq_right ht.1, cutoffParameterMetric_eq_convex, hc,
      one_smul, sub_self, zero_smul, add_zero]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Arbitrary native-history metrics have genuine local primitive source models at every reserve. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem native_local_metric_joint_reserve (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm h) (a b : ℝ) (hab : a ≤ b)
    (H : ℕ) (Y₀ : Vec 2) :
    ∃ (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (U : Set (Vec 2)),
      IsOpen U ∧ Y₀ ∈ U ∧
      Nonempty (∀ i j, JointSourceReserve H (fun t _ Y => G t Y i j)) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, G t Y = (familyLiftData D m slot A ρ edge).G t Y := by
  obtain ⟨G, _lo, B, U, _hlo, hB, hU, hY, hr, hm, _hs, hb, _he, heq⟩ :=
    native_local_metric_production D hζ m slot A hl ρ edge a b hab Y₀
  refine ⟨G, U, hU, hY, ?_, heq⟩
  refine ⟨fun i j => slowIndependentJointSourceReserve H (fun t Y => G t Y i j)
    (fun t => (hr t i j).of_le (by simp)) (fun Y => hm Y i j) B hB ?_⟩
  intro n _hn t Y
  exact hb n t Y i j

end AVRegularity.WeakEntryProofs
end
end

section
/-! Positive-order short smoothing of the actual homogeneous torus trajectory.
The scalar price is dimensionless once the squared radius is compared to νδ. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.WeakEntryProofs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
private theorem weak_scalar_lower_lift {Q j : ℕ} (hj : j ≤ Q)
    {u : TorusHk Q E} {w : TorusHk (Q + 1) E}
    (ht : truncateTorusHk (Nat.le_succ Q) w = u) :
    truncateTorusHk hj u = truncateTorusHk (hj.trans (Nat.le_succ Q)) w := by
  rw [← ht]
  rfl

/-- Positive Sobolev smoothing of a genuine scalar torus solution, with its
explicit radius/duration price. No regularity or estimate of a forced row is
substituted for this homogeneous scalar estimate. -/
theorem weak_scalar_torus_short_smoothing {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    (Q : ℕ) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    {f : TorusHk Q E} {u : ℝ → TorusHk Q E} {w : ℝ → TorusHk (Q + 1) E}
    (hs : WeakScalarTorusSolution ν a b v Q f u w)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : a + Q * δ ≤ t) (htb : t ≤ b) :
    factorialNormSq ρ (u t).val ≤
      2 * (4 + 8 * ρ ^ 2 / (ν * δ)) ^ Q *
        factorialNormSq ρ (truncateTorusHk (Nat.zero_le Q) (u a)).val := by
  let energy := fun j z => if hj : j ≤ Q then factorialNormSq ρ
    (truncateTorusHk (E := E) hj (u z)).val else factorialNormSq ρ (u z).val
  let G := fun j z => if hj : j ≤ Q then gradFactorialNormSq ρ
    (truncateTorusHk (E := E) (Nat.succ_le_succ hj) (w z)).val
    else gradFactorialNormSq ρ (w z).val
  have hc (j : ℕ) (hj : j ≤ Q) : ContinuousOn (energy j) (Icc a b) := by
    simpa only [energy, dite_eq_left hj, Function.comp_def] using
      ((CycleComparison.Coarse.continuous_factorialNormSq ρ _).comp
        continuous_subtype_val).comp_continuousOn
          ((truncateTorusHk (E := E) hj).continuous.comp_continuousOn (hs.1 0))
  have hn (j : ℕ) (hj : j ≤ Q) (z : ℝ) (_hz : z ∈ Icc a b) : 0 ≤ energy j z := by
    simp only [energy, dite_eq_left hj]
    exact factorialNormSq_nonneg _ _
  have hg (j : ℕ) (hj : j ≤ Q) : IntegrableOn (G j) (Icc a b) := by
    have hw : MemLp w 2 (volume.restrict (Icc a b)) := hs.2.1 0
    have hw' : MemLp (fun z => truncateTorusHk
        (Nat.succ_le_succ hj) (w z)) 2 (volume.restrict (Icc a b)) :=
      (truncateTorusHk (E := E) (Nat.succ_le_succ hj)).comp_memLp' hw
    simpa only [G, dite_eq_left hj, IntegrableOn] using
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (ρ := ρ) hw')
  have hgn (j : ℕ) (hj : j ≤ Q) (z : ℝ) (_hz : z ∈ Icc a b) : 0 ≤ G j z := by
    simp only [G, dite_eq_left hj]
    exact CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _
  have htrace : ∀ᵐ z ∂(volume.restrict (Icc a b)),
      truncateTorusHk (E := E) (Nat.le_succ Q) (w z) = u z := hs.2.2.1 0
  have hbridge (j : ℕ) (hj : j < Q) : ∀ᵐ z ∂(volume.restrict (Icc a b)),
      energy (j + 1) z ≤ energy j z + ρ ^ 2 * G j z := by
    filter_upwards [htrace] with z hz
    have hjQ : j + 1 ≤ Q := Nat.succ_le_of_lt hj
    have hnext := weak_scalar_lower_lift (E := E) (Q := Q) (j := j + 1) hjQ hz
    have hprev := weak_scalar_lower_lift (E := E) (Q := Q) (j := j) hj.le hz
    have hh : factorialNormSq ρ (truncateTorusHk (E := E) hjQ (u z)).val ≤
        factorialNormSq ρ (truncateTorusHk (E := E) hj.le (u z)).val + ρ ^ 2 *
          gradFactorialNormSq ρ (truncateTorusHk (E := E) (Nat.succ_le_succ hj.le) (w z)).val := by
      rw [hnext, hprev]
      exact weak_factorial_one_jet_bridge (E := E) ρ (truncateTorusHk
        (Nat.succ_le_succ hj.le) (w z)).val
    simpa only [energy, G, dite_eq_left hjQ, dite_eq_left hj.le] using hh
  have he (j : ℕ) (hj : j ≤ Q) (s z : ℝ)
      (has : a ≤ s) (hsz : s ≤ z) (hzb : z ≤ b) :
      energy j z + ν / 2 * (∫ y in s..z, G j y) ≤ 2 * energy j s := by
    simpa only [energy, G, dite_eq_left hj] using weak_scalar_torus_restarted_energy hj hd
      (weak_scalar_torus_solution_truncate hj hs) s z has hsz hzb
  have hbound := weak_scalar_smoothing_from_restarted_energy energy G a b ν (ρ ^ 2) δ Q
    hd.nu_pos (sq_nonneg _) hδ hc hn hg hgn hbridge he t ht htb
  have hend : energy Q t = factorialNormSq ρ (u t).val := by
    simp only [energy, dite_eq_left (le_refl Q)]
    rfl
  have hstart : energy 0 a = factorialNormSq ρ
      (truncateTorusHk (E := E) (Nat.zero_le Q) (u a)).val := by
    simp only [energy, dite_eq_left (Nat.zero_le Q)]
  rw [hend, hstart] at hbound
  exact hbound

/-- Endpoint smoothing with all short intervals inside the actual window. The
entrance norm is precisely the order-zero norm, independent of the radius. -/
theorem weak_scalar_torus_window_smoothing {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    (Q : ℕ) (hd : WeakScalarTorusDrift ν ρ a b v Q) (hab : a < b)
    {f : TorusHk Q E} {u : ℝ → TorusHk Q E} {w : ℝ → TorusHk (Q + 1) E}
    (hs : WeakScalarTorusSolution ν a b v Q f u w) :
    factorialNormSq ρ (u b).val ≤
      2 * (4 + 8 * ρ ^ 2 * (Q + 1) / (ν * (b - a))) ^ Q *
        factorialNormSq 1 (truncateTorusHk (Nat.zero_le Q) (u a)).val := by
  have hT : 0 < b - a := sub_pos.mpr hab
  have hQ : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  let δ := (b - a) / ((Q : ℝ) + 1)
  have hδ : 0 < δ := div_pos hT hQ
  have htime : a + (Q : ℝ) * δ ≤ b := by
    have hh : ((Q : ℝ) + 1) * δ = b - a := by
      dsimp only [δ]
      exact mul_div_cancel₀ _ hQ.ne'
    nlinarith only [hh, hδ.le]
  have he := weak_scalar_torus_short_smoothing Q hd hs δ hδ b htime le_rfl
  have hprice : 8 * ρ ^ 2 / (ν * δ) =
      8 * ρ ^ 2 * (Q + 1) / (ν * (b - a)) := by
    dsimp only [δ]
    field_simp
  rw [hprice, CycleJointProofs.factorialNormSq_order_zero_measure,
    ← CycleJointProofs.factorialNormSq_order_zero_measure _ 1] at he
  exact he


end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual real torus scalar equation has an L²(H⁻¹) time derivative.
The derivative below is the H¹ Riesz representative of diffusion and transport;
its time membership follows from the native transport carrier, not an assumed
energy identity or moving-test formula. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

def weakScalarDriftC {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) : ℝ :=
  ((Fintype.card (DerivativeWord2 0) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖) *
    max 0 hd.bounded.choose

theorem weakScalarDrift_zero_bound {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (t : ℝ) (ht : t ∈ Icc a b) (l : Fin 1) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ weakScalarDriftC hd := by
  have hl : l.val = 0 := by omega
  rw [hl]
  have hh := Weighted.driftCoefficient_array_norm_le_iterated (v t) 0
    ((hd.smooth t ht).of_le (by simp)) x
  rw [norm_iteratedFDeriv_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    ((hd.bounded.choose_spec t ht x).trans (le_max_right _ _))
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg Weighted.driftCoefficientEmbedding)))


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def weakScalarTransportPath {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (w : ℝ → TorusHk 1 E) :
    ℝ → TorusHk 0 E :=
  plainTransportCarrierPath (fun _ : Unit => 0) a b v hd.smooth hd.periodic
    (fun _ _ => weakScalarDriftC hd) (fun t ht _ l x => weakScalarDrift_zero_bound hd t ht l x)
    (fun _ => w) ()

/-- The literal native transport of an L²(H¹) scalar curve lies in L²(H⁰). -/
theorem weak_scalar_transport_path_memLp {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (w : ℝ → TorusHk 1 E)
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    MemLp (weakScalarTransportPath hd w) 2 (volume.restrict (Icc a b)) := by
  exact plainTransportCarrierPath_memLp (fun _ : Unit => 0) a b v hd.smooth hd.periodic
    (fun _ _ => weakScalarDriftC hd) (fun t ht _ l x => weakScalarDrift_zero_bound hd t ht l x)
    hab 1 zero_lt_one
    (hd.measurable.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (max 0 hd.bounded.choose) (le_max_left _ _)
    (fun t ht x => (hd.bounded.choose_spec t ht x).trans (le_max_right _ _))
    (fun _ => w) (fun _ => hw) ()

/-- The H¹ Riesz representative of the actual diffusion and transport. -/
def weakScalarDualPath {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (w : ℝ → TorusHk 1 E) (t : ℝ) :
    TorusHk 1 E :=
  (-ν) • (torusH1GradientL2CLM (E := E)).adjoint (torusH1GradientL2CLM (E := E) (w t)) -
    (torusHkValueCLM (E := E) (K := 1)).adjoint
      (torusHkValueCLM (weakScalarTransportPath hd w t))

/-- No time differentiability is used to establish square integrability of the dual. -/
theorem weak_scalar_dual_path_memLp {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (w : ℝ → TorusHk 1 E)
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    MemLp (weakScalarDualPath hd w) 2 (volume.restrict (Icc a b)) := by
  have hg := ((torusH1GradientL2CLM (E := E)).adjoint.comp
    (torusH1GradientL2CLM (E := E))).comp_memLp' hw
  have ht := ((torusHkValueCLM (E := E) (K := 1)).adjoint.comp
    (torusHkValueCLM (E := E) (K := 0))).comp_memLp'
      (weak_scalar_transport_path_memLp hd hab w hw)
  simpa only [weakScalarDualPath, ContinuousLinearMap.comp_apply, Function.comp_def,
    Pi.sub_apply, Pi.smul_apply] using! (hg.const_smul (-ν)).sub ht

/-- The Riesz representative pairs with the genuine spatial weak form. -/
theorem weak_scalar_dual_path_pairing {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (w : ℝ → TorusHk 1 E) (t : ℝ) (φ : TorusHk 1 E) :
    inner ℝ (weakScalarDualPath hd w t) φ =
      -ν * inner ℝ (torusH1GradientL2CLM (E := E) (w t)) (torusH1GradientL2CLM (E := E) φ) -
        inner ℝ (torusHkValueCLM (weakScalarTransportPath hd w t)) (torusHkValueCLM φ) := by
  simp only [weakScalarDualPath, inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- The raw periodic weak spatial integrand and the native Riesz derivative
have exactly the same integral at every time of the window. -/
theorem weak_scalar_native_spatial_pairing_integrable {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (w : ℝ → TorusHk 1 E) (t : ℝ) (ht : t ∈ Icc a b) (φ : TorusHk 1 E) :
    Integrable (fun x =>
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube,
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      inner ℝ (weakScalarDualPath hd w t) φ := by
  have htr := torusTransportCarrier_value_ae (v t) (hd.smooth t ht) (hd.periodic t ht)
    (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) (w t)
  have htr' : (fun x => ∑ k : Fin 2, v t x k * inner ℝ
      ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
      (φ.toFunction.jet (valueIndex2 1) x)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => inner ℝ (torusHkValueCLM (weakScalarTransportPath hd w t) x)
        (torusHkValueCLM φ x) := by
    have hraw := ae_all_iff.mpr (fun k : Fin 2 =>
      torusRawJet_ae (w t) ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
    filter_upwards [htr, hraw, torusRawValue_ae φ] with x htx hwx hφx
    simp only [weakScalarTransportPath, plainTransportCarrierPath, dite_eq_left ht]
    change _ = inner ℝ
      ((torusTransportCarrier (v t) (hd.smooth t ht) (hd.periodic t ht)
        (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) (w t)).val
          (valueIndex2 0) x) (torusHkValueCLM φ x)
    rw [htx, sum_inner]
    apply Finset.sum_congr rfl
    intro k _
    rw [hwx k, hφx]
    change _ = inner ℝ (v t x k • ((w t).val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (torusHkValueCLM φ x)
    rw [real_inner_smul_left]
  have hgr : (fun x => ∑ k : Fin 2, inner ℝ
      ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => inner ℝ (torusH1GradientL2CLM (E := E) (w t) x) (torusH1GradientL2CLM (E := E) φ x) := by
    filter_upwards [torusRawTestGradient_ae (w t), torusRawTestGradient_ae φ] with x hwx hφx
    change inner ℝ
      (WithLp.toLp 2 (fun k : Fin 2 => (w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (WithLp.toLp 2 (fun k : Fin 2 => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) = _
    rw [hwx, hφx]
  have hiT := L2.integrable_inner (𝕜 := ℝ)
    (torusHkValueCLM (weakScalarTransportPath hd w t)) (torusHkValueCLM φ)
  have hiG := L2.integrable_inner (𝕜 := ℝ)
    (torusH1GradientL2CLM (E := E) (w t)) (torusH1GradientL2CLM (E := E) φ)
  constructor
  · refine (hiT.neg.sub (hiG.const_mul ν)).congr ?_
    filter_upwards [htr', hgr] with x htx hgx
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [htx, hgx]
  ·
    rw [weak_scalar_dual_path_pairing]
    calc
      _ = ∫ x in AVenhance.unitCube,
          -inner ℝ (torusHkValueCLM (weakScalarTransportPath hd w t) x) (torusHkValueCLM φ x) -
            ν * inner ℝ (torusH1GradientL2CLM (E := E) (w t) x) (torusH1GradientL2CLM (E := E) φ x) := by
        apply integral_congr_ae
        filter_upwards [htr', hgr] with x htx hgx
        rw [htx, hgx]
      _ = _ := by
        have hs := integral_sub hiT.neg (hiG.const_mul ν)
        simp only [Pi.neg_apply] at hs
        rw [hs, integral_neg, integral_const_mul,
          ← L2.inner_def, ← L2.inner_def]
        ring

theorem weak_scalar_native_spatial_pairing {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (w : ℝ → TorusHk 1 E) (t : ℝ) (ht : t ∈ Icc a b) (φ : TorusHk 1 E) :
    (∫ x in AVenhance.unitCube,
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      inner ℝ (weakScalarDualPath hd w t) φ :=
  (weak_scalar_native_spatial_pairing_integrable hd w t ht φ).2

/-- Every native order-zero scalar solution supplies the weak Hilbert time
curve, including its actual continuous values at both closed endpoints. -/
theorem weak_scalar_solution_hilbert_curve {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) {f : TorusHk 0 E}
    {u : ℝ → TorusHk 0 E} {w : ℝ → TorusHk 1 E}
    (hs : WeakScalarTorusSolution ν a b v 0 f u w) :
    WeakScalarHilbertCurve a b (fun t => torusHkValueCLM (u t))
      w (weakScalarDualPath hd w) := by
  refine ⟨torusHkValueCLM.continuous.comp_continuousOn (hs.1 0),
    hs.2.1 0, weak_scalar_dual_path_memLp hd hab w (hs.2.1 0), ?_, ?_⟩
  · filter_upwards [hs.2.2.1 0] with t ht
    rw [← ht]
    rfl
  · intro s hsa t hta hst φ
    have hleft := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left hta.2 hs
    have hright := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right hsa.1 hst hleft
    have hh := hright.2.2.2.2 0 t ⟨hst, le_rfl⟩ φ
    simp only [CoupledWeakIdentity, zero_apply, Finset.sum_const_zero] at hh
    have he := hh.2.2.2.2
    rw [intervalIntegral.integral_of_le hst]
    refine (congrArg₂ (· - ·) (torusRawValue_pairing_integrable_and_integral (u t) φ).2.symm
      (torusRawValue_pairing_integrable_and_integral (u s) φ).2.symm).trans
      (he.trans (integral_congr_ae ?_))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hz : (0 : TorusHk 0 E).toFunction.jet (valueIndex2 0) =ᵐ[
        volume.restrict AVenhance.unitCube] fun _ => 0 := by
      exact (torusRawValue_ae (0 : TorusHk 0 E)).trans (by
        simpa only [map_zero, Pi.zero_apply] using! (Lp.coeFn_zero (E := E) (p := 2)
          (μ := volume.restrict AVenhance.unitCube)))
    have hzv : (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))).toFunction.jet
        (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
      exact (torusRawValue_ae (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E)))).trans (by
        simpa only [map_zero, Pi.zero_apply] using! (Lp.coeFn_zero (E := PiLp 2 (fun _ : Fin 2 => E))
          (p := 2) (μ := volume.restrict AVenhance.unitCube)))
    rw [← weak_scalar_native_spatial_pairing hd w r
      ⟨hsa.1.trans hr.1.le, hr.2.trans hta.2⟩ φ]
    apply integral_congr_ae
    filter_upwards [hz, hzv] with x hx hxv
    simp only [hx, hxv, PiLp.zero_apply, inner_zero_left,
      Finset.sum_const_zero, sub_zero, add_zero]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Spatial adjoint cancellation for the native real scalar weak equation.
The proof is the finite Fourier approximation argument for the cell drift form,
applied to the actual Sobolev transport multiplier. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def weakScalarTransportMap {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (t : ℝ) (ht : t ∈ Icc a b) :
    TorusHk 1 E →L[ℝ] TorusHk 0 E :=
  (KernelEnergy.torusMultiplierCLM (driftFiberCoefficient (E := E) (v t))
    ((driftFiberCoefficient_contDiff (v t) (hd.smooth t ht)).of_le (by simp))
    (by intro n x; unfold driftFiberCoefficient driftCoefficient; rw [hd.periodic t ht n x])
    (fun _ => weakScalarDriftC hd)
    (fun l x => (driftFiberCoefficient_array_norm_le (v t) (hd.smooth t ht) l.val x).trans
      (weakScalarDrift_zero_bound hd t ht l x)) 1 zero_lt_one).comp
        (torusGradientTensorCLM (E := E) 0)

theorem weakScalarTransportMap_apply {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (t : ℝ) (ht : t ∈ Icc a b) (u : TorusHk 1 E) :
    weakScalarTransportMap hd t ht u = weakScalarTransportPath hd (fun _ => u) t := by
  simp only [weakScalarTransportMap, ContinuousLinearMap.comp_apply,
    torusGradientTensorCLM_apply, weakScalarTransportPath, plainTransportCarrierPath,
    dite_eq_left ht]
  rfl

def weakScalarTransportForm {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (t : ℝ) (ht : t ∈ Icc a b) :
    TorusHk 1 E →L[ℝ] TorusHk 1 E →L[ℝ] ℝ :=
  pullbackInnerCLM (torusHkValueCLM.comp (weakScalarTransportMap hd t ht)) torusHkValueCLM

theorem weak_scalar_transport_projection_zero {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (t : ℝ) (ht : t ∈ Icc a b) (u : TorusHk 1 E) (N : ℕ) :
    weakScalarTransportForm hd t ht (galerkinProj N u) (galerkinProj N u) = 0 := by
  let p := galerkinProj N u
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hz := periodic_hilbert_transport_energy_zero (v t)
    ((hd.smooth t ht).of_le (by simp)) (hd.periodic t ht) (hd.div t ht)
    q ((smoothFourierJet_contDiff N u _).of_le (by simp)) (smoothFourierJet_periodic N u _)
  have hval : torusHkValueCLM p =ᵐ[volume.restrict AVenhance.unitCube] q :=
    galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hgrad : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j : Fin 2,
      p.val ⟨⟨1, by decide⟩, fun _ => j⟩ x =
        smoothFourierJet (L := 1) N u ⟨⟨1, by decide⟩, fun _ => j⟩ x :=
    ae_all_iff.2 (fun j => galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩)
  have htr := torusTransportCarrier_value_ae (v t) (hd.smooth t ht) (hd.periodic t ht)
    (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) p
  change inner ℝ (torusHkValueCLM (weakScalarTransportMap hd t ht p)) (torusHkValueCLM p) = 0
  rw [weakScalarTransportMap_apply, L2.inner_def]
  calc
    _ = ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
        v t x j * inner ℝ (fderiv ℝ q x (basisVec j)) (q x) := by
      apply integral_congr_ae
      filter_upwards [htr, hval, hgrad] with x htx hx hg
      simp only [weakScalarTransportPath, plainTransportCarrierPath, dite_eq_left ht]
      change inner ℝ
        ((torusTransportCarrier (v t) (hd.smooth t ht) (hd.periodic t ht)
          (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) p).val
            (valueIndex2 0) x) (torusHkValueCLM p x) = _
      rw [htx, hx, sum_inner]
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_left, hg j]
      have hder := smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x
      change fderiv ℝ q x (basisVec j) = _ at hder
      rw [hder]
      rfl
    _ = 0 := hz

theorem weak_scalar_transport_energy_zero {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (t : ℝ) (ht : t ∈ Icc a b) (u : TorusHk 1 E) :
    weakScalarTransportForm hd t ht u u = 0 := by
  let B := weakScalarTransportForm (E := E) hd t ht
  have hc : Continuous (fun z : TorusHk 1 E => B z z) := B.continuous.clm_apply continuous_id
  have hlim := hc.continuousAt.tendsto.comp (galerkinProj_tendsto u)
  have he : (fun N => B (galerkinProj N u) (galerkinProj N u)) = fun _ : ℕ => 0 := by
    funext N
    exact weak_scalar_transport_projection_zero hd t ht u N
  change Tendsto (fun N => B (galerkinProj N u) (galerkinProj N u)) atTop (𝓝 (B u u)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem weak_scalar_transport_skew {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (t : ℝ) (ht : t ∈ Icc a b) (u z : TorusHk 1 E) :
    weakScalarTransportForm hd t ht u z = -weakScalarTransportForm hd t ht z u := by
  let B := weakScalarTransportForm (E := E) hd t ht
  have hu := weak_scalar_transport_energy_zero hd t ht u
  have hz := weak_scalar_transport_energy_zero hd t ht z
  have hs := weak_scalar_transport_energy_zero hd t ht (u + z)
  change B u u = 0 at hu
  change B z z = 0 at hz
  change B (u + z) (u + z) = 0 at hs
  simp only [map_add, add_apply, hu, hz] at hs
  change B u z = -B z u
  linarith

/-- Opposite velocities give opposite native transport forms; the two window
budgets may differ, since they do not change the represented multiplier. -/
theorem weak_scalar_transport_form_opposite {ν ρ a b a' b' : ℝ}
    {v v' : ℝ → Vec 2 → Vec 2} {Q Q' : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hd' : WeakScalarTorusDrift ν ρ a' b' v' Q')
    (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc a' b')
    (hv : v' s = fun x => -v t x) (u z : TorusHk 1 E) :
    weakScalarTransportForm hd' s hs u z = -weakScalarTransportForm hd t ht u z := by
  change inner ℝ (torusHkValueCLM (weakScalarTransportMap hd' s hs u)) (torusHkValueCLM z) =
    -inner ℝ (torusHkValueCLM (weakScalarTransportMap hd t ht u)) (torusHkValueCLM z)
  rw [weakScalarTransportMap_apply, weakScalarTransportMap_apply,
    L2.inner_def, L2.inner_def, ← integral_neg]
  have htr := torusTransportCarrier_value_ae (v t) (hd.smooth t ht) (hd.periodic t ht)
    (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) u
  have htr' := torusTransportCarrier_value_ae (v' s) (hd'.smooth s hs) (hd'.periodic s hs)
    (fun _ => weakScalarDriftC hd') (weakScalarDrift_zero_bound hd' s hs) u
  apply integral_congr_ae
  filter_upwards [htr, htr'] with x hx hx'
  simp only [weakScalarTransportPath, plainTransportCarrierPath, dite_eq_left ht, dite_eq_left hs]
  change inner ℝ
      ((torusTransportCarrier (v' s) (hd'.smooth s hs) (hd'.periodic s hs)
        (fun _ => weakScalarDriftC hd') (weakScalarDrift_zero_bound hd' s hs) u).val
          (valueIndex2 0) x) (torusHkValueCLM z x) =
    -inner ℝ
      ((torusTransportCarrier (v t) (hd.smooth t ht) (hd.periodic t ht)
        (fun _ => weakScalarDriftC hd) (weakScalarDrift_zero_bound hd t ht) u).val
          (valueIndex2 0) x) (torusHkValueCLM z x)
  rw [hx, hx', hv]
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, inner_neg_left]

/-- The forward generator and the time-reversed opposite-drift generator
cancel in their actual H¹/H⁻¹ cross pairing. -/
theorem weak_scalar_dual_adjoint_cancel {ν ρ a b a' b' : ℝ}
    {v v' : ℝ → Vec 2 → Vec 2} {Q Q' : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hd' : WeakScalarTorusDrift ν ρ a' b' v' Q')
    (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc a' b')
    (hv : v' s = fun x => -v t x)
    (w z : ℝ → TorusHk 1 E) :
    inner ℝ (weakScalarDualPath hd w t) (z s) +
      inner ℝ (-weakScalarDualPath hd' z s) (w t) = 0 := by
  have hskew := weak_scalar_transport_skew hd t ht (w t) (z s)
  have hopp := weak_scalar_transport_form_opposite hd hd' t ht s hs hv (z s) (w t)
  have hw : weakScalarTransportMap hd t ht (w t) = weakScalarTransportPath hd w t := by
    rw [weakScalarTransportMap_apply]
    simp only [weakScalarTransportPath, plainTransportCarrierPath, dite_eq_left ht]
  have hz : weakScalarTransportMap hd' s hs (z s) = weakScalarTransportPath hd' z s := by
    rw [weakScalarTransportMap_apply]
    simp only [weakScalarTransportPath, plainTransportCarrierPath, dite_eq_left hs]
  rw [inner_neg_left, weak_scalar_dual_path_pairing, weak_scalar_dual_path_pairing, ← hw, ← hz]
  change -ν * inner ℝ (torusH1GradientL2CLM (E := E) (w t))
      (torusH1GradientL2CLM (E := E) (z s)) - weakScalarTransportForm hd t ht (w t) (z s) +
    -(-ν * inner ℝ (torusH1GradientL2CLM (E := E) (z s))
      (torusH1GradientL2CLM (E := E) (w t)) - weakScalarTransportForm hd' s hs (z s) (w t)) = 0
  rw [real_inner_comm (torusH1GradientL2CLM (E := E) (z s)), hopp, hskew]
  ring

end AVRegularity.WeakEntryProofs
end
end

section
/-! Primitive reserves construct the actual molecular word family with every reserved parameter order. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_raw_Hilbert_regular_family_exists {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hN : N + 2 ≤ H) (P : MolecularData)
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (he : ∀ Y t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    (hs : ∀ t Y, (G t Y).IsSymm)
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    (hf : ∀ t Y, fieldCellMean (fun z => f t z Y) = 0) :
    ∃ c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ,
    ∃ Q : Vec d → MolecularData,
      (∀ Y, (Q Y).G = fun t => G t Y) ∧ (∀ Y, (Q Y).v = P.v) ∧
      (∀ Y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (Q Y))
        (fun t => cellQ0 (coordinateSourceWord f w Y t))
        (coordinateSourceWord F w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y)) ∧
      (∀ Y w, w.length ≤ N → cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] 0) ∧
      (∀ w, ∀ r : ℕ, w.length + r ≤ N → ∀ t ∈ Icc a b,
        ContDiff ℝ (r : ℕ∞) (fun Y => cellRawTrace (c w Y) t)) ∧
      ∀ w, w.length < N → ∀ Y i t, t ∈ Icc a b →
        Tendsto (fun h : ℝ => h⁻¹ • (cellRawTrace (c w (Y + h • basisVec i)) t -
          cellRawTrace (c w Y) t) - cellRawTrace (c (i :: w) Y) t) (𝓝[≠] 0) (𝓝 0) := by
  let Gj := fun (w : List (Fin d)) t Y =>
    independentMetricWordJet G w.length (coordinateWordDirections w) Y t
  have hnil : Gj [] = G := by
    funext t Y i j
    exact iteratedFDeriv_zero_apply _
  have hreg (w : List (Fin d)) (_hw : w.length ≤ N) t i j :
      ContDiff ℝ 2 (fun X => Gj w t X i j) :=
    coordinate_metric_word_parameter_regular hr w 2 t i j
  have hmeas (w : List (Fin d)) X i j : Measurable (fun t => Gj w t X i j) :=
    general_metric_word_entry_measurable hr hm w.length (coordinateWordDirections w) X i j
  have hbound (w : List (Fin d)) (hw : w.length ≤ N) t X i j :
      |Gj w t X i j| ≤ B w.length :=
    general_metric_word_entry_bound hr B hb w.length (by omega) _ (coordinateWordDirections_norm w) X t i j
  have hcoerce X t (ξ : Vec 2) : (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, Gj [] t X i j * ξ i * ξ j := by rw [hnil]; exact he X t ξ
  let Q := fun X => molecularMetricReplacement P (fun t => Gj [] t X) (B 0)
    (hmeas [] X) (fun t => hbound [] (by simp) t X) (hcoerce X)
  obtain ⟨c, hc⟩ := coordinate_word_window_family_exists hab N (by omega) Q hr hm B hB hb Qf QF
  have hcur := coordinate_word_raw_Hilbert_curves hab N (by omega) Q hr hm hs B hB hb Qf QF hf c
    (fun Y w hw => (hc Y w hw).1) (fun Y w hw => (hc Y w hw).2)
  let QFc := fun j : Fin 2 => QF.map (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j)
  have hfirst (w : List (Fin d)) (hw : w.length ≤ N) t i j X :
      ‖fderiv ℝ (fun Y => Gj w t Y i j) X‖ ≤ B (w.length + 1) := by
    have hh := general_metric_word_derivative_bound hr B hb w.length 1 (by omega)
      (coordinateWordDirections w) (coordinateWordDirections_norm w) X t i j
    simpa only [norm_iteratedFDeriv_one] using hh
  have hsecond (w : List (Fin d)) (hw : w.length ≤ N) t i j X :
      ‖fderiv ℝ (fderiv ℝ (fun Y => Gj w t Y i j)) X‖ ≤ B (w.length + 2) :=
    coordinate_metric_word_parameter_second_bound hr B hb w (by omega) t i j X
  have hcons (w : List (Fin d)) (_hw : w.length < N) i t Y :
      Gj (i :: w) t Y = Matrix.of (fun j k => fderiv ℝ (fun X => Gj w t X j k) Y (basisVec i)) :=
    coordinate_metric_word_parameter_cons hr w i t Y
  have hregular := molecular_primitive_word_Hilbert_family_contDiff hab N hN P Gj
    (fun w => B w.length) (fun w => B (w.length + 1)) (fun w => B (w.length + 2))
    (fun _ _ => hB _) hreg hmeas hbound hcoerce hfirst hsecond hcons Qf QFc
    (fun w Y => cellRawTrace (c w Y)) (fun w Y => cellH1Slice (c w Y))
    (fun w hw Y => (hcur w hw Y).1) (fun w hw Y => (hcur w hw Y).2)
  have hder := molecular_primitive_word_Hilbert_family_derivatives hab N hN P Gj
    (fun w => B w.length) (fun w => B (w.length + 1)) (fun w => B (w.length + 2))
    (fun _ _ => hB _) hreg hmeas hbound hcoerce hfirst hsecond hcons Qf QFc
    (fun w Y => cellRawTrace (c w Y)) (fun w Y => cellH1Slice (c w Y))
    (fun w hw Y => (hcur w hw Y).1) (fun w hw Y => (hcur w hw Y).2)
  refine ⟨c, Q, ?_, fun _ => rfl, (fun Y w hw => (hc Y w hw).1),
    (fun Y w hw => (hc Y w hw).2), hregular, ?_⟩
  · intro Y
    change (fun t => Gj [] t Y) = fun t => G t Y
    rw [hnil]
  · intro w hw Y i t ht
    exact (hder w hw Y i).1 t ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! Native scalar adjoint pairing and negative-order propagation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open Filter
open scoped Topology
namespace AVRegularity.WeakEntryProofs

/-- Restrict a native drift budget in time and in finite jet order. -/
def WeakScalarTorusDrift.restrict {ν ρ a b c d : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Q P : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hsub : Set.Icc c d ⊆ Set.Icc a b) (hP : P ≤ Q) :
    WeakScalarTorusDrift ν ρ c d v P :=
  { hd with
    bounded := ⟨hd.bounded.choose, fun t ht => hd.bounded.choose_spec t (hsub ht)⟩
    smooth := fun t ht => hd.smooth t (hsub ht)
    div := fun t ht => hd.div t (hsub ht)
    periodic := fun t ht => hd.periodic t (hsub ht)
    jets := fun l hl hlP t ht => hd.jets l hl (hlP.trans hP) t (hsub ht) }

theorem weak_scalar_ordered_coefficient_neg
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (fun x => -C x) j w =
      fun x => -orderedCoefficientDerivative C j w x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [orderedCoefficientDerivative, ih, fderiv_fun_neg, neg_apply]

theorem weak_scalar_coefficient_array_neg
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun y => -C y) j x = -coefficientDerivativeArray C j x := by
  ext e w
  simp only [coefficientDerivativeArray_apply, weak_scalar_ordered_coefficient_neg,
    neg_apply, PiLp.neg_apply]

/-- Time reversal and the adjoint drift sign preserve the literal scalar drift
budget, with exactly the same amplitude, radius, length and finite jet cap. -/
def WeakScalarTorusDrift.reflected {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) :
    WeakScalarTorusDrift ν ρ (-b) (-a) (fun t x => -v (-t) x) Q := by
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (-b) (-a)) : -t ∈ Set.Icc a b :=
    ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  refine {
    hd with
    measurable := (hd.measurable.comp ((measurable_fst.neg).prodMk measurable_snd)).neg
    bounded := by
      obtain ⟨V, hV⟩ := hd.bounded
      exact ⟨V, fun t ht x => by rw [norm_neg]; exact hV (-t) (hmem t ht) x⟩
    smooth := fun t ht => (hd.smooth (-t) (hmem t ht)).neg
    div := ?_
    periodic := ?_
    jets := ?_ }
  · intro t ht x
    simpa only [fderiv_fun_neg, neg_apply, Pi.neg_apply,
      Finset.sum_neg_distrib, neg_eq_zero] using hd.div (-t) (hmem t ht) x
  · intro t ht k x
    change -v (-t) (x + AVenhance.latticeShift k) = -v (-t) x
    rw [hd.periodic (-t) (hmem t ht) k x]
  · intro j hj hjQ t ht x
    have hneg : driftCoefficient (fun y => -v (-t) y) =
        fun y => -driftCoefficient (v (-t)) y := by
      funext y
      rw [← Weighted.driftCoefficientEmbedding_apply, map_neg,
        Weighted.driftCoefficientEmbedding_apply]
    rw [hneg, AVRegularity.WeakEntryProofs.weak_scalar_coefficient_array_neg, norm_neg]
    exact hd.jets j hj hjQ (-t) (hmem t ht) x

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A negative factorial Sobolev bound, expressed by all genuine positive-order
tests. The pairing is the actual order-zero periodic Hilbert pairing. -/
def WeakScalarNegativeBound (ρ : ℝ) (Q : ℕ) (f : TorusHk 0 E) (N : ℝ) : Prop :=
  ∀ φ : TorusHk Q E,
    |inner ℝ f (truncateTorusHk (Nat.zero_le Q) φ)| ≤
      N * Real.sqrt (factorialNormSq ρ φ.val)

/-- Moving adjoint tests for the actual real torus scalar weak equation. Time
reversal is literal, including its drift sign and its two closed endpoints. -/
def WeakScalarAdjointPairStatement : Prop :=
  ∀ {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} (Q : ℕ), a ≤ b →
    WeakScalarTorusDrift ν ρ a b v Q →
    ∀ {f : TorusHk 0 E} {u : ℝ → TorusHk 0 E} {w : ℝ → TorusHk 1 E},
    WeakScalarTorusSolution ν a b v 0 f u w →
    ∀ {g : TorusHk Q E} {z : ℝ → TorusHk Q E} {zw : ℝ → TorusHk (Q + 1) E},
    WeakScalarTorusSolution ν (-b) (-a) (fun t x => -v (-t) x) Q g z zw →
    inner ℝ (u b) (truncateTorusHk (Nat.zero_le Q) (z (-b))) =
      inner ℝ (u a) (truncateTorusHk (Nat.zero_le Q) (z (-a)))

omit [FiniteDimensional ℝ E] in
theorem weak_scalar_zero_inner (u z : TorusHk 0 E) :
    inner ℝ u z = inner ℝ
      (CoupledEnergy.Galerkin.torusHkValueCLM u) (CoupledEnergy.Galerkin.torusHkValueCLM z) := by
  classical
  change inner ℝ u.val z.val = _
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_single (valueIndex2 0)
  · intro j _ hj
    exact (hj (CycleJointProofs.zeroJetIndex_eq j)).elim
  · simp

/-- Moving adjoint pairing for genuine native scalar solutions, proved from
their weak time equations and spatial cancellation on the closed window. -/
theorem weak_scalar_adjoint_pair : WeakScalarAdjointPairStatement (E := E) := by
  intro ν ρ a b v Q hab hd f u w hu g z zw hz
  let z0 := fun t => truncateTorusHk (E := E) (Nat.zero_le Q) (z t)
  let z1 := fun t => truncateTorusHk (E := E) (Nat.succ_le_succ (Nat.zero_le Q)) (zw t)
  have hz0 := weak_scalar_torus_solution_truncate (Nat.zero_le Q) hz
  have hf := weak_scalar_solution_hilbert_curve hd hab hu
  have ha := weak_scalar_solution_hilbert_curve hd.reflected (neg_le_neg hab) hz0
  have hb : WeakScalarHilbertCurve a b (fun t => torusHkValueCLM (z0 (-t)))
      (fun t => z1 (-t)) (fun t => -weakScalarDualPath hd.reflected z1 (-t)) := by
    simpa only [neg_neg] using! ha.timeReverse
  have he := hf.pairing_increment hab hb
  have hi : (∫ t in a..b, inner ℝ (weakScalarDualPath hd w t) (z1 (-t)) +
      inner ℝ (-weakScalarDualPath hd.reflected z1 (-t)) (w t)) = 0 := by
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact weak_scalar_dual_adjoint_cancel hd hd.reflected t ht (-t)
          ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
          (by funext x; simp only [neg_neg]) w z1
      _ = 0 := intervalIntegral.integral_zero
  rw [hi] at he
  change inner ℝ (torusHkValueCLM (u b))
      (torusHkValueCLM (truncateTorusHk (E := E) (Nat.zero_le Q) (z (-b)))) -
    inner ℝ (torusHkValueCLM (u a))
      (torusHkValueCLM (truncateTorusHk (E := E) (Nat.zero_le Q) (z (-a)))) = 0 at he
  rw [← weak_scalar_zero_inner, ← weak_scalar_zero_inner] at he
  exact sub_eq_zero.mp he

end AVRegularity.WeakEntryProofs
end
end

section
/-! The genuine scalar evolution as a continuous linear map. Existence and
uniqueness come from the native torus equation; the unweighted bound is used
only for continuity, while the factorial estimate keeps its radius uniform. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Subtraction preserves the literal homogeneous scalar equation. -/
theorem weak_scalar_torus_solution_sub {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K : ℕ} {f g : TorusHk K E} {u z : ℝ → TorusHk K E}
    {w zw : ℝ → TorusHk (K + 1) E}
    (hu : WeakScalarTorusSolution ν a b v K f u w)
    (hz : WeakScalarTorusSolution ν a b v K g z zw) :
    WeakScalarTorusSolution ν a b v K (f - g)
      (fun t => u t - z t) (fun t => w t - zw t) := by
  simpa only [WeakScalarTorusSolution, Providers.WeakGen.Comparison.IsTorusForcedRow,
    sub_self] using CycleComparison.Error.isCoupledWeakSolutionTorus_sub hu hz

/-- A chosen native trajectory, including its actual gradient lift. -/
structure WeakScalarTorusTrajectory (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (K : ℕ) (f : TorusHk K E) where
  value : ℝ → TorusHk K E
  gradient : ℝ → TorusHk (K + 1) E
  solution : WeakScalarTorusSolution ν a b v K f value gradient

/-- Choose the already constructed native solution, with no new PDE input. -/
def weakScalarTorusTrajectory {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (f : TorusHk K E) : WeakScalarTorusTrajectory ν a b v K f := by
  let he := (weak_scalar_torus_exists_unique hK hd hab f).1
  exact ⟨he.choose, he.choose_spec.choose, he.choose_spec.choose_spec⟩

/-- Uniform propagation in the factorial norm, at every closed-window time. -/
theorem weak_scalar_torus_factorial_bound {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    {f : TorusHk K E} {u : ℝ → TorusHk K E} {w : ℝ → TorusHk (K + 1) E}
    (hs : WeakScalarTorusSolution ν a b v K f u w)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    factorialNormSq ρ (u t).val ≤ 2 * factorialNormSq ρ f.val := by
  have he := weak_scalar_torus_restarted_energy hK hd hs a t le_rfl ht.1 ht.2
  have hg : 0 ≤ ν / 2 * (∫ s in a..t, gradFactorialNormSq ρ (w s).val) :=
    mul_nonneg (div_nonneg hd.nu_pos.le (by norm_num))
      (intervalIntegral.integral_nonneg ht.1 fun _ _ =>
        CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
  have hh := (le_add_of_nonneg_right hg).trans he
  have hinit : u a = f := hs.2.2.2.1 0
  rwa [hinit] at hh

/-- A finite unweighted bound, used solely to establish continuity of the
chosen solution map. Its radius dependence never enters a path price. -/
theorem weak_scalar_torus_norm_bound {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    {f : TorusHk K E} {u : ℝ → TorusHk K E} {w : ℝ → TorusHk (K + 1) E}
    (hs : WeakScalarTorusSolution ν a b v K f u w)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ‖u t‖ ≤ Real.sqrt (2 * factorialWeightMax ρ K / factorialWeightMin ρ K) * ‖f‖ := by
  have hm : 0 < factorialWeightMin ρ K := factorialWeightMin_pos ρ hd.radius_pos
  have he := weak_scalar_torus_factorial_bound hK hd hs ht
  have hl := factorialNormSq_lower ρ (u t).val
  have hu := factorialNormSq_upper ρ f.val
  have hmax : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans
      (factorialWeight_le_max ρ (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)))
  have hh : ‖u t‖ ^ 2 ≤
      (2 * factorialWeightMax ρ K / factorialWeightMin ρ K) * ‖f‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).2
    have hb := hl.trans (he.trans (mul_le_mul_of_nonneg_left hu (by norm_num)))
    change factorialWeightMin ρ K * ‖u t‖ ^ 2 ≤
      2 * (factorialWeightMax ρ K * ‖f‖ ^ 2) at hb
    nlinarith only [hb]
  have hh' := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg _)] at hh'
  exact hh'

/-- The native endpoint map is additive, by uniqueness and subtraction. -/
def weakScalarTorusEvolutionAdd {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (t : ℝ) (ht : t ∈ Set.Icc a b) : TorusHk K E →+ TorusHk K E :=
  AddMonoidHom.ofMapSub (fun f => (weakScalarTorusTrajectory hK hd hab f).value t) (by
    intro f g
    let uf := weakScalarTorusTrajectory hK hd hab f
    let ug := weakScalarTorusTrajectory hK hd hab g
    let ud := weakScalarTorusTrajectory hK hd hab (f - g)
    exact (weak_scalar_torus_exists_unique hK hd hab (f - g)).2 _ _ _ _
      ud.solution (weak_scalar_torus_solution_sub uf.solution ug.solution) t ht)

/-- The actual scalar endpoint operator. Continuity plus additivity gives
real linearity, avoiding a second proof of the native scalar weak identity. -/
def weakScalarTorusEvolution {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hK : K ≤ Q) (hd : WeakScalarTorusDrift ν ρ a b v Q)
    (hab : a ≤ b) (t : ℝ) (ht : t ∈ Set.Icc a b) : TorusHk K E →L[ℝ] TorusHk K E :=
  (weakScalarTorusEvolutionAdd hK hd hab t ht).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound _
      (Real.sqrt (2 * factorialWeightMax ρ K / factorialWeightMin ρ K))
      (fun f => weak_scalar_torus_norm_bound hK hd
        (weakScalarTorusTrajectory hK hd hab f).solution ht))

/-- All subwindow endpoint operators of one drift. Only the genuine ordered
subwindows are used; elsewhere the operator is extended by zero. -/
def weakScalarTorusForward {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (K : ℕ) (s t : ℝ) :
    TorusHk K E →L[ℝ] TorusHk K E :=
  if hw : K ≤ Q ∧ a ≤ s ∧ s ≤ t ∧ t ≤ b then
    weakScalarTorusEvolution hw.1
      (hd.restrict (Set.Icc_subset_Icc hw.2.1 hw.2.2.2) le_rfl)
      hw.2.2.1 t ⟨hw.2.2.1, le_rfl⟩
  else 0

/-- Each actual forward operator retains a native solution and gradient lift
on its exact closed subwindow. -/
theorem weak_scalar_torus_forward_native {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {K Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (hK : K ≤ Q)
    (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (f : TorusHk K E) :
    ∃ u w, WeakScalarTorusSolution ν s t v K f u w ∧
      weakScalarTorusForward hd K s t f = u t := by
  let ht := hd.restrict (Set.Icc_subset_Icc has htb) le_rfl
  let z := weakScalarTorusTrajectory hK ht hst f
  refine ⟨z.value, z.gradient, z.solution, ?_⟩
  rw [weakScalarTorusForward, dite_eq_left ⟨hK, has, hst, htb⟩]
  rfl

/-- The forward subwindow map agrees with every native trajectory on it. -/
theorem weak_scalar_torus_forward_eq {ν ρ a b s t : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {K Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (hK : K ≤ Q)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    {f : TorusHk K E} {u : ℝ → TorusHk K E} {w : ℝ → TorusHk (K + 1) E}
    (hs : WeakScalarTorusSolution ν s t v K f u w) :
    weakScalarTorusForward hd K s t f = u t := by
  obtain ⟨z, zw, hz, he⟩ := weak_scalar_torus_forward_native hd hK s t has hst htb f
  exact he.trans ((weak_scalar_torus_exists_unique hK
    (hd.restrict (Set.Icc_subset_Icc has htb) le_rfl) hst f).2 _ _ _ _ hz hs t
      ⟨hst, le_rfl⟩)

end AVRegularity.WeakEntryProofs
end
end
