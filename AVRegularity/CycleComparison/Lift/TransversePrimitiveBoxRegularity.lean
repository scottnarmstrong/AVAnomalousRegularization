-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.FiniteOperatorFinsetSynthesis
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
public import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.CellInverseZero
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Term coefficients have the same exact slow/fast reserve as the literal covariant coefficient. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantLeftTermList_box (η : ℝ) (w : List (Fin 2)) (l : List (LeftTerm E F)) :
    ∀ j p q, j ≤ w.length →
      (∀ c ∈ l, IsBoxSmooth (p + j) (q + w.length - j) c.coeff) →
      ∀ c ∈ covariantLeftTermList η w l j, IsBoxSmooth p q c.coeff := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j p q hj hl c hc
    have hj0 : j = 0 := by simpa using hj
    subst j
    simp only [covariantLeftTermList_nil, ite_true] at hc
    simpa only [Nat.add_zero, List.length_nil, Nat.sub_zero] using hl c hc
  | append_singleton w k ih =>
    intro j p q hj hl
    have hj' : j ≤ w.length + 1 := by simpa using hj
    rw [covariantLeftTermList_append_singleton]
    apply covariantLeftTermStep_box η k _ j p q
    · by_cases hjw : j ≤ w.length
      · apply ih j p (q + 1) hjw
        have he : q + 1 + w.length - j = q + (w ++ [k]).length - j := by
          simp only [List.length_append, List.length_singleton]
          omega
        simpa only [he] using hl
      · rw [covariantLeftTermList_above_degree η w l j (by omega)]
        intro c hc
        exact (List.not_mem_nil hc).elim
    · intro hj0
      apply ih (j - 1) (p + 1) q (by omega)
      have hep : p + 1 + (j - 1) = p + j := by omega
      have heq : q + w.length - (j - 1) = q + (w ++ [k]).length - j := by
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [hep, heq] using hl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Globally measurable Fourier forcing for the first lift, from the original fast data. -/

def clampedFirstSourceProfile (η : ℝ) (V : ℝ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (c : ℝ) : ℝ → ℝ → ℂ := fun t x =>
  ((-(Real.sqrt η * V (Set.projIcc a b hab t) x) * c : ℝ) : ℂ)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_first_clamped_profile_measurable (c : ℝ) :
    Measurable (Function.uncurry (clampedFirstSourceProfile Q.η V a b P.window c)) := by
  have hp := (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have hv := measurable_uncurry_of_continuous_of_measurable
    (u := fun x t => V (Set.projIcc a b P.window t) x)
    (fun t => (P.V_smooth _ (Set.projIcc a b P.window t).2).continuous)
    (fun x => (setting_shear_profile_measurable P x).comp hp)
  have hm : Measurable (fun p : ℝ × ℝ =>
      -(Real.sqrt Q.η * V (Set.projIcc a b P.window p.1) p.2) * c) :=
    (measurable_const.mul (hv.comp measurable_swap)).neg.mul measurable_const
  simpa only [Function.uncurry, clampedFirstSourceProfile] using!
    Complex.ofRealCLM.continuous.measurable.comp hm

include P in
theorem setting_first_clamped_profile_jets (c : ℝ) :
    ∃ C : ℕ → ℝ, (∀ j ≤ qf, 0 ≤ C j) ∧
      ∀ j ≤ qf, ∀ t x,
        ‖iteratedDeriv j (clampedFirstSourceProfile Q.η V a b P.window c t) x‖ ≤ C j := by
  obtain ⟨C, hC, hb⟩ := setting_first_diagonal_profile_jets P c
  exact ⟨C, hC, fun j hj t x => hb j hj _ (Set.projIcc a b P.window t).2 x⟩

include P in
theorem setting_first_clamped_profile_contDiff (c : ℝ) (t : ℝ) :
    ContDiff ℝ (qf : ℕ∞) (clampedFirstSourceProfile Q.η V a b P.window c t) := by
  have hh : ContDiff ℝ (qf : ℕ∞) (fun x =>
      -(Real.sqrt Q.η * V (Set.projIcc a b P.window t) x) * c) :=
    (contDiff_const.mul (P.V_smooth _ (Set.projIcc a b P.window t).2)).neg.mul contDiff_const
  simpa only [clampedFirstSourceProfile, Function.comp_def] using!
    Complex.ofRealCLM.contDiff.comp hh

include P in
theorem setting_first_clamped_profile_periodic (c : ℝ) (t : ℝ) :
    Function.Periodic (clampedFirstSourceProfile Q.η V a b P.window c t) 1 := by
  intro x
  simp only [clampedFirstSourceProfile, P.V_per _ (Set.projIcc a b P.window t).2 x]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Restricting coefficient changes to times outside the cell window preserves the actual inverse relation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem cellFieldInverse_coefficients_congr_on
    (G G' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v v' : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (a b : ℝ) (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hG : ∀ t ∈ Set.Icc a b, G t = G' t)
    (hv : ∀ t ∈ Set.Icc a b, v t = v' t)
    (hc : IsCellFieldInverse G v sZ a b c0 g c) :
    IsCellFieldInverse G' v' sZ a b c0 g c := by
  refine ⟨hc.1, ?_⟩
  intro l
  refine ⟨?_, (hc.2 l).2⟩
  exact cellSolution_coefficients_congr (fun t _ => G t) (fun t _ => G' t) v v'
    (fun t ht => congrArg (fun A _ => A) (hG t ht).symm) (fun t ht => (hv t ht).symm) _ _ _ (hc.2 l).1

theorem cellFieldInverse_local_coefficients
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 g c) :
    IsCellFieldInverse (fun t => G (Set.projIcc a b hab t))
      (localCellDrift a b hab v) sZ a b c0 g c := by
  apply cellFieldInverse_coefficients_congr_on G _ v _ sZ a b c0 g c _ _ hc
  · intro t ht
    rw [Set.projIcc_of_mem hab ht]
  · intro t ht
    exact (localCellDrift_eq a b hab v t ht).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The zeroth fast jet of a coordinate primitive retains the source's reserved slow jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def transversePrimitiveField (p : Fin 2) (f : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => centeredIntervalPrimitive (fun r => f X (r • basisVec p)) (z p)

theorem transversePrimitiveField_slow_regularities
    (p : Fin 2) (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth sX sZ f)
    (C : ℕ → ℝ)
    (hb : ∀ j ≤ sX, ∀ (r : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y => f Y (r • basisVec p)) X‖ ≤ C j) :
    (∀ z, ContDiff ℝ (sX : ℕ∞) (fun X => transversePrimitiveField p f X z)) ∧
    ∀ j ≤ sX, Continuous (fun x : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ j (fun X => transversePrimitiveField p f X x.2) x.1) := by
  let g : ℝ → Vec 2 → E := fun r X => f X (r • basisVec p)
  have hfast (X : Vec 2) : Continuous (fun r => g r X) :=
    (hf.1 X).continuous.comp (continuous_id.smul continuous_const)
  have hslow (r : ℝ) : ContDiff ℝ (sX : ℕ∞) (g r) :=
    boxSmooth_slow_contDiff hf (r • basisVec p)
  have hg : Continuous (Function.uncurry g) :=
    (boxSmooth_continuous hf).comp
      (continuous_snd.prodMk (continuous_fst.smul continuous_const))
  have hjoint (j : ℕ) (hj : j ≤ sX) :
      Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ j (g x.2) x.1) :=
    (boxSmooth_slow_jet_continuous hf j hj).comp
      (continuous_fst.prodMk (continuous_snd.smul continuous_const))
  refine ⟨fun z => parameter_centeredIntervalPrimitive_contDiff sX g hfast hslow C hb (z p), ?_⟩
  intro j hj
  exact (parameter_centeredIntervalPrimitive_slow_joint_jets sX g hg hslow C hb hjoint j hj).comp
    (continuous_fst.prodMk ((continuous_apply p).comp continuous_snd))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The literal zero-start Duhamel response has its reserved slow parameter regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeResponse_parameter_contDiff (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j) :
    ContDiff ℝ (n : ℕ∞)
      (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) := by
  let F := fun s Y => transverseModeKernel rate (fun t => g t Y)
    (projIcc a b hab s) b • f (projIcc a b hab s) Y
  have hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b) := by
    intro X
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (by omega) t X)
  have hF : ∀ s, ContDiff ℝ (n : ℕ∞) (F s) := by
    intro s
    exact (transverseModeKernel_parameter_contDiff n g hm hs (fun j => M * lam ^ j)
      hb rate (projIcc a b hab s) b).smul (hf _)
  have hme : ∀ X, Measurable (fun s => F s X) :=
    fun X => clamped_duhamel_measurable g f hmf rate a b hab hi X
  have hI : ContDiff ℝ (n : ℕ∞) (fun X => ∫ s, F s X ∂volume.restrict (Ioc a b)) := by
    apply parameter_integral_contDiff (volume.restrict (Ioc a b)) n F hme hF
      (fun q => ((∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) *
        (1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q)) * lam ^ q)
    intro q hq s X
    exact clamped_duhamel_uniform_jet_bound n g hm hs M lam rate κ a b
      hM hlam hrate hκ hab hb hgl f hf S hS hfB q hq s X
  have he : (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) =
      fun X => ∫ s, F s X ∂volume.restrict (Ioc a b) := by
    funext X
    rw [transverseModeResponse, intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [F, projIcc_of_mem hab (show s ∈ Icc a b from ⟨hs.1.le, hs.2⟩)]
  rw [he]
  exact hI

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Paired cross differences separate the field difference from a single metric perturbation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_paired_difference (η : ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 1 1 f) (hg : IsBoxSmooth 1 1 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => J t X i j)) (X z : Vec 2) :
    cellB1 η G v t f X z - cellB1 η J v t g X z =
      cellB1 η G v t (fun Y y => f Y y - g Y y) X z +
        cellB1 η (fun s Y i j => G s Y i j - J s Y i j) (fun _ _ => 0) t g X z := by
  have he : (fun s Y i j => J s Y i j + (G s Y i j - J s Y i j)) = G := by
    funext s Y i j
    ring
  have hadd := congrFun (congrFun (cellB1_metric_add η J
    (fun s Y i j => G s Y i j - J s Y i j) v t g hg hJ
    (fun i j => (hG i j).sub (hJ i j))) X) z
  rw [he] at hadd
  rw [cellB1_field_sub η G v t f g hf hg hG X z, hadd]
  abel

theorem cellB2_paired_difference (η : ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 2 0 f) (hg : IsBoxSmooth 2 0 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => J t X i j)) (X z : Vec 2) :
    cellB2 η G t f X z - cellB2 η J t g X z =
      cellB2 η G t (fun Y y => f Y y - g Y y) X z +
        cellB2 η (fun s Y i j => G s Y i j - J s Y i j) t g X z := by
  have he : (fun s Y i j => J s Y i j + (G s Y i j - J s Y i j)) = G := by
    funext s Y i j
    ring
  have hadd := congrFun (congrFun (cellB2_metric_add η J
    (fun s Y i j => G s Y i j - J s Y i j) t g hg hJ
    (fun i j => (hG i j).sub (hJ i j))) X) z
  rw [he] at hadd
  rw [cellB2_field_sub η G t f g hf hg hG X z, hadd]
  abel

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Measurability, slow regularity and a common jet bound for the actual response integrand. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem clamped_duhamel_reserve_data (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j) :
    (∀ X, Measurable (fun s => clampedDuhamelField rate g f a b hab s X)) ∧
    (∀ s, ContDiff ℝ (n : ℕ∞) (clampedDuhamelField rate g f a b hab s)) ∧
    (∀ q ≤ n, ∀ s X, ‖iteratedFDeriv ℝ q (clampedDuhamelField rate g f a b hab s) X‖ ≤
      duhamelSlowJetMajorant n M κ S q * lam ^ q) := by
  have hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b) := by
    intro X
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (by omega) t X)
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact clamped_duhamel_measurable g f hmf rate a b hab hi X
  · intro s
    exact (transverseModeKernel_parameter_contDiff n g hm hs (fun j => M * lam ^ j)
      hb rate (projIcc a b hab s) b).smul (hf _)
  · intro q hq s X
    exact clamped_duhamel_uniform_jet_bound n g hm hs M lam rate κ a b
      hM hlam hrate hκ hab hb hgl f hf S hS hfB q hq s X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite left terms represent the actual covariant coefficient on every smooth coarse input. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantLeftTermList_apply (η : ℝ) (w : List (Fin 2)) (l : List (LeftTerm E F))
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ j, (∀ c ∈ l, IsBoxSmooth j (w.length - j) c.coeff) →
      leftTermsApply (covariantLeftTermList η w l j) f =
        covariantListCoefficients η w (leftTermsApply l f) j := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j _
    rw [covariantLeftTermList_nil, covariantListCoefficients_nil]
    by_cases hj : j = 0
    · simp only [ite_eq_left hj]
    · simp only [ite_eq_right hj, leftTermsApply_nil]
  | append_singleton w k ih =>
    intro j hl
    by_cases hj : j ≤ w.length + 1
    · have hfast : ∀ c ∈ covariantLeftTermList η w l j, IsBoxSmooth 0 1 c.coeff := by
        by_cases hjw : j ≤ w.length
        · apply covariantLeftTermList_box η w l j 0 1 hjw
          have he : 1 + w.length - j = (w ++ [k]).length - j := by
            simp only [List.length_append, List.length_singleton]
            omega
          simpa only [zero_add, he] using hl
        · rw [covariantLeftTermList_above_degree η w l j (by omega)]
          intro c hc
          exact (List.not_mem_nil hc).elim
      have hslow : j ≠ 0 → ∀ c ∈ covariantLeftTermList η w l (j - 1),
          IsBoxSmooth 1 0 c.coeff := by
        intro hj0
        apply covariantLeftTermList_box η w l (j - 1) 1 0 (by omega)
        have hep : 1 + (j - 1) = j := by omega
        have heq : w.length - (j - 1) = (w ++ [k]).length - j := by
          simp only [List.length_append, List.length_singleton]
          omega
        simpa only [hep, zero_add, heq] using hl
      have hefast : leftTermsApply (covariantLeftTermList η w l j) f =
          covariantListCoefficients η w (leftTermsApply l f) j :=
        ih j (fun c hc => (hl c hc).mono le_rfl (by simp only [List.length_append, List.length_singleton]; omega))
      rw [covariantLeftTermList_append_singleton,
        covariantLeftTermStep_apply η k _ j hfast hslow f hf,
        covariantListCoefficients_append_singleton]
      by_cases hj0 : j = 0
      · funext X z
        simp only [covariantCoefficientStep, hefast, ite_eq_left hj0]
      · have heq : w.length - (j - 1) = (w ++ [k]).length - j := by
          simp only [List.length_append, List.length_singleton]
          omega
        have heslow := ih (j - 1) (fun c hc => (hl c hc).mono (by omega) (by omega))
        funext X z
        simp only [covariantCoefficientStep, hefast, heslow, ite_eq_right hj0]
    · rw [covariantLeftTermList_above_degree η (w ++ [k]) l j
        (by simp only [List.length_append, List.length_singleton]; omega), leftTermsApply_nil,
        covariantListCoefficients_above_degree η (w ++ [k]) (leftTermsApply l f) j
          (by simp only [List.length_append, List.length_singleton]; omega)]
end

/-! Normalized test degree n becomes left-coefficient degree n-m under finite calibration. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem liftCoefficient_mixed_grading_of_finite_tests (p q n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (lam : ℝ) (hlam : 0 < lam)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι)
    (htest : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      IsBoxSmooth p q (fun X z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
            t X z v)) (X z : Vec 2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (fun y => (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
          liftApply n c
            (fun _ Z => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Z) • Pi.single u ξ)
            t Y y v) z) X‖ ≤ (B * lam ^ (n + p)) * ‖ξ‖) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => c m α t Y y v u) z) X‖ ≤
      (finiteTestCalibrationConstant n m α * B) * lam ^ (n - m + p) := by
  have hbox := liftCoefficient_box_reserve_of_finite_tests p q n m hm c lam
    (ne_of_gt hlam) hc α t v u htest
  have hK := finiteTestCalibrationConstant_nonneg n m α
  apply mixed_operator_jet_norm_le_from_apply p q _ hbox X z _
    (mul_nonneg (mul_nonneg hK hB) (pow_nonneg hlam.le _))
  intro ξ
  have hh := liftCoefficient_applied_mixed_bound_of_finite_tests p q n m hm c lam
    (ne_of_gt hlam) hc α t v u ξ (htest ξ) X z ((B * lam ^ (n + p)) * ‖ξ‖) (hb ξ)
  apply hh.trans_eq
  rw [abs_of_pos (inv_pos.mpr (pow_pos hlam m))]
  have he : n + p = m + (n - m + p) := by omega
  have hscale : (lam ^ m)⁻¹ * lam ^ (n + p) = lam ^ (n - m + p) := by
    rw [he, pow_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos hlam m)), one_mul]
  calc
    _ = (finiteTestCalibrationConstant n m α * B) *
        ((lam ^ m)⁻¹ * lam ^ (n + p)) * ‖ξ‖ := by ring
    _ = _ := by rw [hscale]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Each interpolated metric-difference integrand has a summable decay majorant linear in the perturbation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def metricDifferenceKernelSourceConstant (p q : ℕ) (M Md κ : ℝ) (S : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial *
    metricDifferenceSourceBudget p Md S (q - j)) *
    (1 + q.factorial * (2 * ((2 : ℝ) ^ p * (1 + M)) / κ) ^ q) * (1 + 4 / κ)

theorem metricDifferenceKernelSource_decay
    (p q : ℕ) (hq : q ≤ p) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (g d : ℝ → Vec 2 → ℝ)
    (hgm : ∀ X, Measurable (fun t => g t X)) (hdm : ∀ X, Measurable (fun t => d t X))
    (hgs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t)) (hds : ∀ t, ContDiff ℝ (p : ℕ∞) (d t))
    (M Md eps lam rate κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hrate : 0 ≤ rate) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hgb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hdb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (d t) X‖ ≤ Md * eps * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : Vec 2 → E) (hf : ContDiff ℝ (p : ℕ∞) f) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hfB : ∀ j ≤ p, ∀ X, ‖iteratedFDeriv ℝ j f X‖ ≤ S j * lam ^ j)
    (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y =>
      transverseModeKernel rate (fun t => scalarMetricInterpolation θ g t Y) a b •
        (transverseMetricDifferenceExponent rate d a b Y • f Y)) X‖ ≤
      metricDifferenceKernelSourceConstant p q M Md κ S * eps *
        Real.exp (-(rate * κ / 4) * (b - a)) * lam ^ q := by
  let B := fun j => metricDifferenceSourceBudget p Md S j
  let S' := fun j => B j * eps * rate * (b - a)
  let C := ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * B (q - j)
  let F := 1 + (q.factorial : ℝ) * (2 * ((2 : ℝ) ^ p * (1 + M)) / κ) ^ q
  have hB (j : ℕ) (hj : j ≤ p) : 0 ≤ B j :=
    metricDifferenceSourceBudget_nonneg p j Md S hMd (fun r hr => hS r (hr.trans hj))
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hB (q - j) ((Nat.sub_le _ _).trans hq))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hd := transverseMetricDifferenceExponent_contDiff p d hdm hds
    (fun j => Md * eps * lam ^ j) hdb rate a b
  have hh := transverseModeKernel_source_scaled_jet_decay p q hq
    (scalarMetricInterpolation θ g)
    (fun Y => measurable_const.add ((hgm Y).const_mul θ))
    (scalarMetricInterpolation_contDiff θ p g hgs) (1 + M) lam rate κ a b
    (by positivity) hlam hrate hκ hab
    (scalarMetricInterpolation_scaled_jet_le θ hθ p g hgs M lam hM hlam hgb)
    (fun t _ Y => scalarMetricInterpolation_lower θ κ hθ hκ1 g hgl t Y)
    (fun Y => transverseMetricDifferenceExponent rate d a b Y • f Y) (hd.smul hf) S'
    (fun j hj => mul_nonneg (mul_nonneg (mul_nonneg (hB j hj) heps) hrate) (sub_nonneg.mpr hab))
    (fun j hj Y => transverseMetricDifferenceExponent_source_scaled_jet_le p d hdm hds Md eps lam rate a b
      hMd heps hlam hrate hab hdb f hf S hS hfB j hj Y) X
  have hsum : (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S' (q - j)) =
      C * eps * rate * (b - a) := by
    dsimp [S', C]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum] at hh
  have hk := linear_weighted_decayKernel_le rate (κ / 2) (b - a) hrate (by positivity) (sub_nonneg.mpr hab)
  have ha : rate * (κ / 2) = rate * κ / 2 := by ring
  have hb : rate * (κ / 2) / 2 = rate * κ / 4 := by ring
  have hc : 2 / (κ / 2) = 4 / κ := by ring
  rw [hb, ha, hc] at hk
  calc
    _ ≤ (C * F * eps) * ((rate * (b - a)) * Real.exp (-(rate * κ / 2) * (b - a))) * lam ^ q :=
      hh.trans_eq (by dsimp [F]; ring)
    _ ≤ (C * F * eps) * ((1 + 4 / κ) * Real.exp (-(rate * κ / 4) * (b - a))) * lam ^ q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk
        (mul_nonneg (mul_nonneg hC hF) heps)) (pow_nonneg hlam _)
    _ = _ := by dsimp [C, F, B, metricDifferenceKernelSourceConstant]; ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Exponential coarse normalization preserves the exact paired cross-operator splitting. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB1_paired_difference (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 1 1 f) (hg : IsBoxSmooth 1 1 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => J t X i j)) (X z : Vec 2) :
    (Real.exp (A X))⁻¹ • cellB1 η G v t (fun Y y => Real.exp (A Y) • f Y y) X z -
      (Real.exp (A X))⁻¹ • cellB1 η J v t (fun Y y => Real.exp (A Y) • g Y y) X z =
    (Real.exp (A X))⁻¹ • cellB1 η G v t (fun Y y => Real.exp (A Y) • (f Y y - g Y y)) X z +
      (Real.exp (A X))⁻¹ • cellB1 η (fun s Y i j => G s Y i j - J s Y i j)
        (fun _ _ => 0) t (fun Y y => Real.exp (A Y) • g Y y) X z := by
  have he (Y y : Vec 2) : Real.exp (A Y) • (f Y y - g Y y) =
      Real.exp (A Y) • f Y y - Real.exp (A Y) • g Y y := smul_sub _ _ _
  have hΦf : IsBoxSmooth 1 1 (fun Y y => Real.exp (A Y) • f Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field 1 1 _ (Real.contDiff_exp.comp A.contDiff)) hf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦg : IsBoxSmooth 1 1 (fun Y y => Real.exp (A Y) • g Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field 1 1 _ (Real.contDiff_exp.comp A.contDiff)) hg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  simp_rw [he]
  rw [← smul_sub, cellB1_paired_difference η G J v t _ _ hΦf hΦg hG hJ X z, smul_add]

theorem normalizedCellB2_paired_difference (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 2 0 f) (hg : IsBoxSmooth 2 0 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => J t X i j)) (X z : Vec 2) :
    (Real.exp (A X))⁻¹ • cellB2 η G t (fun Y y => Real.exp (A Y) • f Y y) X z -
      (Real.exp (A X))⁻¹ • cellB2 η J t (fun Y y => Real.exp (A Y) • g Y y) X z =
    (Real.exp (A X))⁻¹ • cellB2 η G t (fun Y y => Real.exp (A Y) • (f Y y - g Y y)) X z +
      (Real.exp (A X))⁻¹ • cellB2 η (fun s Y i j => G s Y i j - J s Y i j)
        t (fun Y y => Real.exp (A Y) • g Y y) X z := by
  have he (Y y : Vec 2) : Real.exp (A Y) • (f Y y - g Y y) =
      Real.exp (A Y) • f Y y - Real.exp (A Y) • g Y y := smul_sub _ _ _
  have hΦf : IsBoxSmooth 2 0 (fun Y y => Real.exp (A Y) • f Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field 2 0 _ (Real.contDiff_exp.comp A.contDiff)) hf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦg : IsBoxSmooth 2 0 (fun Y y => Real.exp (A Y) • g Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field 2 0 _ (Real.contDiff_exp.comp A.contDiff)) hg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  simp_rw [he]
  rw [← smul_sub, cellB2_paired_difference η G J t _ _ hΦf hΦg hG hJ X z, smul_add]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Positive primitive fast words inherit the source's reserved slow smoothness. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem transversePrimitiveField_fast_contDiff (p : Fin 2) (q : ℕ)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ X, ContDiff ℝ (q : ℕ∞) (f X)) (X : Vec 2) :
    ContDiff ℝ ((q + 1 : ℕ) : ℕ∞) (transversePrimitiveField p f X) := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec p)
  have hprofile : ContDiff ℝ (q : ℕ∞) (fun r : ℝ => f X (r • basisVec p)) :=
    (hf X).comp line.contDiff
  exact (centeredIntervalPrimitive_contDiff q _ hprofile).comp
    (ContinuousLinearMap.proj p : Vec 2 →L[ℝ] ℝ).contDiff

theorem transversePrimitiveField_positive_word_slow_contDiff
    (p : Fin 2) (sX sZ m : ℕ) (hm : m ≤ sZ) (α : DerivativeWord2 (m + 1))
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth sX sZ f)
    (hfactor : ∀ X z, f X z = f X ((z p) • basisVec p)) (z : Vec 2) :
    ContDiff ℝ (sX : ℕ∞)
      (fun X => orderedDerivative α (transversePrimitiveField p f X) z) := by
  have he : (fun X => orderedDerivative α (transversePrimitiveField p f X) z) =
      fun X => if (∀ i, α i = p) then
        orderedDerivative (fun _ : Fin m => p) (f X) z else 0 := by
    funext X
    exact congrFun (orderedDerivative_transverse_primitive_source_word p m α (f X)
      ((hf.1 X).of_le (by exact_mod_cast hm)) (hfactor X)) z
  rw [he]
  by_cases ha : ∀ i, α i = p
  · simp only [ite_eq_left ha]
    exact boxSmooth_fast_word_slow_contDiff sX sZ m hm f hf (fun _ => p) z
  · simp only [ite_eq_right ha]
    exact contDiff_const

theorem transversePrimitiveField_positive_word_slow_jet_continuous
    (p : Fin 2) (sX sZ m r : ℕ) (hm : m ≤ sZ) (hr : r ≤ sX)
    (α : DerivativeWord2 (m + 1))
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth sX sZ f)
    (hfactor : ∀ X z, f X z = f X ((z p) • basisVec p)) :
    Continuous (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ r
      (fun X => orderedDerivative α (transversePrimitiveField p f X) x.2) x.1) := by
  have he (z : Vec 2) : (fun X => orderedDerivative α (transversePrimitiveField p f X) z) =
      fun X => if (∀ i, α i = p) then
        orderedDerivative (fun _ : Fin m => p) (f X) z else 0 := by
    funext X
    exact congrFun (orderedDerivative_transverse_primitive_source_word p m α (f X)
      ((hf.1 X).of_le (by exact_mod_cast hm)) (hfactor X)) z
  simp_rw [he]
  by_cases ha : ∀ i, α i = p
  · simp only [ite_eq_left ha]
    exact boxSmooth_fast_word_slow_jet_continuous sX sZ r m hr hm f hf (fun _ => p)
  · simp only [ite_eq_right ha, iteratedFDeriv_fun_zero, Pi.zero_apply]
    exact continuous_const

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A transverse primitive preserves slow box order and gains one fast order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transversePrimitiveField_boxSmooth
    (p : Fin 2) (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth sX sZ f)
    (hfactor : ∀ X z, f X z = f X ((z p) • basisVec p))
    (C : ℕ → ℝ)
    (hb : ∀ j ≤ sX, ∀ (r : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y => f Y (r • basisVec p)) X‖ ≤ C j) :
    IsBoxSmooth sX (sZ + 1) (transversePrimitiveField p f) := by
  classical
  let G := transversePrimitiveField p f
  have hfast (X : Vec 2) : ContDiff ℝ ((sZ + 1 : ℕ) : ℕ∞) (G X) :=
    transversePrimitiveField_fast_contDiff p sZ f hf.1 X
  have hzero := transversePrimitiveField_slow_regularities p sX sZ f hf C hb
  have hword (m : ℕ) (hm : m ≤ sZ) (w : DerivativeWord2 (m + 1)) (z : Vec 2) :
      (fun X => orderedDerivative (fun i => w (Fin.rev i)) (G X) z) =
        fun X => iteratedFDeriv ℝ (m + 1) (G X) z (fun i => basisVec (w i)) := by
    funext X
    have he := congrFun (orderedDerivative_eq_iteratedFDeriv
      (fun i => w (Fin.rev i)) ((hfast X).of_le
        (by exact_mod_cast Nat.succ_le_succ hm))) z
    simpa only [Fin.rev_rev] using he
  refine ⟨hfast, ?_, ?_⟩
  · intro b hbq z
    cases b with
    | zero =>
      let c0 := (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv
      have he : (fun X => iteratedFDeriv ℝ 0 (G X) z) = c0.symm ∘ (fun X => G X z) := by
        funext X
        rfl
      rw [he]
      exact c0.symm.contDiff.comp (hzero.1 z)
    | succ m =>
      have hm : m ≤ sZ := by omega
      apply contDiff_multilinear_of_basis_coordinates (m + 1) sX
      intro w
      rw [← hword m hm w z]
      exact transversePrimitiveField_positive_word_slow_contDiff p sX sZ m hm
        (fun i => w (Fin.rev i)) f hf hfactor z
  · intro r b hr hbq
    cases b with
    | zero =>
      let J := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Vec 2) E
      let c0 := (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv
      let post := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin r => Vec 2) E J c0.symm.toContinuousLinearMap
      have he (z : Vec 2) : (fun X => iteratedFDeriv ℝ 0 (G X) z) =
          c0.symm ∘ (fun X => G X z) := by
        funext X
        rfl
      have hc := post.continuous.comp (hzero.2 r hr)
      apply hc.congr
      intro x
      rw [he x.2, c0.symm.iteratedFDeriv_comp_left]
      rfl
    | succ m =>
      have hm : m ≤ sZ := by omega
      apply multilinear_slow_jet_continuous_of_basis_coordinates (m + 1) sX r hr
        (fun X z => iteratedFDeriv ℝ (m + 1) (G X) z)
      · intro w z
        rw [← hword m hm w z]
        exact transversePrimitiveField_positive_word_slow_contDiff p sX sZ m hm
          (fun i => w (Fin.rev i)) f hf hfactor z
      · intro w
        simp_rw [← hword m hm w]
        exact transversePrimitiveField_positive_word_slow_jet_continuous p sX sZ m r hm hr
          (fun i => w (Fin.rev i)) f hf hfactor

end AVRegularity.CycleComparison.Lift
end
