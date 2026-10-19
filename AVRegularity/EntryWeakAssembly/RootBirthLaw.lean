-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.MeanLeftTermsLocalCongruence
public import AVRegularity.EntryWeakAssembly.FiniteStagePaths
import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.Definitions.EntryWeak.WeakReduction
import AVRegularity.EntryWeakAssembly.MassRecursion

section
section
/-! Finite-window stability with varying scalar, divergence and metric data. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_variable_data_tendsto {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (G : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : A → ℝ)
    (hm : ∀ X i j, Measurable (fun t => G X t i j))
    (hb : ∀ X t i j, |G X t i j| ≤ CG X)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G X t i j * ξ i * ξ j)
    (δ : A → ℝ) (hδ : ∀ X t i j, |G X t i j - P.G t i j| ≤ δ X)
    (hsmall : Tendsto δ l (𝓝 0))
    (S : A → ℝ → ComplexCellL2) (S₀ : ℝ → ComplexCellL2)
    (F : A → ℝ → Fin 2 → ComplexCellL2) (F₀ : ℝ → Fin 2 → ComplexCellL2)
    (hS : ∀ X, MemLp (S X) 2 (volume.restrict (Icc a b)))
    (hS₀ : MemLp S₀ 2 (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => F X t j) 2 (volume.restrict (Icc a b)))
    (hF₀ : ∀ j, MemLp (fun t => F₀ t j) 2 (volume.restrict (Icc a b)))
    (hs : Tendsto (fun X => ∫ t in a..b, ‖S X t - S₀ t‖ ^ 2) l (𝓝 0))
    (hf : ∀ j, Tendsto (fun X => ∫ t in a..b, ‖F X t j - F₀ t j‖ ^ 2) l (𝓝 0))
    (u : A → ℝ → ComplexCellL2) (v : ℝ → ComplexCellL2)
    (slice : A → ℝ → TorusHk 1 ℂ) (other : ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X) (fun t => dataDualDerivative
      (molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)) t
        (slice X t) (S X t) (F X t)))
    (h₀ : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S₀ t) (F₀ t)))
    (hi : ∀ X, u X a = v a) :
    (∀ t ∈ Icc a b, Tendsto (fun X => u X t - v t) l (𝓝 0)) ∧
      Tendsto (fun X => ∫ s in a..b,
        ∑ j, ‖cellDerivativeCLM j (slice X s - other s)‖ ^ 2) l (𝓝 0) := by
  let Q := fun X => molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)
  let M := fun X t => G X t - P.G t
  let flux := fun X t j => F X t j - F₀ t j + molecularMetricHilbertFlux (M X t) (other t) j
  have hM X j k : Measurable (fun t => M X t j k) :=
    (hm X j k).sub (P.metric_measurable j k)
  have hflux X j : MemLp (fun t => flux X t j) 2 (volume.restrict (Icc a b)) :=
    ((hF X j).sub (hF₀ j)).add
      (molecularMetricHilbertFlux_memLp _ (M X) (δ X) (hM X) (hδ X) other h₀.state j)
  have hd X : CellWeakHilbertCurve a b (fun t => u X t - v t)
      (fun t => slice X t - other t) (fun t => dataDualDerivative (Q X) t
        (slice X t - other t) (S X t - S₀ t) (flux X t)) :=
    molecularWeak_metric_difference a b P (G X) (CG X) (hm X) (hb X) (he X)
      (S X) S₀ (F X) F₀ (u X) v (slice X) other (h X) h₀
  let B := fun X => ‖u X a - v a‖ ^ 2 + ∫ t in a..b,
    ‖S X t - S₀ t‖ ^ 2 + 4 * ∑ j, ‖flux X t j‖ ^ 2
  have hBt : Tendsto B l (𝓝 0) := by
    apply window_forcing_budget_tendsto_zero l hab (fun X => u X a - v a)
      (fun X t => S X t - S₀ t) flux (fun X => (hS X).sub hS₀) hflux
    · simpa only [hi, sub_self, norm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : A => (0 : ℝ)) l (𝓝 0))
    · exact hs
    · intro j
      exact window_normSq_add_integral_tendsto_zero l hab _ _
        (fun X => (hF X j).sub (hF₀ j))
        (fun X => molecularMetricHilbertFlux_memLp _ (M X) (δ X) (hM X) (hδ X) other h₀.state j)
        (hf j) (molecularMetricHilbertFlux_component_integral_tendsto_zero l hab
          M δ hM hδ other h₀.state hsmall j)
  have hB X : 0 ≤ B X := add_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg hab
    (fun t _ => add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))))
  refine ⟨?_, ?_⟩
  · intro t ht
    exact molecular_weak_window_value_tendsto_zero l hab Q P.V (fun _ => rfl)
      (fun X t => S X t - S₀ t) flux (fun X => (hS X).sub hS₀) hflux
      (fun X t => u X t - v t) (fun X t => slice X t - other t) hd
      B hB (fun _ => le_rfl) hBt t ht
  · exact molecular_weak_window_gradient_tendsto_zero l hab Q P.V (fun _ => rfl)
      (fun X t => S X t - S₀ t) flux (fun X => (hS X).sub hS₀) hflux
      (fun X t => u X t - v t) (fun X t => slice X t - other t) hd
      B (fun _ => le_rfl) hBt

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal triangular raw forcing is the same spatial class as the actual Hilbert word forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {I : Type*}

theorem wordMetricFlux_Hilbert_ae
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (w : List I) (t : ℝ)
    (hc : ∀ p ∈ independentWordForcing w, HasPeriodicOrderedWeakJet (c p.2 t)) (k : Fin 2) :
    molecularWordHilbertFlux (fun p s => (G p s).transpose) (fun p => cellH1Slice (c p)) w t k =ᵐ[
      volume.restrict AVenhance.unitCube]
        fun x => independentWordMetricFlux (fun p s _ => G p s) c w t x k := by
  have heval (l : List (List I × List I)) (x : Vec 2) :
      ((l.map (fun p => cellMetricFlux (fun s _ => G p.1 s) (c p.2) t x)).sum) k =
        (l.map (fun p => cellMetricFlux (fun s _ => G p.1 s) (c p.2) t x k)).sum := by
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, PiLp.zero_apply]
    | cons p l ih => simp only [List.map_cons, List.sum_cons, PiLp.add_apply, ih]
  have hh := window_list_L2_ae (independentWordForcing w)
    (fun p => molecularMetricHilbertFlux (G p.1 t).transpose (cellH1Slice (c p.2) t) k)
    (fun p x => cellMetricFlux (fun s _ => G p.1 s) (c p.2) t x k)
    (fun p hp => cellMetricFlux_Hilbert_ae (G p.1) (c p.2) t (hc p hp) k)
  have hh' := hh.trans (Filter.EventuallyEq.of_eq (funext (fun x =>
    window_list_sum_apply (independentWordForcing w)
      (fun p x => cellMetricFlux (fun s _ => G p.1 s) (c p.2) t x k) x)))
  simpa only [molecularWordHilbertFlux, independentWordMetricFlux, window_list_sum_apply,
    List.map_map, Function.comp_def, heval] using hh'

theorem wordMetricFlux_sourceSlice_eq_Hilbert
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (w : List I) (t : ℝ)
    (hc : ∀ p ∈ independentWordForcing w, HasPeriodicOrderedWeakJet (c p.2 t)) (k : Fin 2) :
    cellSourceSlice (fun s x => independentWordMetricFlux (fun p r _ => G p r) c w s x k) t =
      molecularWordHilbertFlux (fun p s => (G p s).transpose) (fun p => cellH1Slice (c p)) w t k :=
  cellSourceSlice_eq_of_ae _ t _ (wordMetricFlux_Hilbert_ae G c w t hc k)

end AVRegularity.WeakEntryProofs
end
end

section
/-! The two molecular cross operators preserve local coefficient germs. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsFastPartial_slow_local_congr (Ω : Set (Vec 2)) (k : Fin 2)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermsFastPartial k l) (leftTermsFastPartial k r) :=
  List.rel_map (fun _ _ hh => hh.fastDerivative k) he

end AVRegularity.WeakEntryProofs
end
end

section
/-! Clock changes preserve genuine finite-order field inverses. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution

theorem cellFieldInverse_comp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ) (a b c : ℝ) (hc : 0 < c) (hab : a ≤ b)
    (c₀ : Vec 2 → E) (g u : ℝ → Vec 2 → E)
    (h : IsCellFieldInverse G v r (c * a) (c * b) c₀ g u) :
    IsCellFieldInverse (fun t => c • G (c * t)) (fun t => c • v (c * t)) r a b c₀
      (fun t => c • g (c * t)) (fun t => u (c * t)) := by
  have hmaps : MapsTo (fun t : ℝ => c * t) (Icc a b) (Icc (c * a) (c * b)) := by
    intro t ht
    exact ⟨mul_le_mul_of_nonneg_left ht.1 hc.le, mul_le_mul_of_nonneg_left ht.2 hc.le⟩
  refine ⟨fun t ht => h.1 _ (hmaps ht), ?_⟩
  intro ℓ
  obtain ⟨hsol, hm, hi, _⟩ := h.2 ℓ
  have hs := cellSolution_comp_mul a b c hc ⟨fun t _ => G t, v, 0, 0⟩
    (fun t x => (ℓ (g t x) : ℂ)) (fun _ _ => 0) (cellJetOfField ℓ u) hsol
  have hC : cellClockCoefficients ⟨fun t _ => G t, v, 0, 0⟩ c =
      ⟨fun t _ => c • G (c * t), fun t => c • v (c * t), 0, 0⟩ := by
    simp only [cellClockCoefficients, Pi.zero_apply, smul_zero]
    rfl
  rw [hC] at hs
  have hsrc : (fun t => c • fun x => (ℓ (g (c * t) x) : ℂ)) =
      fun t x => (ℓ ((c • g (c * t)) x) : ℂ) := by
    funext t x
    simp only [Pi.smul_apply, map_smul, Complex.real_smul, Complex.ofReal_mul, smul_eq_mul]
  rw [hsrc] at hs
  have hzero : (fun _ : ℝ => c • fun _ : Vec 2 => (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) =
      fun _ _ => 0 := by
    funext t x
    exact smul_zero c
  rw [hzero] at hs
  refine ⟨hs, fun t ht => hm _ (hmaps ht), hi, ?_⟩
  exact cellSolution_finite_energyNorm hab hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! The two molecular cross operators preserve local coefficient germs. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsMetricCrossDerivative_slow_local_metric_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (G G' : Vec 2 → Fin 2 → Fin 2 → ℝ) (hG : ∀ X ∈ Ω, G X = G' X) (i j : Fin 2)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermsMetricCrossDerivative G i j l)
      (leftTermsMetricCrossDerivative G' i j r) := by
  unfold leftTermsMetricCrossDerivative
  apply List.rel_append
  · exact List.rel_map (fun _ _ hh => hh.fieldSmul_congr (fun X hX _ => congrFun (congrFun (hG X hX) i) j))
      (leftTermsFastPartial_slow_local_congr Ω i _ _
        (leftTermsSlowPartial_slow_local_congr Ω hΩ j l r he))
  · apply leftTermsSlowPartial_slow_local_congr Ω hΩ i
    exact List.rel_map (fun _ _ hh => hh.fieldSmul_congr (fun X hX _ => congrFun (congrFun (hG X hX) i) j))
      (leftTermsFastPartial_slow_local_congr Ω j l r he)

theorem leftTermsMetricSlowDerivative_slow_local_metric_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (G G' : Vec 2 → Fin 2 → Fin 2 → ℝ) (hG : ∀ X ∈ Ω, G X = G' X) (i j : Fin 2)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermsMetricSlowDerivative G i j l)
      (leftTermsMetricSlowDerivative G' i j r) := by
  unfold leftTermsMetricSlowDerivative
  apply leftTermsSlowPartial_slow_local_congr Ω hΩ i
  exact List.rel_map (fun _ _ hh => hh.fieldSmul_congr (fun X hX _ => congrFun (congrFun (hG X hX) i) j))
    (leftTermsSlowPartial_slow_local_congr Ω hΩ j l r he)

theorem cellB1LeftTerms_slow_local_metric_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (η : ℝ)
    (G G' : Vec 2 → Fin 2 → Fin 2 → ℝ) (hG : ∀ X ∈ Ω, G X = G' X) (v : Vec 2 → Vec 2)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (cellB1LeftTerms η G v l) (cellB1LeftTerms η G' v r) := by
  unfold cellB1LeftTerms
  apply List.rel_append
  · apply leftTermSlowEq_flatMap_same
    intro k _
    exact List.rel_map (fun _ _ hh => hh.fieldSmul (fun _ z => Real.sqrt η * v z k))
      (leftTermsSlowPartial_slow_local_congr Ω hΩ k l r he)
  · apply leftTermSlowEq_flatMap_same
    intro i _
    apply leftTermSlowEq_flatMap_same
    intro j _
    exact List.rel_map (fun _ _ hh => hh.smul (-Real.sqrt η))
      (leftTermsMetricCrossDerivative_slow_local_metric_congr Ω hΩ G G' hG i j l r he)

theorem cellB2LeftTerms_slow_local_metric_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (η : ℝ) (G G' : Vec 2 → Fin 2 → Fin 2 → ℝ) (hG : ∀ X ∈ Ω, G X = G' X)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (cellB2LeftTerms η G l) (cellB2LeftTerms η G' r) := by
  unfold cellB2LeftTerms
  apply leftTermSlowEq_flatMap_same
  intro i _
  apply leftTermSlowEq_flatMap_same
  intro j _
  exact List.rel_map (fun _ _ hh => hh.smul (-η))
    (leftTermsMetricSlowDerivative_slow_local_metric_congr Ω hΩ G G' hG i j l r he)

end AVRegularity.WeakEntryProofs
end
end

section
/-! The admissible response words in a weak source are a genuinely finite menu. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weakSource_words_finite (N R : ℕ) :
    Set.Finite {w : List WordLetter | w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R} := by
  classical
  have he : {w : List WordLetter | w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R} =
      insert [] (↑(wordsUpTo (weakAlphabet N) R) : Set (List WordLetter)) := by
    ext w
    rfl
  rw [he]
  exact (wordsUpTo (weakAlphabet N) R).finite_toSet.insert []

instance weakEntryValidWordsFinite (N R : ℕ) :
    Finite {w : List WordLetter // w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R} :=
  (weakSource_words_finite N R).to_subtype

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Strict lower-word induction proves continuity of every actual ordered-word equation. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {A I : Type*} [TopologicalSpace A]

theorem molecular_word_Hilbert_family_continuous {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (P : MolecularData)
    (G : List I → A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : List I → ℝ)
    (hm : ∀ w X j k, Measurable (fun t => G w X t j k))
    (hb : ∀ w, w.length ≤ N → ∀ X t j k, |G w X t j k| ≤ B w)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] X t i j * ξ i * ξ j)
    (δ : List I → A → A → ℝ)
    (hd : ∀ w, w.length ≤ N → ∀ X Y t j k,
      |G w X t j k - G w Y t j k| ≤ δ w Y X)
    (hδ : ∀ w, w.length ≤ N → ∀ Y, Tendsto (δ w Y) (𝓝 Y) (𝓝 0))
    (S : List I → A → ℝ → ComplexCellL2)
    (F : List I → A → ℝ → Fin 2 → ComplexCellL2)
    (hS : ∀ w, w.length ≤ N → ∀ X, MemLp (S w X) 2 (volume.restrict (Icc a b)))
    (hF : ∀ w, w.length ≤ N → ∀ X j,
      MemLp (fun t => F w X t j) 2 (volume.restrict (Icc a b)))
    (hs : ∀ w, w.length ≤ N → ∀ Y,
      Tendsto (fun X => ∫ t in a..b, ‖S w X t - S w Y t‖ ^ 2) (𝓝 Y) (𝓝 0))
    (hf : ∀ w, w.length ≤ N → ∀ Y j,
      Tendsto (fun X => ∫ t in a..b, ‖F w X t j - F w Y t j‖ ^ 2) (𝓝 Y) (𝓝 0))
    (u : List I → A → ℝ → ComplexCellL2) (slice : List I → A → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (G [] X) (B []) (hm [] X) (hb [] (by simp) X) (he X)) t
        (slice w X t) (S w X t)
        (fun j => F w X t j + molecularWordHilbertFlux (fun p => G p X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0) :
    ∀ w, w.length ≤ N → ∀ Y,
      (∀ t ∈ Icc a b, Tendsto (fun X => u w X t - u w Y t) (𝓝 Y) (𝓝 0)) ∧
      Tendsto (fun X => ∫ t in a..b,
        ∑ j, ‖cellDerivativeCLM j (slice w X t - slice w Y t)‖ ^ 2) (𝓝 Y) (𝓝 0) := by
  let Q := fun X => molecularMetricReplacement P (G [] X) (B []) (hm [] X) (hb [] (by simp) X) (he X)
  intro w hw
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro Y
    have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
    have hg p (hp : p ∈ independentWordForcing w) : p.1.length ≤ N := by
      have hh := hl p hp
      omega
    have hc p (hp : p ∈ independentWordForcing w) : p.2.length ≤ N := by
      have hh := hl p hp
      omega
    let L := fun X => molecularWordHilbertFlux (fun p => G p X) (fun p => slice p X) w
    have hmL X j : MemLp (fun t => L X t j) 2 (volume.restrict (Icc a b)) :=
      molecularWordHilbertFlux_memLp (a := a) (b := b) _ _ w B
        (fun p _ => hm p.1 X) (fun p hp => hb p.1 (hg p hp) X)
        (fun p hp => (h p.2 (hc p hp) X).state) j
    have htL j : Tendsto (fun X => ∫ t in a..b, ‖L X t j - L Y t j‖ ^ 2) (𝓝 Y) (𝓝 0) :=
      molecularWordHilbertFlux_difference_integral_tendsto_zero (𝓝 Y) hab G
        (fun p => G p Y) slice (fun p => slice p Y) w B (fun p => δ p Y)
        (fun p _ => hm p.1) (fun p _ => hm p.1 Y)
        (fun p hp => hb p.1 (hg p hp)) (fun p hp X => hd p.1 (hg p hp) X Y)
        (fun p hp => hδ p.1 (hg p hp) Y)
        (fun p hp X => (h p.2 (hc p hp) X).state)
        (fun p hp => (h p.2 (hc p hp) Y).state)
        (fun p hp => (ih p.2.length (by have hh := hl p hp; omega) p.2 (hc p hp) rfl Y).2) j
    let VF := fun X t j => F w X t j + L X t j
    have hmVF X j : MemLp (fun t => VF X t j) 2 (volume.restrict (Icc a b)) :=
      (hF w hw X j).add (hmL X j)
    have htVF j : Tendsto (fun X => ∫ t in a..b, ‖VF X t j - VF Y t j‖ ^ 2) (𝓝 Y) (𝓝 0) := by
      have hh := window_normSq_add_integral_tendsto_zero (𝓝 Y) hab
        (fun X t => F w X t j - F w Y t j) (fun X t => L X t j - L Y t j)
        (fun X => (hF w hw X j).sub (hF w hw Y j))
        (fun X => (hmL X j).sub (hmL Y j)) (hf w hw Y j) (htL j)
      have heq X t : VF X t j - VF Y t j =
          (F w X t j - F w Y t j) + (L X t j - L Y t j) := by dsimp only [VF]; abel
      simpa only [heq] using hh
    have hQQ X : molecularMetricReplacement (Q Y) (G [] X) (B [])
        (hm [] X) (hb [] (by simp) X) (he X) = Q X := rfl
    have hQg : (Q Y).G = G [] Y := rfl
    have hmetric X t j k : |G [] X t j k - (Q Y).G t j k| ≤ δ [] Y X := by
      rw [hQg]
      exact hd [] (by simp) X Y t j k
    have hcur X : CellWeakHilbertCurve a b (u w X) (slice w X)
        (fun t => dataDualDerivative
          (molecularMetricReplacement (Q Y) (G [] X) (B [])
            (hm [] X) (hb [] (by simp) X) (he X)) t (slice w X t) (S w X t) (VF X t)) := by
      rw [hQQ X]
      exact h w hw X
    exact molecularWeak_variable_data_tendsto (𝓝 Y) hab (Q Y) (G []) (fun _ => B [])
      (hm []) (hb [] (by simp)) he (δ [] Y) hmetric (hδ [] (by simp) Y)
      (S w) (S w Y) VF (VF Y) (hS w hw) (hS w hw Y) hmVF (hmVF Y)
      (hs w hw Y) htVF (u w) (u w Y) (slice w) (slice w Y) hcur (h w hw Y)
      (fun X => by rw [hi w hw X, hi w hw Y])

end AVRegularity.WeakEntryProofs
end
end

section
/-! Weak tags retain the exact kernel width and original finer wavelength. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakPassage_record_lengths (P : ProvParams) (Mn : WeakMenu) (rW : ℝ)
    (Din : ℕ) (G G' : GenStage D hr Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) :
    (G'.fam.identity v u γ).record.length = D.eps G.level ∧
      (G'.fam.identity v u γ).record.width = rW := by
  obtain ⟨_, _, _, _, _, e, _idx, _Cc, _Cc0, _hCc, _hCc0, _hinj, hd⟩ := hp
  have htag := (ht v u γ).1
  rw [(hd v u γ).1] at htag
  have hl := htag.2.2.2.1
  have hw := htag.2.2.2.2.1
  change (G'.fam.identity v u γ).record.length =
    ((e v u γ).1.weakTag P G.level rW Mn.η0).length at hl
  change (G'.fam.identity v u γ).record.width =
    ((e v u γ).1.weakTag P G.level rW Mn.η0).width at hw
  have hs : ((e v u γ).1.weakTag P G.level rW Mn.η0).length = D.eps G.level ∧
      ((e v u γ).1.weakTag P G.level rW Mn.η0).width = rW := by
    cases (e v u γ).1 <;> exact ⟨rfl, rfl⟩
  exact ⟨hl.trans hs.1, hw.trans hs.2⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! The weak alphabet has exactly the requested number of eddy letters. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem card_weakAlphabet (N : ℕ) : (weakAlphabet N).card = N := by
  rw [weakAlphabet, Finset.card_image_of_injective _ (fun a b h => WordLetter.eddy.inj h),
    Nat.card_Icc]
  omega

end AVRegularity.WeakEntryProofs
end
end

section
/-! A finite-depth incoming graph has only finitely many valid weak source identities. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakValidSources_finite (G : GenStage D hr Dm b j₀) (N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) :
    Set.Finite {s : WeakSource G | s.Valid N R Din} := by
  let W := {w : List WordLetter // w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R}
  let C := (W × (Σ h : Fin (H + 1), StagePath G h.1) × Fin (N + Din + 1)) ⊕
    (CompIn G.comps × W × Fin (N + 2))
  let decode : C → WeakSource G := fun c => match c with
    | .inl (w, π, n) => .inherited w.1 π.1.1 π.2 n.1
    | .inr (v, w, n) => .eddy v w.1 n.1
  have hf : Set.Finite (Set.range decode) := Set.finite_range decode
  apply hf.subset
  intro s hs
  cases s with
  | inherited w h π n =>
      obtain ⟨hw, _hh, _hn, hn⟩ := hs
      exact ⟨Sum.inl (⟨w, hw⟩, ⟨⟨h, by have := hpath h π; omega⟩, π⟩,
        ⟨n, by omega⟩), rfl⟩
  | eddy v w n =>
      obtain ⟨hw, _hwlen, _hn, hn⟩ := hs
      exact ⟨Sum.inr (v, ⟨w, hw⟩, ⟨n, by omega⟩), rfl⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! Positivity and readout contraction for weak word weights. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weakMass_nonneg (D : OCData) (N J : ℕ) (η : ℝ)
    (heps : ∀ i, 0 ≤ D.eps i) (v : Comp) : 0 ≤ weakMass D N J η v := by
  unfold weakMass
  apply mul_nonneg (by norm_num)
  apply List.prod_nonneg
  intro x hx
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
  apply pow_nonneg
  apply mul_nonneg
  · unfold weakCw
    positivity
  · exact Real.rpow_nonneg (heps e.scale) _

theorem weakReadoutWeight_nonneg (D : OCData) (η : ℝ)
    (heps : ∀ i, 0 ≤ D.eps i) (v : Comp) : 0 ≤ weakReadoutWeight D η v := by
  unfold weakReadoutWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
  exact pow_nonneg (Real.rpow_nonneg (heps e.scale) _) _

theorem weakReadoutWeight_le_one (D : OCData) (η : ℝ) (hη : 0 ≤ η)
    (heps : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1) (v : Comp) :
    weakReadoutWeight D η v ≤ 1 := by
  unfold weakReadoutWeight
  have hp : ∀ l : List ℝ, (∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) → l.prod ≤ 1 := by
    intro l
    induction l with
    | nil => intro _; exact le_refl _
    | cons a l ih =>
        intro hl
        have ha := hl a (List.mem_cons_self)
        have ht : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 1 :=
          fun x hx => hl x (List.mem_cons_of_mem _ hx)
        have hn := List.prod_nonneg (fun x hx => (ht x hx).1)
        exact (mul_le_mul ha.2 (ih ht) hn (by norm_num)).trans_eq (one_mul 1)
  apply hp
  intro x hx
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
  exact ⟨pow_nonneg (Real.rpow_nonneg (heps e.scale).1 _) _,
    pow_le_one₀ (Real.rpow_nonneg (heps e.scale).1 _)
      (Real.rpow_le_one (heps e.scale).1 (heps e.scale).2 hη)⟩

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Actual weak masses and readout weights are strictly positive. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weakMass_pos (D : OCData) (N J : ℕ) (η : ℝ) (hN : 1 ≤ N) (hJ : 1 ≤ J)
    (heps : ∀ i, 0 < D.eps i) (v : Comp) : 0 < weakMass D N J η v := by
  unfold weakMass
  apply mul_pos (by norm_num)
  apply List.prod_pos
  intro x hx
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
  apply pow_pos
  apply mul_pos
  · unfold weakCw
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hj : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    positivity
  · exact Real.rpow_pos_of_pos (heps e.scale) _

theorem weakReadoutWeight_pos (D : OCData) (η : ℝ)
    (heps : ∀ i, 0 < D.eps i) (v : Comp) : 0 < weakReadoutWeight D η v := by
  unfold weakReadoutWeight
  apply List.prod_pos
  intro x hx
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
  exact pow_pos (Real.rpow_pos_of_pos (heps e.scale) _) _

end AVRegularity.WeakEntryProofs
end
end

section
/-! At the weak output, stored widths and original lengths have their exact requested values. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_output_records (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J)
    (v u : CompIn (stage M).comps) (γ : (stage M).fam.Γ v u) :
    ((stage M).fam.identity v u γ).record.length = D.eps (M + 1) ∧
      ((stage M).fam.identity v u γ).record.width = rW := by
  have hp := hc.2.2 (M + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hp
  have hl := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc
    (M + 1) (by omega) (by omega)
  have hrec := weakPassage_record_lengths P Mn rW (1 + (M + J - (M + 1)) * Mn.N)
    (stage (M + 1)) (stage M) hp.1 hp.2 v u γ
  rw [hl] at hrec
  exact hrec

end AVRegularity.WeakEntryProofs
end
end

section
/-! One global source enumeration supplies fresh seed identities across every ordered edge. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def weakSourceLabel (G : GenStage D hr Dm b j₀) (N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) :
    {s : WeakSource G // s.Valid N R Din} → ℕ := by
  haveI sourceFinite : Finite {s : WeakSource G // s.Valid N R Din} :=
    (weakValidSources_finite G N R Din H hpath).to_subtype
  letI sourceFintype : Fintype {s : WeakSource G // s.Valid N R Din} := Fintype.ofFinite _
  exact fun s => (Fintype.equivFin _ s).val

theorem weakSourceLabel_injective (G : GenStage D hr Dm b j₀) (N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) :
    Function.Injective (weakSourceLabel G N R Din H hpath) := by
  have sourceFinite : Finite {s : WeakSource G // s.Valid N R Din} :=
    (weakValidSources_finite G N R Din H hpath).to_subtype
  let sourceFintype : Fintype {s : WeakSource G // s.Valid N R Din} := Fintype.ofFinite _
  intro s s' hs
  apply (Fintype.equivFin {s : WeakSource G // s.Valid N R Din}).injective
  exact Fin.ext hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! Canonical weak edges and a seed index that is injective across distinct component pairs. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def weakSourceEdge (G : GenStage D hr Dm b j₀) (S : Finset Comp) (m N R Din : ℕ)
    (v u : CompIn S) :=
  {s : WeakSource G // s.Valid N R Din ∧ s.srcComp m = u.1 ∧ s.tgtComp m = v.1}

@[instance_reducible] def weakSourceEdgeFintype (G : GenStage D hr Dm b j₀) (S : Finset Comp) (m N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) (v u : CompIn S) :
    Fintype (weakSourceEdge G S m N R Din v u) := by
  let embed : weakSourceEdge G S m N R Din v u → {s : WeakSource G // s.Valid N R Din} :=
    fun s => ⟨s.1, s.2.1⟩
  have he : Function.Injective embed := by
    intro s s' h
    apply Subtype.ext
    exact congrArg (fun q : {s : WeakSource G // s.Valid N R Din} => q.1) h
  haveI sourceFinite : Finite {s : WeakSource G // s.Valid N R Din} :=
    (weakValidSources_finite G N R Din H hpath).to_subtype
  haveI edgeFinite : Finite (weakSourceEdge G S m N R Din v u) := Finite.of_injective embed he
  exact Fintype.ofFinite _

def weakSourceEdgeIndex (G : GenStage D hr Dm b j₀) (S : Finset Comp) (m N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) (v u : CompIn S)
    (γ : weakSourceEdge G S m N R Din v u) : ℕ :=
  weakSourceLabel G N R Din H hpath ⟨γ.1, γ.2.1⟩

theorem weakSourceEdgeIndex_injective (G : GenStage D hr Dm b j₀) (S : Finset Comp)
    (m N R Din H : ℕ) (hpath : ∀ h, StagePath G h → h ≤ H)
    (v u : CompIn S) (γ : weakSourceEdge G S m N R Din v u)
    (v' u' : CompIn S) (γ' : weakSourceEdge G S m N R Din v' u')
    (hi : weakSourceEdgeIndex G S m N R Din H hpath v u γ =
      weakSourceEdgeIndex G S m N R Din H hpath v' u' γ') :
    v = v' ∧ u = u' ∧ HEq γ γ' := by
  have hs : γ.1 = γ'.1 := congrArg Subtype.val (weakSourceLabel_injective G N R Din H hpath hi)
  have hu : u = u' := Subtype.ext
    (γ.2.2.1.symm.trans ((congrArg (WeakSource.srcComp m) hs).trans γ'.2.2.1))
  have hv : v = v' := Subtype.ext
    (γ.2.2.2.symm.trans ((congrArg (WeakSource.tgtComp m) hs).trans γ'.2.2.2))
  subst u'
  subst v'
  exact ⟨rfl, rfl, heq_of_eq (Subtype.ext hs)⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! Positive mass sums through one actual weak response-word extension. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

open scoped BigOperators

theorem weakExtComps_mass_sum_le (D : OCData) (N J m R : ℕ) (η : ℝ)
    (heps : ∀ i, 0 ≤ D.eps i) (S : Finset Comp) :
    ∑ v ∈ weakExtComps m N R S, weakMass D N J η v ≤
      (∑ v ∈ S, weakMass D N J η v) *
        (1 + ∑ n ∈ Finset.Icc 1 R,
          (N : ℝ) ^ n * (weakCw N J * D.eps (m - 1) ^ (η / 2)) ^ n) := by
  classical
  let W := wordsUpTo (weakAlphabet N) R
  let f := weakMass D N J η
  let r := weakCw N J * D.eps (m - 1) ^ (η / 2)
  have hf : ∀ v, 0 ≤ f v := weakMass_nonneg D N J η heps
  have hr : 0 ≤ r := by
    apply mul_nonneg
    · unfold weakCw
      positivity
    · exact Real.rpow_nonneg (heps (m - 1)) _
  have hu : ∑ v ∈ S ∪ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f v ≤
      (∑ v ∈ S, f v) + ∑ v ∈ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f v := by
    have hi := Finset.sum_union_inter (s₁ := S) (s₂ := (S ×ˢ W).image (fun x => succComp m x.1 x.2)) (f := f)
    have hn : 0 ≤ ∑ v ∈ S ∩ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f v :=
      Finset.sum_nonneg (fun v _ => hf v)
    linarith only [hi, hn]
  have him : (∑ v ∈ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f v) ≤
      ∑ x ∈ S ×ˢ W, f (succComp m x.1 x.2) :=
    Finset.sum_image_le_of_nonneg (fun v _ => hf v)
  have hp : (∑ x ∈ S ×ˢ W, f (succComp m x.1 x.2)) =
      (∑ v ∈ S, f v) * ∑ w ∈ W, r ^ w.length := by
    rw [Finset.sum_product]
    simp_rw [show ∀ v w, f (succComp m v w) = f v * r ^ w.length from
      fun v w => weakMass_succComp D N J m η v w, ← Finset.mul_sum]
    rw [Finset.sum_mul]
  have hw := sum_wordsUpTo_weight_le (weakAlphabet N) R r hr
  rw [card_weakAlphabet] at hw
  change (∑ v ∈ S ∪ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f v) ≤ _
  calc
    _ ≤ (∑ v ∈ S, f v) + ∑ x ∈ S ×ˢ W, f (succComp m x.1 x.2) :=
      hu.trans (add_le_add le_rfl him)
    _ = (∑ v ∈ S, f v) * (1 + ∑ w ∈ W, r ^ w.length) := by rw [hp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hw)
      (Finset.sum_nonneg (fun v _ => hf v))

end AVRegularity.WeakEntryProofs
end
end

section
/-! The prescribed weak root masses and readouts define a genuine positive birth law. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

theorem weakCw_strict_pos (N J : ℕ) (hN : 1 ≤ N) (hJ : 1 ≤ J) : 0 < weakCw N J := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hj : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  unfold weakCw
  positivity

def weakRootBirthLaw (D : OCData) (S : Finset Comp) (N J : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i) : BirthLaw where
  cH := weakCw N J
  cH_pos := weakCw_strict_pos N J hN hJ
  wordCount := 1
  wordCount_pos := Nat.zero_lt_one
  etaB := η / 2
  eta0 := η
  iota := 0
  rootMass := weakRootWeight S (fun v => weakMass D N J η v.1)
  rootMass_pos := weakRootWeight_pos S _ (fun v => weakMass_pos D N J η hN hJ heps v.1)
  rootReadout := weakRootWeight S (fun v => weakReadoutWeight D η v.1)
  rootReadout_pos := weakRootWeight_pos S _ (fun v => weakReadoutWeight_pos D η heps v.1)

@[simp] theorem weakRootBirthLaw_mass (D : OCData) (S : Finset Comp) (N J : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i) (v : CompIn S) :
    (weakRootBirthLaw D S N J η hN hJ heps).rootMass (weakRootLabel S v) =
      weakMass D N J η v.1 := by
  exact weakRootWeight_label S (fun v => weakMass D N J η v.1) v

@[simp] theorem weakRootBirthLaw_readout (D : OCData) (S : Finset Comp) (N J : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i) (v : CompIn S) :
    (weakRootBirthLaw D S N J η hN hJ heps).rootReadout (weakRootLabel S v) =
      weakReadoutWeight D η v.1 := by
  exact weakRootWeight_label S (fun v => weakReadoutWeight D η v.1) v

end AVRegularity.WeakEntryProofs
end
end
end
