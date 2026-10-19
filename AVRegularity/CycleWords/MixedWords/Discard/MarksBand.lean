-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.BandRep
import AVRegularity.CycleWords.MixedWords.Discard.QuietOp
import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.Seam.OldScalar.Assembly
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the operator bound of the coupling at a quiet good time

`quiet_tau_op_bound`: `∑_i ‖∑_{i'} τ_{i,i'} w_{i'}‖² ≤ (C_Q (1+|y|²)^{p})² ∑ ‖w‖²`, with `C_Q`, `p` free
of the number of components, from the block bound and the block-triangular structure. -/

section Op

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The constant of the jet counts over the ladder. -/
def quietJetConst (Nw s₀ : ℕ) (d Ks : Fin Nw → ℕ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
    (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ)

/-- **The operator bound of the coupling at a quiet good time.** -/
theorem quiet_tau_op_bound {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hθ : θ ∈ freqCube) (r : ℝ) (hr0 : ∀ z, F.v r z = 0)
    (hq : ∀ l, ∀ (v u : ι) (d' : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d', ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (d : Fin Nw → ℕ) (s₀ : ℕ) (hs₀ : 2 ≤ s₀) {Bz : ℝ} (hBz : 0 ≤ Bz) (n : Fin 2 → ℤ)
    (hprov : ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ Bz ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (w : B1WIndex ι h Nw m Ks → ℂ) :
    ∑ i, ‖∑ i', quietTau F θ n r i i' * w i'‖ ^ 2 ≤
      (((b1wM Nw m Ks + 1) ^ 2 : ℝ) * (Bz * Real.sqrt (quietJetConst Nw s₀ d Ks (b1wM Nw m Ks)) *
        (1 + quietYSq θ n) ^ (b1wLadderTop s₀ d Ks m))) ^ 2 * ∑ i', ‖w i'‖ ^ 2 := by
  classical
  set M := b1wM Nw m Ks with hM
  set yq := quietYSq θ n with hyq
  have hy0 : 0 ≤ yq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy1 : 1 ≤ 1 + yq := by linarith
  set Cj := quietJetConst Nw s₀ d Ks M with hCj
  have hCj0 : 0 ≤ Cj := Finset.sum_nonneg fun k _ => by positivity
  set β : ℝ := Bz * Real.sqrt Cj * (1 + yq) ^ (b1wLadderTop s₀ d Ks m) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hop := blockTriangular_op_bound (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks))
    (Mst := M) (fun i => (b1wSt_lt i).le) (fun i i' => quietTau F θ n r i i')
    (fun i i' hi => quietTau_zero F θ n r i i' hi) hβ0 ?_ w
  · simpa [hβ, mul_assoc] using hop
  · intro k k' hkk a
    by_cases hk : k < M
    · have hblock := quiet_block_bound F θ r hr0 hq (b1wLadderAt Nw s₀ d Ks k)
        (b1wLadderAt Nw s₀ d Ks k') k k' (by have := le_b1wLadderAt Nw s₀ d Ks k; omega) hkk n
        (hprov k k' hkk) a
      refine hblock.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hN := ModeNorm_le (b1wLadderAt Nw s₀ d Ks k) n
      have hb := Budget_le hθ n
      have hb0 := Budget_pos n
      have h1 : ModeNorm (b1wLadderAt Nw s₀ d Ks k) n ≤
          (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
            (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ) *
            (1 + yq) ^ (b1wLadderAt Nw s₀ d Ks k) := by
        refine hN.trans ?_
        calc (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) : ℝ) *
            Budget n ^ (b1wLadderAt Nw s₀ d Ks k)
            ≤ (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) : ℝ) *
              (((1 + 4 * Real.pi ^ 2) * (1 + yq)) ^ (b1wLadderAt Nw s₀ d Ks k)) := by gcongr
          _ = _ := by rw [mul_pow]; ring
      have h2 : (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
            (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ) ≤ Cj :=
        Finset.single_le_sum (f := fun k => (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
          (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ)) (fun _ _ => by positivity)
          (Finset.mem_range.2 hk)
      have h3 : (1 + yq) ^ (b1wLadderAt Nw s₀ d Ks k) ≤ (1 + yq) ^ (b1wLadderTop s₀ d Ks m) :=
        pow_le_pow_right₀ hy1 (b1wLadderAt_le_top s₀ m d Ks hk)
      have h4 : (1 + yq) ^ (b1wLadderTop s₀ d Ks m) ≤ (1 + yq) ^ (2 * b1wLadderTop s₀ d Ks m) :=
        pow_le_pow_right₀ hy1 (by omega)
      have h5 : 0 ≤ (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
            (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ) := by positivity
      calc Bz ^ 2 * ModeNorm (b1wLadderAt Nw s₀ d Ks k) n
          ≤ Bz ^ 2 * (Cj * (1 + yq) ^ (2 * b1wLadderTop s₀ d Ks m)) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            calc _ ≤ (Fintype.card (JetIndex2 (b1wLadderAt Nw s₀ d Ks k)) *
                  (1 + 4 * Real.pi ^ 2) ^ (b1wLadderAt Nw s₀ d Ks k) : ℝ) *
                  (1 + yq) ^ (b1wLadderAt Nw s₀ d Ks k) := h1
              _ ≤ Cj * (1 + yq) ^ (2 * b1wLadderTop s₀ d Ks m) :=
                mul_le_mul h2 (h3.trans h4) (by positivity) hCj0
        _ = β ^ 2 := by
            rw [hβ, mul_pow, mul_pow, Real.sq_sqrt hCj0, ← pow_mul]
            ring_nf
    · have hempty : stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun i hi => hk ?_
        rw [← (Finset.mem_filter.1 hi).2]; exact b1wSt_lt i
      simp only [stageSet] at hempty
      rw [hempty]
      simp

end Op

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # the terminal pass on a frame

* `WindowFamilyProp C Q j s ρ`: the conclusion of `window_family_hs` with the constants `C, Q`;
  `window_family_uniform`: one pair of constants for every `j ≤ J_t`, `s ≤ S_t`.
* `fullField_frame_family`: on a frame of duration at least one, at a frequency of the zone, the
  stage curves (`b1w_stage_curves`) on the terminal window `[b − 1, b]` with the windows `T + kτ`,
  `τ = 1/(M+1)`: the negative-order bound `M_neg` of the plain pass at every time, the sources of
  the source bound (`StageSourceHsStatement` on the frame) and the uniform window step give
  (`terminal_pass_family`) every stage at `b` in `H^{n_i}` (the positive ladder), with the `ℓ²` norm
  over the stages of each order bounded by a `termConst` constant times `M_neg`, `L = J/√η`. -/

section
open AVRegularity.CycleWords.Assembly

universe u v

/-- `τ^{-x/2} ≤ (M+1)^E` for `τ = (M+1)⁻¹` and `x ≤ 2E`. -/
theorem inv_rpow_neg_half_le (M : ℕ) {x E : ℕ} (h : x ≤ 2 * E) :
    ((M : ℝ) + 1)⁻¹ ^ (-(x : ℝ) / 2) ≤ ((M : ℝ) + 1) ^ E := by
  have h1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) M
    linarith
  have h0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have he : ((M : ℝ) + 1)⁻¹ ^ (-(x : ℝ) / 2) = ((M : ℝ) + 1) ^ ((x : ℝ) / 2) := by
    rw [Real.inv_rpow h0, ← Real.rpow_neg h0]
    congr 1
    ring
  rw [he, ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le h1 ?_
  rw [div_le_iff₀ two_pos]
  exact_mod_cast (by omega : x ≤ E * 2)
end

/-! # the terminal pass on a frame, by stage families

* `WindowFamilyProp`: the conclusion of `window_family_hs` with given constants;
  `window_family_uniform`: one pair of constants for `j_max = J_t` and every `s ≤ S_t`.
* `fullField_frame_family`: on a frame of duration at least one, at a frequency of the zone, given
  the negative-order bound `M_neg` of the stage families at every time (the plain pass), the
  sources of the source bound and the uniform family window constants, every stage family of order `k < M` at
  `b` has `H^{n_i}` representatives with `ℓ²` norm at most
  `termConst (C_f(1+L)^{Q_f}) ((M+1)^{J_t+S_t}) B 1 k · M_neg`, `L = J/√η`; constants independent
  of the number of stages. -/

section
open AVRegularity.CycleWords.Assembly

universe u v w

/-- The conclusion of `window_family_hs` with the constants `C, Q`. -/
def WindowFamilyProp (C : ℝ) (Q jmax s : ℕ) (ρ : ℝ) : Prop :=
  ∀ (t₀ b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    t₀ ≤ b → b ≤ t₀ + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc t₀ b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ jmax + s + 1 → t ∈ Set.Icc t₀ b → ∀ x,
      ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ {J : Type w} [Fintype J] (j : J → ℕ), (∀ i, j i ≤ jmax) →
  ∀ (u : J → ℝ → ComplexCellL2) (slice : J → ℝ → TorusHk 1 ℂ) (S : J → ℝ → ComplexCellL2)
    (F : J → ℝ → Fin 2 → ComplexCellL2),
    (∀ i, CellWeakHilbertCurve t₀ b (u i) (slice i) (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice i t) (S i t) (F i t))) →
  ∀ M : ℝ, 0 ≤ M →
    (∀ ψ : J → TorusHk s ℂ, ‖∑ i, cellComplexPair (u i t₀) (torusHkValueCLM (ψ i))‖ ≤
      M * Real.sqrt (∑ i, ‖ψ i‖ ^ 2)) →
  ∀ (σ : ∀ i, ℝ → TorusHk (j i) ℂ) (f : ℝ → ℝ), IntegrableOn f (Set.Icc t₀ b) →
    (∀ᵐ t ∂volume.restrict (Set.Icc t₀ b), Real.sqrt (∑ i, ‖σ i t‖ ^ 2) ≤ f t ∧
      ∀ i (z : TorusHk 1 ℂ), cellComplexSource (fun k => (θ k : ℂ)) (S i t) (F i t) z =
        cellComplexPair (torusHkValueCLM (σ i t)) (torusHkValueCLM z)) →
  ∀ τ : ℝ, 0 < τ → ∀ t ∈ Set.Icc t₀ b, t₀ + τ ≤ t →
    ∃ X : ∀ i, TorusHk (j i) ℂ, (∀ i, torusHkValueCLM (X i) = u i t) ∧
      Real.sqrt (∑ i, ‖X i‖ ^ 2) ≤
        C * (1 + L) ^ Q * (τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M + ∫ r in t₀..t, f r)

/-- **One pair of family window constants for `j_max = J_t` and every `s ≤ S_t`.** -/
theorem window_family_uniform (hP4bF : CellForcedHsFamilyStatement.{w})
    (hP4cF : CellNegativeSmoothingFamilyStatement.{w}) (Jt St : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ (Cf : ℝ) (Qf : ℕ), 0 < Cf ∧ ∀ s ≤ St, WindowFamilyProp.{w} Cf Qf Jt s ρ := by
  choose C Q hC hW using fun s : Fin (St + 1) => window_family_hs hP4bF hP4cF Jt s hρ
  refine ⟨∑ s, C s, ∑ s, Q s, Finset.sum_pos (fun s _ => hC s) ⟨0, Finset.mem_univ _⟩,
    fun s hs => ?_⟩
  intro t₀ b L G hG v hv V hb θ ht₀b hb1 hL hθ hsm hjet J _ j hj u slice S F hu M hM hneg σ f hf
    hσ τ hτ t ht htτ
  obtain ⟨X, hX, hXn⟩ := hW ⟨s, by omega⟩ t₀ b L G hG hv V hb θ ht₀b hb1 hL hθ hsm hjet j hj u
    slice S F hu M hM hneg σ f hf hσ τ hτ t ht htτ
  refine ⟨X, hX, hXn.trans ?_⟩
  have hf0 : 0 ≤ ∫ r in t₀..t, f r := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict ht.1 ?_
    have hsub : Set.Icc t₀ t ⊆ Set.Icc t₀ b := Set.Icc_subset_Icc le_rfl ht.2
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hσ] with r hr
    exact (Real.sqrt_nonneg _).trans hr.1
  have hbr : 0 ≤ τ ^ (-((Jt + s : ℕ) : ℝ) / 2) * M + ∫ r in t₀..t, f r :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) hM) hf0
  have hCs : C ⟨s, by omega⟩ ≤ ∑ s, C s :=
    Finset.single_le_sum (f := C) (fun s _ => (hC s).le) (Finset.mem_univ _)
  have hQs : (1 + L) ^ Q ⟨s, by omega⟩ ≤ (1 + L) ^ ∑ s, Q s :=
    pow_le_pow_right₀ (by linarith) (Finset.single_le_sum (f := Q) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ _))
  exact mul_le_mul_of_nonneg_right (mul_le_mul hCs hQs (by positivity)
    ((hC _).le.trans hCs)) hbr

/-- A sum over a stage set is a sum over the stage subtype. -/
theorem sum_stageSet_eq_subtype {I : Type*} [Fintype I] (st : I → ℕ) (k : ℕ) (g : I → ℝ) :
    ∑ i ∈ stageSet st k, g i = ∑ i : {i // st i = k}, g i.1 :=
  Finset.sum_subtype (stageSet st k) (fun i => by simp [stageSet]) g

theorem sum_stageSet_eq_subtype_complex {I : Type*} [Fintype I] (st : I → ℕ) (k : ℕ)
    (g : I → ℂ) : ∑ i ∈ stageSet st k, g i = ∑ i : {i // st i = k}, g i.1 :=
  Finset.sum_subtype (stageSet st k) (fun i => by simp [stageSet]) g

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The terminal pass on a frame, by stage families.** -/
theorem fullField_frame_family {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hθ : θ ∈ freqCube) (d : Fin Nw → ℕ) (s₀ Kf : ℕ)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (hab : F.a + 1 ≤ F.b)
    (Jt St : ℕ) (hJt : ∀ i : B1WIndex ι h Nw m Ks, b1wPosLadder Kf d i ≤ Jt)
    (hSt : ∀ k < b1wM Nw m Ks, b1wLadderAt Nw s₀ d Ks k ≤ St)
    (Cf : ℝ) (Qf : ℕ) (hCf : 0 ≤ Cf)
    (hwinF : ∀ s ≤ St, WindowFamilyProp.{u} Cf Qf Jt s (2 * Real.pi))
    (Mneg : ℝ) (hMneg : 0 ≤ Mneg)
    (hplain : ∀ t ∈ Icc (F.b - 1) F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2,
      IsScaledStage F θ t W →
      ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
          Mneg * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2))
    (B : ℝ) (hB : 0 ≤ B)
    (hsrcF : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k : ℕ)
      (X : ∀ i' : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i') ℂ),
      (∀ i', b1wSt i' < k → (torusHkValueCLM (X i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i' r) →
    ∀ (S : B1WIndex ι h Nw m Ks → ComplexCellL2)
      (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2),
      (∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
          amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y) →
      (∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
          amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j) →
      ∃ σ : ∀ i : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i) ℂ,
        (∀ i ∈ stageSet b1wSt k, ∀ z : TorusHk 1 ℂ,
          cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) z =
            cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
        ∑ i ∈ stageSet b1wSt k, ‖σ i‖ ^ 2 ≤
          B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2) :
    ∀ k < b1wM Nw m Ks, ∃ X : ∀ i : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i) ℂ,
      (∀ i ∈ stageSet b1wSt k, (torusHkValueCLM (X i) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i F.b) ∧
      Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖X i‖ ^ 2) ≤
        termConst (Cf * (1 + (∑ l ∈ Finset.range (Jt + St + 2), b1wJets K l) /
          Real.sqrt F.η) ^ Qf) ((((b1wM Nw m Ks : ℕ) : ℝ) + 1) ^ (Jt + St)) B 1 k * Mneg := by
  classical
  -- the stage curves
  obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl⟩ := b1w_stage_curves F m Ks θ hM V hb
    (b1wScale F.π F.ϖ F.ηg F.letters)
  have hW := fun i => cellWeakHilbertCurve_shift (b1wCoeff_eq_real F θ) (hcur i)
  have hscaled : ∀ i, ∀ t ∈ Icc F.a F.b,
      (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i t := by
    intro i t ht
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellRawTrace (Dθ i) t), cellRawTrace_ae (Dθ i) t (hmem i t ht), hval i t ht]
      with y h1 h2 h3
    rw [h1, h2, h3]
    rfl
  -- the window, the drift jets
  set M := b1wM Nw m Ks with hMdef
  set τ : ℝ := ((M : ℝ) + 1)⁻¹ with hτdef
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hτ0 : 0 < τ := inv_pos.2 hM1
  set T := F.b - 1 with hTdef
  have hTa : F.a ≤ T := by linarith
  have hsubT : Icc T F.b ⊆ Icc F.a F.b := Icc_subset_Icc hTa le_rfl
  obtain ⟨Js, hJs⟩ : ∃ Js : ℝ, Js = ∑ l ∈ Finset.range (Jt + St + 2), b1wJets K l := ⟨_, rfl⟩
  have hJs0 : 0 ≤ Js := by
    rw [hJs]
    exact Finset.sum_nonneg fun l _ => le_max_right _ _
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.mpr F.piece.hη
  have hL0 : 0 ≤ Js / Real.sqrt F.η := div_nonneg hJs0 hs.le
  have hjet : ∀ (l : ℕ) t, l ≤ Jt + St + 1 → ∀ x,
      ‖iteratedFDeriv ℝ l (F.v t) x‖ ≤ Js / Real.sqrt F.η := fun l t hl x =>
    frame_drift_jet_le F ((le_max_left _ _).trans (by
      rw [hJs]
      exact Finset.single_le_sum (f := b1wJets K) (fun l _ => le_max_right _ _)
        (Finset.mem_range.2 (by omega)))) t x
  have hstep : ∀ k < M, T + (k : ℝ) * τ ∈ Icc T F.b := by
    intro k hk
    have hlt : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hk
    have hle : (k : ℝ) * τ ≤ 1 := by
      rw [hτdef, ← div_eq_mul_inv, div_le_one hM1]
      linarith
    exact ⟨by nlinarith [hτ0.le, Nat.cast_nonneg (α := ℝ) k], by linarith⟩
  -- the abstract terminal pass
  have hpass := terminal_pass_family b1wSt M (b1wPosLadder Kf d) (b1wLadderAt Nw s₀ d Ks) hτ0
    (fun k => ((θ k : ℝ) : ℂ))
    (fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t))
    (fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t))
    (fun i t k => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z k) t))
    (Cf * (1 + Js / Real.sqrt F.η) ^ Qf) (((M : ℝ) + 1) ^ (Jt + St)) B Mneg
    (by positivity) (by positivity) hB hMneg ?hwin ?hlen hstep ?hneg ?hsrc
  case hwin =>
    intro k hk t₀ ht₀ M' hM' hneg' σ f hf hσ t ht htτ
    have ht₀' : F.b ≤ t₀ + 1 := by linarith [ht₀.1]
    -- the family of the stages of order `k`, as a subtype
    obtain ⟨X', hX', hX'n⟩ := hwinF (b1wLadderAt Nw s₀ d Ks k) (hSt k hk) t₀ F.b
      (Js / Real.sqrt F.η) F.G F.piece.hGm F.piece.hv V hb θ ht₀.2 ht₀' hL0
      (sqrt_vecDot_le_of_freqCube hθ) (fun t _ => F.piece.hvs t)
      (fun l r hl _ x => hjet l r (by have := hSt k hk; omega) x)
      (J := {i : B1WIndex ι h Nw m Ks // b1wSt i = k}) (fun i => b1wPosLadder Kf d i.1)
      (fun i => hJt i.1)
      (fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i.1) (cellRawTrace (Dθ i.1) t))
      _ _ _ (fun i => (hW i.1).mono (Icc_subset_Icc (hTa.trans ht₀.1) le_rfl)) M' hM'
      (fun ψ => by
        have hn := hneg' (fun i => if hi : b1wSt i = k then ψ ⟨i, hi⟩ else 0)
        rw [sum_stageSet_eq_subtype_complex, sum_stageSet_eq_subtype] at hn
        have hψ : ∀ x : {i : B1WIndex ι h Nw m Ks // b1wSt i = k},
            (if hi : b1wSt x.1 = k then ψ ⟨x.1, hi⟩ else 0) = ψ x := fun x => by
          split_ifs with hi
          · rfl
          · exact absurd x.2 hi
        simp only [hψ] at hn
        exact hn)
      (fun i t => σ t i.1) f hf
      (by
        filter_upwards [hσ] with r hr
        refine ⟨?_, fun i z => hr.2 i.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, i.2⟩) z⟩
        rw [← sum_stageSet_eq_subtype b1wSt k (fun i => ‖σ r i‖ ^ 2)]
        exact hr.1)
      τ hτ0 t ht htτ
    refine ⟨fun i => if hi : b1wSt i = k then X' ⟨i, hi⟩ else 0, fun i hi => ?_, ?_⟩
    · have hik : b1wSt i = k := (Finset.mem_filter.1 hi).2
      simp only [hik, dite_true]
      exact hX' ⟨i, hik⟩
    · rw [sum_stageSet_eq_subtype]
      have hX'' : ∀ x : {i : B1WIndex ι h Nw m Ks // b1wSt i = k},
          (if hi : b1wSt x.1 = k then X' ⟨x.1, hi⟩ else 0) = X' x := fun x => by
        split_ifs with hi
        · rfl
        · exact absurd x.2 hi
      simp only [hX'']
      refine hX'n.trans ?_
      have hpow := inv_rpow_neg_half_le M (x := Jt + b1wLadderAt Nw s₀ d Ks k) (E := Jt + St)
        (by have := hSt k hk; omega)
      have hC0 : 0 ≤ Cf * (1 + Js / Real.sqrt F.η) ^ Qf := by positivity
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hpow hM') le_rfl) hC0
  case hlen =>
    intro t₀ ht₀ t ht
    linarith [ht₀.1, ht.2]
  case hneg =>
    intro k hk ψ
    have hti : T + (k : ℝ) * τ ∈ Icc F.a F.b := hsubT (hstep k hk)
    exact hplain _ (hstep k hk) (fun j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters j)
      (cellRawTrace (Dθ j) (T + (k : ℝ) * τ))) (fun j => hscaled j _ hti) k ψ
  case hsrc =>
    refine ae_restrict_of_ae_restrict_of_subset hsubT ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.2 hlit, ae_all_iff.2 hsl,
      hsrcF] with r hr hl hs' hp k X hX
    have hgood := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hr) (fun i => hmem i r hr)
      (fun i => ⟨(hs' i).1, (hl i).1, (hs' i).2, (hl i).2⟩)
    exact hp k X (fun i' hi' => by
        rw [hX i' hi']
        exact hscaled i' r hr)
      _ _ (fun i _ => hgood.1 i) (fun i _ j => hgood.2.1 i j)
  intro k hk
  have hbI : F.b ∈ Icc (T + ((k : ℝ) + 1) * τ) F.b := by
    refine ⟨?_, le_rfl⟩
    have hlt : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hk
    have hle : ((k : ℝ) + 1) * τ ≤ 1 := by
      rw [hτdef, ← div_eq_mul_inv, div_le_one hM1]
      linarith
    linarith
  obtain ⟨X, hX, hXn⟩ := hpass k hk F.b hbI
  refine ⟨X, fun i hi => ?_, ?_⟩
  · rw [hX i hi]
    exact hscaled i F.b ⟨F.ordered, le_rfl⟩
  · rw [← hJs]
    exact hXn

end Frame
end

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard.BandDatum

/-! # `BandAmpOutputStatement`

The output norm of a band-limited family by the `L²` norm of its amplitude jets. One layer of
`jetOutputNorm` is compared with the weighted layer of `layer_sq_le` (with `M = a`), and the
factor `ϖ^a (1 + |θ|/ϖ)^a = (ϖ + |θ|)^a ≤ (1 + π/2)^a` on the ball is absorbed. -/

universe u v

section Layer

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]

/-- One layer of the output norm against the weighted layer. -/
theorem layer_comparison (π : ι → ℝ) {m a : ℕ} {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ m) {ϖ rstar : ℝ}
    (hr : 0 < rstar) (S : ι → Vec 2 → ℝ) (hS : ∀ v z, 0 ≤ S v z)
    (hSm : ∀ v, AEStronglyMeasurable (S v) volume) :
    ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * S v z) 2 volume ^ 2 ≤
      ENNReal.ofReal (rstar ^ a) ^ 2 * ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * S v z) 2 volume ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hle : eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * S v z) 2 volume ≤
      ENNReal.ofReal (rstar ^ a) *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * S v z) 2 volume := by
    have hc : eLpNorm (rstar ^ a • fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
        S v z) 2 volume = ENNReal.ofReal (rstar ^ a) *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * S v z) 2 volume := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    rw [← hc]
    refine eLpNorm_mono (AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
      (hSm v)) fun z => ?_
    have hm := abs_scaled_moment_le ϖ z hβ
    rw [abs_mul] at hm
    have hSz := hS v z
    have hW : 0 ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) :=
      Real.rpow_nonneg (by nlinarith [sq_nonneg ϖ, sq_nonneg (z 0), sq_nonneg (z 1)]) _
    have hpow : (0 : ℝ) ≤ rstar ^ a := by positivity
    simp only [Real.norm_eq_abs, abs_mul, Pi.smul_apply, smul_eq_mul, abs_of_nonneg hSz,
      abs_of_nonneg hW, abs_of_nonneg hpow]
    calc |(ϖ * z 0) ^ β.1| * |(ϖ * z 1) ^ β.2| * rstar ^ a * S v z
        ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * rstar ^ a * S v z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) hSz
      _ = rstar ^ a * ((1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * S v z) := by ring
  calc ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * S v z) 2 volume ^ 2
      ≤ ENNReal.ofReal ((π v)⁻¹) * (ENNReal.ofReal (rstar ^ a) *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * S v z) 2 volume) ^ 2 :=
        mul_le_mul_right (pow_le_pow_left₀ zero_le hle 2) _
    _ = _ := by rw [mul_pow]; ring

end Layer

section Absorb

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of one layer: `3^{2m} · 3 (2π)² 2^a 3 · c_a² (1 + π/2)^{2a}`. -/
noncomputable def layerConst (m a : ℕ) : ℝ :=
  (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
    (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ))) ^ 2 *
      (1 + Real.pi / 2) ^ (2 * a)

theorem layerConst_pos (m a : ℕ) : 0 < layerConst m a := by
  unfold layerConst; positivity

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- On the ball, `ϖ^a (1 + |θ|/ϖ)^a ≤ (1 + π/2)^a`: the weighted amplitude integral is absorbed. -/
theorem absorb_le (π : ι → ℝ) {m a : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    {A B : ∀ x, Vec 2 → h x} (hvan : ∀ x θ, (Real.pi / 2) ^ 2 < vecDot θ θ → A x θ = 0 ∧ B x θ = 0) :
    ENNReal.ofReal ((3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
        (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))) ^ 2) *
      ampJetIntegral π m a ϖ A B ≤
    ENNReal.ofReal (layerConst m a) * ∫⁻ θ, amplitudeJetNorm π m ϖ A B θ ^ 2 := by
  unfold ampJetIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun θ => ?_
  by_cases hz : amplitudeJetNorm π m ϖ A B θ = 0
  · simp [hz]
  have hθ : vecDot θ θ ≤ (Real.pi / 2) ^ 2 := by
    by_contra hcon
    exact hz (amplitudeJetNorm_eq_zero_of_gt π m ϖ hvan (not_le.1 hcon))
  have hn : ‖θ‖ ≤ Real.pi / 2 := by
    refine (norm_le_sqrt_vecDot θ).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    exact hθ
  have hb : ϖ ^ a * (1 + ‖θ‖ / ϖ) ^ a ≤ (1 + Real.pi / 2) ^ a := by
    rw [← mul_pow, mul_add, mul_one, mul_div_cancel₀ _ hϖ.ne']
    exact pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg θ]) a
  rw [mul_pow (ENNReal.ofReal ((1 + ‖θ‖ / ϖ) ^ a)) (amplitudeJetNorm π m ϖ A B θ) 2,
    ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  unfold layerConst
  set Kc : ℝ := (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
    (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ))) ^ 2 with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have e1 : (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
        (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))) ^ 2 *
          ((1 + ‖θ‖ / ϖ) ^ a) ^ 2 = Kc * (ϖ ^ a * (1 + ‖θ‖ / ϖ) ^ a) ^ 2 := by
    rw [hKc]; ring
  rw [e1, pow_mul']
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 2) hKc0

end Absorb

/-- **Step 2**: the output norm of a band-limited family by its amplitude jets. -/
theorem bandAmpOutputStatement : BandAmpOutputStatement.{u, v} := by
  intro Kf m Cout hCout
  set Cs : ℝ := ∑ a ∈ Finset.range (Kf + 1), Cout ^ a * layerConst m a ^ (1 / 2 : ℝ) with hCs
  have hCs0 : 0 < Cs := by
    refine Finset.sum_pos (fun a _ => mul_pos (pow_pos hCout a)
      (Real.rpow_pos_of_pos (layerConst_pos m a) _)) ⟨0, by simp⟩
  have hcard : 0 < ((momentIndices m).card : ℝ) := by
    have : (0, 0) ∈ momentIndices m := by simp [momentIndices]
    exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
  refine ⟨((momentIndices m).card : ℝ) * Cs, mul_pos hcard hCs0, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ rstar hϖ hϖ1 hr hrC A B hA hB
  set I : ℝ≥0∞ := ∫⁻ θ, amplitudeJetNorm π m ϖ A B θ ^ 2 with hI
  have hvan : ∀ x θ, (Real.pi / 2) ^ 2 < vecDot θ θ → A x θ = 0 ∧ B x θ = 0 :=
    fun x θ hθ => ⟨(hA x).2 θ hθ, (hB x).2 θ hθ⟩
  have hterm : ∀ β ∈ momentIndices m, ∀ a ∈ Finset.range (Kf + 1),
      ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) *
            Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w
              (ampFun (Real.pi / 2) (A v) (B v)) z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Cout ^ a * layerConst m a ^ (1 / 2 : ℝ)) * I ^ (1 / 2 : ℝ) := by
    intro β hβ a ha
    have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
    have haKf : a ≤ Kf := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h1 := layer_comparison π (a := a) (ϖ := ϖ) hβm hr (fun v z => Real.sqrt (∑ w : DerivativeWord2 a,
      ‖orderedDerivative w (ampFun (Real.pi / 2) (A v) (B v)) z‖ ^ 2))
      (fun v z => Real.sqrt_nonneg _) (fun v => by
        refine Continuous.aestronglyMeasurable (Real.continuous_sqrt.comp
          (continuous_finsetSum _ fun w _ => (continuous_orderedDerivative_ampFun
            (by positivity) (hA v) (hB v) w).norm.pow 2)))
    have h2 := layer_sq_le π (by positivity : (0 : ℝ) ≤ Real.pi / 2) hϖ hA hB (le_refl a)
    have h3 := absorb_le π (m := m) (a := a) hϖ hϖ1 hvan
    have h4 : (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => ((ϖ * z 0) ^ β.1 *
        (ϖ * z 1) ^ β.2 * rstar ^ a) * Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w
          (ampFun (Real.pi / 2) (A v) (B v)) z‖ ^ 2)) 2 volume ^ 2) ≤
        ENNReal.ofReal (rstar ^ a) ^ 2 * (ENNReal.ofReal (layerConst m a) * I) :=
      h1.trans (mul_le_mul_right (h2.trans h3) _)
    have h5 := ENNReal.rpow_le_rpow h4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      sq_rpow_half] at h5
    have hf : ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ?_)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (by positivity))
    calc _ ≤ 1 * _ := mul_le_mul_left hf _
      _ = _ := one_mul _
      _ ≤ ENNReal.ofReal (rstar ^ a) * (ENNReal.ofReal (layerConst m a) ^ (1 / 2 : ℝ) *
            I ^ (1 / 2 : ℝ)) := h5
      _ ≤ ENNReal.ofReal (Cout ^ a) * (ENNReal.ofReal (layerConst m a) ^ (1 / 2 : ℝ) *
            I ^ (1 / 2 : ℝ)) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le hrC a)) _
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (layerConst_pos m a).le (by norm_num), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
  unfold jetOutputNorm
  calc _ ≤ ∑ β ∈ momentIndices m, ∑ a ∈ Finset.range (Kf + 1),
        ENNReal.ofReal (Cout ^ a * layerConst m a ^ (1 / 2 : ℝ)) * I ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun β hβ => Finset.sum_le_sum fun a ha => hterm β hβ a ha
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (pow_nonneg hCout.le _)
            (Real.rpow_nonneg (layerConst_pos m a).le _)), ← hCs,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end AVRegularity.CycleWords.Discard.BandDatum
end
end

section
/-! # Tools of the discard assemblies: thresholds and the scaled stages

* `IsWordPiece.mono`, `AmplitudeIdFrame.mono`: a frame at a threshold `g₁` is a frame at every
  larger threshold, with the same data (the scaled stages and the coefficients agree by `rfl`).
  The statements of the discard each choose their own `g₁`; an assembly takes the minimum.
* `isScaledStage_exists`: on every frame (below the threshold of the measurable fibre clause),
  at every frequency, the scaled stage values have `L²` representatives at every time of the frame
  (`b1w_stage_curves`): the `W₀`, `W` of `PlainStageStatement`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

universe u v

namespace AVRegularity.CycleWords.Assembly

/-- A smaller threshold gives a piece of the larger one. -/
theorem IsWordPiece.mono {K : ScalarConstants} {g₁ g₂ : ℝ} {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ}
    {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D} {η S ηg ϖ : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}
    {a b : ℝ} (hP : IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b) (h12 : g₁ ≤ g₂) :
    IsWordPiece K g₂ H J π letters η S ηg ϖ G v g reg a b :=
  { hP with hg₁ := hP.hg₁.trans h12 }

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- A frame at a smaller threshold is a frame at the larger one, with the same data. -/
def AmplitudeIdFrame.mono {K : ScalarConstants} {g₁ g₂ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (h12 : g₁ ≤ g₂) :
    AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₂ :=
  { F with piece := F.piece.mono h12 }

end Frame

end AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

open AVRegularity.CycleWords.Assembly

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

theorem isScaledStage_mono {K : ScalarConstants} {g₁ g₂ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (h12 : g₁ ≤ g₂)
    (θ : Vec 2) (t : ℝ) (W : B1WIndex ι h Nw m Ks → ComplexCellL2) :
    IsScaledStage (F.mono h12) θ t W ↔ IsScaledStage F θ t W := Iff.rfl

end Frame

/-- **The scaled stages have `L²` representatives** at every time of every frame below the
threshold of the measurable fibre clause. -/
theorem isScaledStage_exists (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D Nw m : ℕ} {Ks : Fin Nw → ℕ}
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    ∃ W : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2,
      ∀ t ∈ Icc F.a F.b, IsScaledStage F θ t (fun i => W i t) := by
  obtain ⟨gM, hgM, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  refine ⟨gM, hgM, ?_⟩
  intro ι _ h _ _ _ _ _ _ D Nw m Ks F θ
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  obtain ⟨Dθ, -, -, -, hval, -, hmem, -⟩ := b1w_stage_curves F m Ks θ
    (fun j x e β => hMK F j x e θ β) V hb (b1wScale F.π F.ϖ F.ηg F.letters)
  refine ⟨fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t),
    fun t ht i => ?_⟩
  filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
    (cellRawTrace (Dθ i) t), cellRawTrace_ae (Dθ i) t (hmem i t ht), hval i t ht] with y h1 h2 h3
  rw [h1, h2, h3]
  rfl

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # the plain pass

`plainStageAssembly : PlainStageAssembly`: from the transform families at every frequency of the
zone and the adjoint propagator in `H^j` with a kernel, the plain pass
`PlainStageStatement`. `plainStage_of_adjointKernel`: the same with the transform families proved.

Constants. The adjoint propagator bound at the ladder orders `s_k`, `k < M`, gives `C_k, Q_k` (`adjoint_kernel_frame`, with
the drift jets of the frames); `c₀ = ∑ C_k`, `Q_m = ∑ Q_k`, and `C_a = c₀ P_e^{Q_m}` on a frame.
`plain_pass` gives `C_k(C_a) ≤ C_k(1) max(1, C_a)^{k+1}` (`plainConst_le_scale`), so the bound is
`C P_e^Q (1 + (t − a))^Q κ(a,t)` with `C = 1 + ∑_{k<M} C_k(1) max(1, c₀)^{k+1}` and
`Q = Q_m M + M`, before the frame. Stages of order `k ≥ M` are empty. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The constants of the plain pass are polynomial in `C_a`. -/
theorem plainConst_le_scale {Ca A B : ℝ} (hCa : 0 ≤ Ca) (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    plainConst Ca A B k ≤ plainConst 1 A B k * max 1 Ca ^ (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set L := max 1 Ca with hL
  have hl1 : 1 ≤ L := le_max_left _ _
  have hCaL : Ca ≤ L := le_max_right _ _
  rw [plainConst_eq, plainConst_eq]
  have hsum : Ca * ∑ k' ∈ Finset.range k, plainConst Ca A B k' ≤
      L ^ (k + 1) * ∑ k' ∈ Finset.range k, plainConst 1 A B k' := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k' hk' => ?_
    have hk'k := Finset.mem_range.1 hk'
    have hp0 := plainConst_nonneg hCa hA hB k'
    have hp1 := plainConst_nonneg zero_le_one hA hB k'
    calc Ca * plainConst Ca A B k' ≤ L * (plainConst 1 A B k' * L ^ (k' + 1)) :=
          mul_le_mul hCaL (ih k' hk'k) hp0 (by positivity)
      _ = L ^ (k' + 2) * plainConst 1 A B k' := by ring
      _ ≤ L ^ (k + 1) * plainConst 1 A B k' :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (by omega)) hp1
  have hl : Ca ≤ L ^ (k + 1) := hCaL.trans (le_self_pow₀ hl1 (by omega))
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  calc Ca + A * B * Ca * ∑ k' ∈ Finset.range k, plainConst Ca A B k'
      = Ca + A * B * (Ca * ∑ k' ∈ Finset.range k, plainConst Ca A B k') := by ring
    _ ≤ L ^ (k + 1) + A * B * (L ^ (k + 1) * ∑ k' ∈ Finset.range k, plainConst 1 A B k') :=
        add_le_add hl (mul_le_mul_of_nonneg_left hsum hAB)
    _ = (1 + A * B * 1 * ∑ k' ∈ Finset.range k, plainConst 1 A B k') * L ^ (k + 1) := by ring

/-- The final constants. -/
theorem plain_final_le {A B c₀ P T κ X Y : ℝ} {Qm M k : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc₀ : 0 ≤ c₀) (hP : 1 ≤ P) (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hk : k < M) :
    plainConst (c₀ * P ^ Qm) A B k * (1 + T) ^ k * κ * X * Y ≤
      (1 + ∑ k ∈ Finset.range M, plainConst 1 A B k * max 1 c₀ ^ (k + 1)) *
        P ^ (Qm * M + M) * (1 + T) ^ (Qm * M + M) * κ * X * Y := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPQ : 1 ≤ P ^ Qm := one_le_pow₀ hP
  have hm1 : 1 ≤ max 1 c₀ := le_max_left _ _
  have hp1 := plainConst_nonneg zero_le_one hA hB k
  have hmax : max 1 (c₀ * P ^ Qm) ≤ max 1 c₀ * P ^ Qm :=
    max_le (by nlinarith) (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have h1 : plainConst (c₀ * P ^ Qm) A B k ≤
      plainConst 1 A B k * max 1 c₀ ^ (k + 1) * P ^ (Qm * M + M) := by
    refine (plainConst_le_scale (mul_nonneg hc₀ (by positivity)) hA hB k).trans ?_
    calc plainConst 1 A B k * max 1 (c₀ * P ^ Qm) ^ (k + 1)
        ≤ plainConst 1 A B k * (max 1 c₀ * P ^ Qm) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
            hmax _) hp1
      _ = plainConst 1 A B k * max 1 c₀ ^ (k + 1) * P ^ (Qm * (k + 1)) := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ plainConst 1 A B k * max 1 c₀ ^ (k + 1) * P ^ (Qm * M + M) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP ?_) (by positivity)
          have : Qm * (k + 1) ≤ Qm * M := Nat.mul_le_mul_left _ hk
          omega
  have h2 : plainConst 1 A B k * max 1 c₀ ^ (k + 1) ≤
      1 + ∑ k ∈ Finset.range M, plainConst 1 A B k * max 1 c₀ ^ (k + 1) := by
    have := Finset.single_le_sum (f := fun k => plainConst 1 A B k * max 1 c₀ ^ (k + 1))
      (fun k _ => mul_nonneg (plainConst_nonneg zero_le_one hA hB k) (by positivity))
      (Finset.mem_range.2 hk)
    linarith
  have h3 : (1 + T) ^ k ≤ (1 + T) ^ (Qm * M + M) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hpc0 : 0 ≤ plainConst (c₀ * P ^ Qm) A B k :=
    plainConst_nonneg (mul_nonneg hc₀ (by positivity)) hA hB k
  have hκXY : 0 ≤ κ * X * Y := by positivity
  calc plainConst (c₀ * P ^ Qm) A B k * (1 + T) ^ k * κ * X * Y
      = plainConst (c₀ * P ^ Qm) A B k * (1 + T) ^ k * (κ * X * Y) := by ring
    _ ≤ ((1 + ∑ k ∈ Finset.range M, plainConst 1 A B k * max 1 c₀ ^ (k + 1)) *
          P ^ (Qm * M + M)) * (1 + T) ^ (Qm * M + M) * (κ * X * Y) := by
        have hC0 : 0 ≤ 1 + ∑ k ∈ Finset.range M, plainConst 1 A B k * max 1 c₀ ^ (k + 1) :=
          (mul_nonneg hp1 (by positivity)).trans h2
        refine mul_le_mul_of_nonneg_right (mul_le_mul (h1.trans
          (mul_le_mul_of_nonneg_right h2 (by positivity))) h3 (by positivity)
          (mul_nonneg hC0 (by positivity))) hκXY
    _ = _ := by ring

/-- The plain pass, from the transform families and the adjoint propagator bound. -/
theorem plainStageAssembly : PlainStageAssembly.{u, v} := by
  intro hZ hK2 K
  obtain ⟨g₁, hg₁, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D m d Ks pos s₀ A hs₀ hA
  obtain ⟨B, hB, hprov⟩ := hZ K Nw D m d Ks pos Real.pi s₀ hs₀
  choose Ck Qk hCk hadjk using fun k =>
    adjoint_kernel_frame.{u, v} hK2 K (b1wLadderAt Nw s₀ d Ks k) hA
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k := ⟨_, rfl⟩
  obtain ⟨Qm, hQm⟩ : ∃ Qm : ℕ, Qm = ∑ k ∈ Finset.range (b1wM Nw m Ks), Qk k := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact Finset.sum_nonneg fun k _ => (hCk k).le
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨1 + ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1),
    Qm * b1wM Nw m Ks + b1wM Nw m Ks, ?_, ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1) :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (plainConst_nonneg zero_le_one hA0 hB k) (by positivity)
    linarith
  intro ι _ h _ _ _ _ _ _ F θ hlet hJF hθ V hb κ hκ W₀ hW₀ t ht W hW k ψ
  have hP := one_le_peFactor F.η
  have hP0 : 0 ≤ peFactor F.η := zero_le_one.trans hP
  have hT : 0 ≤ t - F.a := sub_nonneg.2 ht.1
  have hκ0 : 0 ≤ κ F.a t := (hκ.pos F.a t).le
  by_cases hk : k < b1wM Nw m Ks
  swap
  · -- no stage of order `k`
    have he : stageSet b1wSt k = (∅ : Finset (B1WIndex ι h Nw m Ks)) := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => hk ?_
      rw [← (Finset.mem_filter.1 hi).2]
      exact b1wSt_lt i
    rw [he, Finset.sum_empty, norm_zero]
    have : 0 ≤ 1 + ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun k _ =>
        mul_nonneg (plainConst_nonneg zero_le_one hA0 hB k) (by positivity))
    have hpow : 0 ≤ (1 + (t - F.a)) ^ (Qm * b1wM Nw m Ks + b1wM Nw m Ks) :=
      pow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg this (pow_nonneg hP0 _)) hpow)
      hκ0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- the adjoint curves with one constant
  have hadj : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b,
      ∀ ψ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ)
        (U : ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        CellWeakHilbertCurve F.a t Ψv Ψs (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv t = torusHkValueCLM ψ ∧
        ∀ r ∈ Icc F.a t, torusHkValueCLM (U r) = Ψv r ∧
          ‖U r‖ ≤ c₀ * peFactor F.η ^ Qm * κ r t * ‖ψ‖ := by
    intro k hk t ht ψ
    obtain ⟨Ψv, Ψs, U, h1, h2, h3⟩ := hadjk k g₁ F θ hθ V hb κ hκ t ht ψ
    refine ⟨Ψv, Ψs, U, h1, h2, fun r hr => ⟨(h3 r hr).1, (h3 r hr).2.trans ?_⟩⟩
    have hk' : k ∈ Finset.range (b1wM Nw m Ks) := Finset.mem_range.2 hk
    have hC : Ck k * peFactor F.η ^ Qk k ≤ c₀ * peFactor F.η ^ Qm := by
      rw [hc₀, hQm]
      exact mul_le_mul (Finset.single_le_sum (f := Ck) (fun k _ => (hCk k).le) hk')
        (pow_le_pow_right₀ hP (Finset.single_le_sum (f := Qk) (fun _ _ => Nat.zero_le _) hk'))
        (pow_nonneg hP0 _) (by rw [← hc₀]; exact hc₀0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (hκ.pos r t).le)
      (norm_nonneg _)
  obtain ⟨Wc, hWc, hbd⟩ := plain_stage_frame F θ d s₀ hs₀ (fun l => ⟨(hlet l).1, (hlet l).2.1⟩)
    (by omega) (fun j x e β => hMK F j x e θ β) B hB (hprov g₁ F θ hlet hJF fun k => hθ k) V hb κ
    hA0 hκ (c₀ * peFactor F.η ^ Qm) (mul_nonneg hc₀0 (pow_nonneg hP0 _)) hadj
  have hWt : ∀ i, W i = Wc i t := fun i => Lp.ext ((hW i).trans (hWc i t ht).symm)
  have hWa : ∀ i, W₀ i = Wc i F.a := fun i =>
    Lp.ext ((hW₀ i).trans (hWc i F.a ⟨le_rfl, F.ordered⟩).symm)
  have e1 : ∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i)) =
      ∑ i ∈ stageSet b1wSt k, cellComplexPair (Wc i t) (torusHkValueCLM (ψ i)) :=
    Finset.sum_congr rfl fun i _ => by rw [hWt i]
  have e2 : ∑ i, ‖W₀ i‖ ^ 2 = ∑ i, ‖Wc i F.a‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hWa i]
  rw [e1, e2]
  exact (hbd k hk t ht ψ).trans (plain_final_le hA0 hB hc₀0 hP hT hκ0 (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hk)

/-- The plain pass from the adjoint propagator bound alone. -/
theorem plainStage_of_adjointKernel (hK2 : CellAdjointKernelHsStatement) :
    PlainStageStatement.{u, v} :=
  plainStageAssembly stageFamilyZone hK2

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the marks band at the fibre level

`marksBandFibreAssembly : MarksBandFibreAssembly`. From the plain pass and the marks kernel: the
terminal stage means are the pairings with the constant `1` (`marksMean_frame_le`), the plain pass
at `t = F.b` with the marks kernel gives `κ(t₀, t₀ + S) ≤ A e^{-cS}`. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The reserve `J_*` of the marks band covers the ladder of the plain pass with `s₀ = max d + 3`. -/
theorem marksBand_reserve {Nw : ℕ} (m : ℕ) (d Ks : Fin Nw → ℕ) :
    b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d := by
  have hsup : Finset.univ.sup d ≤ ∑ l, d l :=
    Finset.sup_le fun l hl => Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hl
  unfold b1wLadderTop wordReserveJstar wordReserveKstar wordReserveN
  omega

/-- The marks band at the fibre level from the plain pass and the marks kernel. -/
theorem marksBandFibreAssembly : MarksBandFibreAssembly.{u, v} := by
  intro hPS hMK K
  obtain ⟨gP, hgP, hPK⟩ := hPS K
  obtain ⟨A, c, hA, hc, hMKK⟩ := hMK K
  obtain ⟨gW, hgW, hWK⟩ := isScaledStage_exists.{u, v} K
  refine ⟨min gP gW, lt_min hgP hgW, ?_⟩
  intro Nw D m d Ks pos
  obtain ⟨C, Q, hC, hPQ⟩ := hPK Nw D m d Ks pos (Finset.univ.sup d + 3) A le_rfl hA
  refine ⟨Real.sqrt (b1wM Nw m Ks) * C * A, c, Q, ?_, hc, ?_⟩
  · have : 0 < Real.sqrt (b1wM Nw m Ks) := Real.sqrt_pos.2 (by
      unfold b1wM; positivity)
    positivity
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hpkg hab hbb hS hθ hξ
  have hJ' : b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤ F.J :=
    (marksBand_reserve m d Ks).trans hJ
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  obtain ⟨κ, hκ, hκle⟩ := hMKK F.η F.t₀ F.Sw F.ϖ F.G F.v F.reg hpkg F.piece.hGm F.piece.hv V hb
    F.piece.hη F.piece.hη1 hS θ hθ hξ
  have hκ1 : IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ := by
    have key : ∀ a b : ℝ, a = F.t₀ → b = F.t₀ + F.Sw →
        IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb a b A κ := by
      rintro a b rfl rfl
      exact isFibreKernel_shift (b1wCoeff_eq_real F θ).symm hκ
    exact key _ _ hab hbb
  obtain ⟨Wf, hWf⟩ := hWK (m := m) (Ks := Ks) (F.mono (min_le_right gP gW)) θ
  have hma : F.a ∈ Icc F.a F.b := ⟨le_rfl, F.ordered⟩
  have hmb : F.b ∈ Icc F.a F.b := ⟨F.ordered, le_rfl⟩
  have hP := hPQ (F.mono (min_le_left gP gW)) θ hlet hJ' hθ V hb κ hκ1 (fun i => Wf i F.a)
    (hWf F.a hma) F.b hmb (fun i => Wf i F.b) (hWf F.b hmb)
  have hfr := marksMean_frame_le F θ (fun i => Wf i F.a) (fun i => Wf i F.b) (hWf F.a hma)
    (hWf F.b hmb) (fun k => b1wLadderAt Nw (Finset.univ.sup d + 3) d Ks k)
    (B := C * peFactor F.η ^ Q * (1 + (F.b - F.a)) ^ Q * κ F.a F.b) hP
  have hba : F.b - F.a = F.Sw := by rw [hab, hbb]; ring
  have hκle' : κ F.a F.b ≤ A * Real.exp (-c * F.Sw) := by rw [hab, hbb]; exact hκle
  have hpe : 0 < peFactor F.η := by
    unfold peFactor
    have := F.piece.hη
    positivity
  have hS0 : 0 ≤ F.Sw := by linarith
  refine hfr.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  rw [hba]
  have hκ0 : 0 ≤ κ F.a F.b := (hκ1.pos F.a F.b).le
  have hBle : C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * κ F.a F.b ≤
      C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * (A * Real.exp (-c * F.Sw)) :=
    mul_le_mul_of_nonneg_left hκle' (by positivity)
  have hsM : 0 ≤ Real.sqrt (b1wM Nw m Ks) := Real.sqrt_nonneg _
  calc (b1wM Nw m Ks : ℝ) * (C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * κ F.a F.b) ^ 2
      = (Real.sqrt (b1wM Nw m Ks) * (C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * κ F.a F.b)) ^ 2 := by
        rw [mul_pow (Real.sqrt _), Real.sq_sqrt (Nat.cast_nonneg _)]
    _ ≤ (Real.sqrt (b1wM Nw m Ks) *
        (C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * (A * Real.exp (-c * F.Sw)))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hsM (by positivity)) (mul_le_mul_of_nonneg_left hBle hsM) 2
    _ = _ := by ring

end AVRegularity.CycleWords.Discard
end
end
