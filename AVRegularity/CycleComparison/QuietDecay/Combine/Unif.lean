-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Parts.MetricMean
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.QuietDecay.Lift.Recentre
import AVRegularity.CycleComparison.QuietDecay.Assembly.LevelAmp

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Generic tools for combining the part bounds of the quiet source: the bridge from word-based
vector jets to `ptJet`, and the vanishing of `ptJet` of the zero field. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem comb_ptJet_zero (X : Vec 2) (p q : ℕ) :
    ptJet (fun (_ _ : Vec 2) => (0 : E)) X p q = 0 := by
  unfold ptJet
  simp

theorem comb_ptJet_ite (c : Prop) [Decidable c] (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) :
    ptJet (fun X z => if c then Ψ X z else 0) X p q ≤ if c then ptJet Ψ X p q else 0 := by
  by_cases hc : c
  · simp [hc]
  · simp [hc, comb_ptJet_zero]

/-- The word `L²` norm is the vector jet at the corresponding lists. -/
theorem comb_word_eq_vecJ {sX sZ p0 q0 : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (hp : p0 ≤ sX) (hq : q0 ≤ sZ) (α : DerivativeWord2 p0) (β : DerivativeWord2 q0) (X : Vec 2) :
    eLpNorm (fun z => orderedDerivative α (fun X' => orderedDerivative β (F X') z) X) 2
      (volume.restrict AVenhance.unitCube) = vecJ F X (List.ofFn α) (List.ofFn β) := by
  have hl : (List.ofFn α).length ≤ sX := by simpa using hp
  have hm : (List.ofFn β).length ≤ sZ := by simpa using hq
  unfold vecJ
  have h := edge_orderedDerivative_comm hF (List.ofFn α) (List.ofFn β) hl hm X
  have e : ∀ z, fastDerivs (List.ofFn β) (slowDerivs (List.ofFn α) F X) z =
      orderedDerivative α (fun X' => orderedDerivative β (F X') z) X := by
    intro z
    rw [h z]
    simp only [orderedDerivative_eq_derivList, List.ofFn_get]
  simp only [e]

/-- `ptJet` is bounded by `2^(p+q)` times a bound for the vector jets of exact word lengths. -/
theorem comb_ptJet_le_vecJ {sX sZ p0 q0 : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (hp : p0 ≤ sX) (hq : q0 ≤ sZ) (X : Vec 2) {M : ℝ≥0∞}
    (h : ∀ l m : List (Fin 2), l.length = p0 → m.length = q0 → vecJ F X l m ≤ M) :
    ptJet F X p0 q0 ≤ 2 ^ (p0 + q0) * M := by
  refine ptJet_le_of_words_le hF hp hq X fun α β => ?_
  rw [comb_word_eq_vecJ hF hp hq α β X]
  exact h _ _ (by simp) (by simp)

/-- The vector jet at lists of lengths `≤ (sX, sZ)` is at most the `ptJet` of the lengths. -/
theorem comb_vecJ_le_ptJet {sX sZ : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (l m : List (Fin 2)) (hl : l.length ≤ sX) (hm : m.length ≤ sZ) (X : Vec 2) :
    vecJ F X l m ≤ ptJet F X l.length m.length := edge_vecJ_le_ptJet hF l m hl hm X
end

/-! The five parts of the quiet source of a centred monomial test field, as fields (the `v`
component), with their box smoothness and their `ptJet` bounds (from the vector jet bounds of the
parts). -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The hypotheses shared by the parts of the quiet source at one time and slow point. -/
structure CombHyp (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ)
    (hh p q N sX sZ : ℕ) (Γ : ℝ) (X : Vec 2) : Prop where
  D2 : 2 ≤ D
  N1 : 1 ≤ N
  sX3 : p + 3 ≤ sX
  sXD : p + D ≤ sX
  sZD : q + D ≤ sZ
  η0 : 0 ≤ Q.η
  η1 : Q.η ≤ 1
  drift : ∀ z, Real.sqrt Q.η • Q.v σ z = 0
  quiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z'
  edge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
    ContDiff ℝ ((p + N : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z)
  Gs : ∀ i j, ContDiff ℝ ((p + N + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)
  Gder : ∀ i j r, r ≤ p + N + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ Γ
  box : ∀ g, g ≤ hh → ∀ n' m (α : DerivativeWord2 m) w u',
    IsBoxSmooth sX sZ (fun X z => Cc g n' m α σ X z w u')

section Fields

variable (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ) (hh n : ℕ)
  (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (v : ι)

/-- Part A: the first cross operator. -/
def combA : Vec 2 → Vec 2 → h v := fun X' z => cellB1 Q.η Q.G Q.v σ (liftApply (n - 1)
  (Cc hh (n - 1)) (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) X' z v

/-- Part B: the second cross operator. -/
def combB : Vec 2 → Vec 2 → h v := fun X' z => cellB2 Q.η Q.G σ (liftApply (n - 2)
  (Cc hh (n - 2)) (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) X' z v

/-- Part D: the edge source of the lower lift action. -/
def combD (j : ℕ) : Vec 2 → Vec 2 → h v := fun X' z => sourceCoeff Q.edge Q.η j σ (liftApply (n - j)
  (Cc (hh - 1) (n - j)) (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) X' z v

/-- Parts C and E: the lift action on the quiet mean. -/
def combM (j : ℕ) (pr : ℕ × ℕ) : Vec 2 → Vec 2 → h v := fun X' z => liftApply j (Cc pr.1 j)
  (fun s X' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) pr.2 (n - j) s X')
  σ X' z v

end Fields
end

/-! Leibniz bound for a finite sum of slow scalar multiples, and the slow jets of the recentring
weights `c_S`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem comb_smul_sum_le {κ : Type*} [Fintype κ] (cT : κ → Vec 2 → ℝ)
    (FT : κ → Vec 2 → Vec 2 → E) {p q p0 q0 : ℕ} (hp0 : p0 ≤ p) (hq0 : q0 ≤ q) (X : Vec 2)
    (hc : ∀ T, ContDiff ℝ (p : ℕ∞) (cT T)) (hF : ∀ T, IsBoxSmooth p q (FT T)) {Cb : ℝ}
    (hCb : ∀ T, ∀ i, i ≤ p0 → ‖iteratedFDeriv ℝ i (cT T) X‖ ≤ Cb) {M : ℝ≥0∞}
    (hM : ∀ T, ∀ i, i ≤ p0 → ptJet (FT T) X (p0 - i) q0 ≤ M) :
    ptJet (fun X' z => ∑ T, cT T X' • FT T X' z) X p0 q0 ≤
      (Fintype.card κ : ℝ≥0∞) * (2 ^ p0 * ENNReal.ofReal Cb) * M := by
  refine (ptJet_sum_le Finset.univ (fun T _ => (hF T).smul_slow (hc T)) hp0 hq0 X).trans ?_
  have hterm : ∀ T : κ, ptJet (fun X' z => cT T X' • FT T X' z) X p0 q0 ≤
      (2 ^ p0 * ENNReal.ofReal Cb) * M := by
    intro T
    refine (ptJet_smul_le (hF T) hp0 hq0 (hc T) X).trans ?_
    calc _ ≤ ∑ i ∈ Finset.range (p0 + 1), (p0.choose i : ℝ≥0∞) * ENNReal.ofReal Cb * M := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ p0 := by have := Finset.mem_range.1 hi; omega
          refine mul_le_mul' (mul_le_mul' le_rfl ?_) (hM T i hi')
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hCb T i hi')
      _ = (∑ i ∈ Finset.range (p0 + 1), (p0.choose i : ℝ≥0∞)) * ENNReal.ofReal Cb * M := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = _ := by
          congr 3
          have := Nat.sum_range_choose p0
          exact_mod_cast this
  calc _ ≤ ∑ _T : κ, (2 ^ p0 * ENNReal.ofReal Cb) * M := Finset.sum_le_sum fun T _ => hterm T
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The slow jets of the recentring weights at the centre. -/
theorem comb_cS_iter_le (X : Vec 2) (α : List (Fin 2)) (S : Finset (Fin α.length)) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (cS X α S) X‖ ≤ 2 ^ i * (α.length.factorial : ℝ) := by
  have hg : ContDiff ℝ (i : ℕ∞) (cS X α S) := contDiff_cS X α S _
  refine (edge_norm_iteratedFDeriv_le_words hg X).trans ?_
  have : ∀ w : DerivativeWord2 i, ‖orderedDerivative w (cS X α S) X‖ ≤
      (α.length.factorial : ℝ) := fun w => norm_orderedDerivative_cS_le X X (by simp) w α S
  refine (Finset.sum_le_sum fun w _ => this w).trans (le_of_eq ?_)
  rw [Finset.sum_const, AVRegularity.card_derivativeWord2]
  simp
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The shared hypotheses `CombHyp` of the part bounds, from the premises of the lift setting, the
lift sequence and quietness at one quiet time. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The pointwise slow jets of the metric at a time of the window, from `hset.G_jets`. -/
theorem comb_Gder
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {σ : ℝ} (hσ : σ ∈ Icc t₀ t₁) {r P : ℕ} (hr : r ≤ P) (hP : P ≤ qs) (i j : Fin 2) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ metricΓ CG P := by
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hset.ρ_pos.le hset.E_pos.le
  have hGs : ContDiff ℝ (qs : ℕ∞) (fun X' => Q.G σ X') :=
    contDiff_pi.2 fun j => contDiff_pi.2 fun k => hset.G_smooth σ hσ j k
  have hGw : ContDiff ℝ (r : ℕ∞) (fun X' => Q.G σ X') := hGs.of_le (by exact_mod_cast (by omega))
  have hGj : ContDiff ℝ (r : ℕ∞) (fun X' => Q.G σ X' i) := contDiff_pi.1 hGw i
  have hGjk : ContDiff ℝ (r : ℕ∞) (fun X' => Q.G σ X' i j) := contDiff_pi.1 hGj j
  refine (norm_iteratedFDeriv_pi_proj_le hGj j).trans
    ((norm_iteratedFDeriv_pi_proj_le hGw i).trans ?_)
  have hJ1 := hset.G_jets r (by omega)
  have hle : ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X') X‖ₑ ≤ ENNReal.ofReal (CG r * lam ^ r) :=
    le_trans (le_trans (le_iSup (fun Y' => ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X') Y'‖ₑ) X)
      (le_iSup₂ (f := fun t' _ => ⨆ Y' : Vec 2,
        ‖iteratedFDeriv ℝ r (fun X' => Q.G t' X') Y'‖ₑ) σ hσ)) hJ1
  have hreal : ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X') X‖ ≤ max (CG r * lam ^ r) 0 := by
    rw [← ofReal_norm] at hle
    have := (ENNReal.ofReal_le_ofReal_iff').1 hle
    rcases this with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_right _ _)
  refine hreal.trans (le_trans ?_ (le_metricΓ CG (r := r) hr))
  have hlp : lam ^ r ≤ 1 := pow_le_one₀ hlam0 hset.lam_le
  have hl0 : 0 ≤ lam ^ r := pow_nonneg hlam0 _
  rcases le_total 0 (CG r) with hc | hc
  · refine max_le_max ?_ le_rfl
    calc CG r * lam ^ r ≤ CG r * 1 := by gcongr
      _ = CG r := mul_one _
  · exact max_le (le_trans (mul_nonpos_of_nonpos_of_nonneg hc hl0) (le_max_right _ _))
      (le_max_right _ _)

omit [DecidableEq ι] in
/-- **The shared hypotheses of the part bounds** at a quiet time `σ`. -/
theorem comb_hyp_of_setting
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {σ : ℝ} (hσ : σ ∈ S) {hh p q : ℕ} (hhH : hh ≤ H) (X : Vec 2) (hpK : p + 1 ≤ K)
    (hqF : q + D ≤ max (k + 1) (L + 2)) (hpq : p + N + 2 ≤ qs) :
    CombHyp Q Cc σ hh p q N (K + D + 2) (max (k + 1) (L + 2)) (metricΓ CG (p + N + 1)) X := by
  have hσI : σ ∈ Icc t₀ t₁ := hS hσ
  have hD2 := hset.D_ge
  have hN1 := hset.N_ge
  refine ⟨hD2, hN1, by omega, by omega, hqF, ?_, hset.η_le, fun z => hq.1 σ hσ z,
    fun v w d γ hγ α X z z' => hq.2 v w d γ hγ α σ hσ X z z', ?_, ?_, ?_, ?_⟩
  · rw [hset.η_eq]; exact div_nonneg hset.ν_pos.le hset.B_pos.le
  · intro v w d γ hγ α z
    exact (((hset.coeff_smooth v w d γ hγ α σ hσI).isSlowSmooth).1 z).of_le
      (by exact_mod_cast (by omega))
  · intro i j
    exact (hset.G_smooth σ hσI i j).of_le (by exact_mod_cast (by omega))
  · intro i j r hr
    exact comb_Gder hset hσI hr (by omega) i j X
  · intro g hg n' m α w u'
    exact (hseq.2.2.2.2.2.1 g (hg.trans hhH) n' m α w u' σ hσI).1

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Box smoothness of the parts of the quiet source of a centred monomial test field. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem comb_box_lift (c : LiftCoeff ι h) (N : ℕ) (b : Vec 2 → ∀ i, h i) (σ : ℝ) {s t : ℕ}
    (hc : ∀ w m (α : DerivativeWord2 m) u', IsBoxSmooth s t (fun X z => c m α σ X z w u'))
    (hb : ContDiff ℝ ((s + N : ℕ) : ℕ∞) b) :
    IsBoxSmooth s t (liftApply N c (fun _ => b) σ) :=
  edge_isBoxSmooth_pi fun w => edge_isBoxSmooth_liftApply c N b σ w (fun m α u' => hc w m α u') hb

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {σ : ℝ}
  {hh p q N sX sZ : ℕ} {Γ : ℝ} {X : Vec 2} (H : CombHyp Q Cc σ hh p q N sX sZ Γ X)
  {n : ℕ} (β : List (Fin 2)) (u : ι) (x : h u) (v : ι)

include H

theorem comb_boxA : IsBoxSmooth p q (combA Q Cc σ hh n X β u x v) := by
  have := H.sX3; have := H.sZD; have := H.D2; have := H.N1
  have hΦ : IsBoxSmooth (p + 1) (q + 1) (liftApply (n - 1) (Cc hh (n - 1))
      (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) :=
    comb_box_lift _ _ _ _ (fun w m α u' => (H.box hh le_rfl (n - 1) m α w u').mono (by omega)
      (by omega)) (edge_contDiff_testField X β u x _)
  have hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j) := fun i j =>
    (H.Gs i j).of_le (by exact_mod_cast (by omega))
  exact (metric_isBoxSmooth_cellB1 hΦ H.drift hG).clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

theorem comb_boxB : IsBoxSmooth p q (combB Q Cc σ hh n X β u x v) := by
  have := H.sX3; have := H.sZD; have := H.D2; have := H.N1
  have hΦ : IsBoxSmooth (p + 2) q (liftApply (n - 2) (Cc hh (n - 2))
      (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) :=
    comb_box_lift _ _ _ _ (fun w m α u' => (H.box hh le_rfl (n - 2) m α w u').mono (by omega)
      (by omega)) (edge_contDiff_testField X β u x _)
  have hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j) := fun i j =>
    (H.Gs i j).of_le (by exact_mod_cast (by omega))
  exact (metric_isBoxSmooth_cellB2 hΦ hG).clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

theorem comb_boxD (j : ℕ) : IsBoxSmooth p q (combD Q Cc σ hh n X β u x v j) := by
  have := H.sXD; have := H.sZD; have := H.D2; have := H.N1
  have hΦ : IsBoxSmooth sX sZ (liftApply (n - j) (Cc (hh - 1) (n - j))
      (fun _ => fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) :=
    comb_box_lift _ _ _ _ (fun w m α u' => H.box (hh - 1) (by omega) (n - j) m α w u')
      (edge_contDiff_testField X β u x _)
  have ha : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z) := fun v u d γ hγ α z =>
    (H.edge v u d γ hγ α z).of_le (by exact_mod_cast (by omega))
  exact (edge_isBoxSmooth_sourceCoeff Q.edge Q.η σ H.quiet hΦ j (by omega) (by omega)
    (by omega) (by omega) ha).clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

theorem comb_meanOp_smooth {j : ℕ} (hjn : j < n) (hnN : n ≤ N) (p2 : ℕ) :
    ContDiff ℝ ((p + j : ℕ) : ℕ∞) (fun X' => quietMeanOp Q
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) p2 (n - j) σ X') := by
  classical
  by_cases h0 : p2 = 0
  · subst h0
    have hGs : ∀ i k, ContDiff ℝ ((p + j + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i k) := fun i k =>
      (H.Gs i k).of_le (by exact_mod_cast (by omega))
    have hGd : ∀ i k, Differentiable ℝ (fun X => Q.G σ X i k) := fun i k =>
      (hGs i k).differentiable (by simp)
    have e : (fun X' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 0
        (n - j) σ X') = fun X' => (if n - j = 2 then metricF2 Q σ X β X' else 0) •
          (Pi.single u x : ∀ i, h i) :=
      funext fun X' => metric_quietMeanOp_mono Q σ X β u x (n - j) hGd X'
    rw [e]
    have hfq : ContDiff ℝ ((p + j : ℕ) : ℕ∞)
        (fun X' : Vec 2 => (if n - j = 2 then metricF2 Q σ X β X' else 0)) := by
      by_cases h2 : n - j = 2
      · simp only [h2, ↓reduceIte]
        have hΦ : IsBoxSmooth (p + j + 2) 0 (fun X'' (_ : Vec 2) => monoF X β X'') :=
          metric_isBoxSmooth_slowOnly (contDiff_monoF X _ β)
        exact (metric_isBoxSmooth_cellB2 (η := Q.η) (G := Q.G) (t := σ) hΦ hGs).contDiff_slow 0
      · simp only [h2, ↓reduceIte]
        exact contDiff_const
    exact hfq.smul (contDiff_const (c := (Pi.single u x : ∀ i, h i)))
  · by_cases h1 : p2 = 1
    · subst h1
      have e : (fun X' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1
          (n - j) σ X') = fun X' => -sourceCoeff Q.edge Q.η (n - j) σ (fun X'' _ =>
            (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0 :=
        funext fun X' => edge_quietMeanOp_one Q _ (n - j) σ X'
      rw [e]
      exact edge_E_smooth Q σ H.quiet X β u x (p := p) (n := n) (j := j) (p0 := p) le_rfl hjn
        (fun v w d γ hγ α z => (H.edge v w d γ hγ α z).of_le
          (by exact_mod_cast (by omega)))
    · have e : (fun X' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) p2
          (n - j) σ X') = fun _ => 0 := by
        funext X'; simp [quietMeanOp, h0, h1]
      rw [e]; exact contDiff_const

theorem comb_boxM {j : ℕ} (hjn : j < n) (hnN : n ≤ N) (pr : ℕ × ℕ) (hpr : pr.1 ≤ hh) :
    IsBoxSmooth p q (combM Q Cc σ n X β u x v j pr) := by
  have := H.sXD; have := H.sZD
  have e : combM Q Cc σ n X β u x v j pr = fun X' z => liftApply j (Cc pr.1 j) (fun _ X'' =>
      quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) pr.2 (n - j) σ X'')
      σ X' z v := by
    funext X' z
    simp only [combM, liftApply]
  rw [e]
  exact edge_isBoxSmooth_liftApply (Cc pr.1 j) j _ σ v
    (fun m α u' => (H.box pr.1 hpr j m α v u').mono (by omega) (by omega))
    (comb_meanOp_smooth H β u x hjn hnN pr.2)
end

/-! The quiet source of a centred monomial test field (`v` component) is the signed sum of the
five parts; its box smoothness and its `ptJet` bound. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

section Fields

variable (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ) (hh n : ℕ)
  (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (v : ι)

/-- The `v` component of the quiet source of the centred monomial test field. -/
def combF : Vec 2 → Vec 2 → h v := fun X' z =>
  quietSource Q Cc (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) hh n σ X' z v

def combGA : Vec 2 → Vec 2 → h v := fun X' z => if 2 ≤ n then combA Q Cc σ hh n X β u x v X' z else 0

def combGB : Vec 2 → Vec 2 → h v := fun X' z => if 3 ≤ n then combB Q Cc σ hh n X β u x v X' z else 0

def combGD : Vec 2 → Vec 2 → h v := fun X' z => if hh = 0 then 0 else
  ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n), combD Q Cc σ hh n X β u x v j X' z

def combGM : Vec 2 → Vec 2 → h v := fun X' z => ∑ j ∈ Finset.Icc 1 (n - 2),
  ∑ pr ∈ Finset.HasAntidiagonal.antidiagonal hh, combM Q Cc σ n X β u x v j pr X' z

theorem combF_eq : combF Q Cc σ hh n X β u x v = fun X' z =>
    ((-(combGA Q Cc σ hh n X β u x v X' z) - combGB Q Cc σ hh n X β u x v X' z) +
      combGD Q Cc σ hh n X β u x v X' z) + combGM Q Cc σ hh n X β u x v X' z := by
  funext X' z
  simp only [combF, combGA, combGB, combGD, combGM, quietSource, combA, combB, combD, combM]
  by_cases h1 : 2 ≤ n <;> by_cases h2 : 3 ≤ n <;> by_cases h3 : hh = 0 <;>
    simp [h1, h2, h3, Finset.sum_apply, Pi.add_apply]

end Fields

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {σ : ℝ}
  {hh p q N sX sZ : ℕ} {Γ : ℝ} {X : Vec 2} (H : CombHyp Q Cc σ hh p q N sX sZ Γ X)
  {n : ℕ} (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (v : ι) {p0 q0 : ℕ}
  (hp0 : p0 ≤ p) (hq0 : q0 ≤ q)

include H

theorem comb_boxGA : IsBoxSmooth p q (combGA Q Cc σ hh n X β u x v) := by
  unfold combGA
  by_cases h2 : 2 ≤ n
  · simp only [h2, ↓reduceIte]; exact comb_boxA H β u x v
  · simp only [h2, ↓reduceIte]; exact IsBoxSmooth.zero

theorem comb_boxGB : IsBoxSmooth p q (combGB Q Cc σ hh n X β u x v) := by
  unfold combGB
  by_cases h2 : 3 ≤ n
  · simp only [h2, ↓reduceIte]; exact comb_boxB H β u x v
  · simp only [h2, ↓reduceIte]; exact IsBoxSmooth.zero

theorem comb_boxGD : IsBoxSmooth p q (combGD Q Cc σ hh n X β u x v) := by
  unfold combGD
  by_cases h2 : hh = 0
  · simp only [h2, ↓reduceIte]; exact IsBoxSmooth.zero
  · simp only [h2, ↓reduceIte]
    exact IsBoxSmooth.sum _ fun j _ => comb_boxD H β u x v j

theorem comb_boxGM (hnN : n ≤ N) : IsBoxSmooth p q (combGM Q Cc σ hh n X β u x v) := by
  unfold combGM
  refine IsBoxSmooth.sum _ fun j hj => IsBoxSmooth.sum _ fun pr hpr => ?_
  have hj' := Finset.mem_Icc.1 hj
  have hpr' := Finset.HasAntidiagonal.mem_antidiagonal.1 hpr
  exact comb_boxM H β u x v (by omega) hnN pr (by omega)

theorem comb_boxF (hnN : n ≤ N) : IsBoxSmooth p q (combF Q Cc σ hh n X β u x v) := by
  rw [combF_eq]
  exact (((comb_boxGA H β u x v).neg.sub (comb_boxGB H β u x v)).add
    (comb_boxGD H β u x v)).add (comb_boxGM H β u x v hnN)
end

/-! The uniform constants of the combined source bound: the explicit constants of the parts, summed
over all parameters in their ranges (degrees, word lengths). -/

/-- The sum of the constants of the part (A). -/
def srcKA (p q N : ℕ) (Γ : ℝ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), metricCA p q a Γ k

/-- The sum of the constants of the part (B). -/
def srcKB (p q N : ℕ) (Γ : ℝ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), metricCB p q a Γ k

/-- The sum of the constants of the part (C). -/
def srcKC (p N : ℕ) (Γ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), metricCC p j Γ k

/-- The sum of the constants of the part (D). -/
def srcKD (p q N D : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    (edgeCD D p q n j (List.replicate k 0) : ℝ)

/-- The sum of the constants of the part (E). -/
def srcKE (p q N D : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    (edgeCE D p q n j (List.replicate k 0) : ℝ)

/-- The total constant of the parts. -/
def srcK (p q N D : ℕ) (Γ : ℝ) : ℝ :=
  srcKA p q N Γ + srcKB p q N Γ + srcKC p N Γ + srcKD p q N D + srcKE p q N D

/-- **The constant of the combined source bound.** It depends only on `p, q, N, D` and the metric
bound `Γ = Σ_{r ≤ p+N+1} max (C_G r) 0`. -/
def srcConst (p q N D : ℕ) (CG : ℕ → ℝ) : ℝ :=
  2 ^ N * (4 ^ p * (N.factorial : ℝ)) * 2 ^ (p + q) *
    srcK p q N D (metricΓ CG (p + N + 1))

theorem srcKA_nonneg (p q N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ srcKA p q N Γ :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => by unfold metricCA; positivity

theorem srcKB_nonneg (p q N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ srcKB p q N Γ :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => by unfold metricCB; positivity

theorem srcKC_nonneg (p N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ srcKC p N Γ :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => by unfold metricCC; positivity

theorem srcKD_nonneg (p q N D : ℕ) : 0 ≤ srcKD p q N D :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Nat.cast_nonneg _

theorem srcKE_nonneg (p q N D : ℕ) : 0 ≤ srcKE p q N D :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Nat.cast_nonneg _

theorem srcK_nonneg (p q N D : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ srcK p q N D Γ :=
  add_nonneg (add_nonneg (add_nonneg (add_nonneg (srcKA_nonneg p q N hΓ) (srcKB_nonneg p q N hΓ))
    (srcKC_nonneg p N hΓ)) (srcKD_nonneg p q N D)) (srcKE_nonneg p q N D)

theorem srcConst_nonneg (p q N D : ℕ) (CG : ℕ → ℝ) : 0 ≤ srcConst p q N D CG := by
  unfold srcConst
  have := srcK_nonneg p q N D (metricΓ_nonneg CG (p + N + 1))
  positivity

theorem comb_le_sum2 (f : ℕ → ℕ → ℝ) (hf : ∀ a k, 0 ≤ f a k) {N a k : ℕ} (ha : a ≤ N)
    (hk : k ≤ N) :
    f a k ≤ ∑ a' ∈ Finset.range (N + 1), ∑ k' ∈ Finset.range (N + 1), f a' k' := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun a' => ∑ k' ∈ Finset.range (N + 1), f a' k')
    (fun a' _ => Finset.sum_nonneg fun k' _ => hf a' k') (Finset.mem_range.2 (by omega) : a ∈ _))
  exact Finset.single_le_sum (f := fun k' => f a k') (fun k' _ => hf a k')
    (Finset.mem_range.2 (by omega) : k ∈ _)

theorem comb_le_sum3 (f : ℕ → ℕ → ℕ → ℝ) (hf : ∀ a b k, 0 ≤ f a b k) {N a b k : ℕ} (ha : a ≤ N)
    (hb : b ≤ N) (hk : k ≤ N) :
    f a b k ≤ ∑ a' ∈ Finset.range (N + 1), ∑ b' ∈ Finset.range (N + 1),
      ∑ k' ∈ Finset.range (N + 1), f a' b' k' := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun a' => ∑ b' ∈ Finset.range (N + 1), ∑ k' ∈ Finset.range (N + 1), f a' b' k')
    (fun a' _ => Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun k' _ => hf a' b' k')
    (Finset.mem_range.2 (by omega) : a ∈ _))
  exact comb_le_sum2 (fun b' k' => f a b' k') (fun b' k' => hf a b' k') hb hk

theorem comb_CA_le {p q N a k : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) (ha : a ≤ N) (hk : k ≤ N) :
    metricCA p q a Γ k ≤ srcKA p q N Γ :=
  comb_le_sum2 (fun a k => metricCA p q a Γ k) (fun a k => by unfold metricCA; positivity) ha hk

theorem comb_CB_le {p q N a k : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) (ha : a ≤ N) (hk : k ≤ N) :
    metricCB p q a Γ k ≤ srcKB p q N Γ :=
  comb_le_sum2 (fun a k => metricCB p q a Γ k) (fun a k => by unfold metricCB; positivity) ha hk

theorem comb_CC_le {p N j k : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) (hj : j ≤ N) (hk : k ≤ N) :
    metricCC p j Γ k ≤ srcKC p N Γ :=
  comb_le_sum2 (fun j k => metricCC p j Γ k) (fun a k => by unfold metricCC; positivity) hj hk

theorem comb_CD_le {p q N D n j : ℕ} (β : List (Fin 2)) (hn : n ≤ N) (hj : j ≤ N)
    (hk : β.length ≤ N) : (edgeCD D p q n j β : ℝ) ≤ srcKD p q N D := by
  have e : edgeCD D p q n j β = edgeCD D p q n j (List.replicate β.length 0) := by
    simp [edgeCD]
  rw [e]
  unfold srcKD
  exact comb_le_sum3 (fun n j k => (edgeCD D p q n j (List.replicate k 0) : ℝ))
    (fun _ _ _ => Nat.cast_nonneg _) hn hj hk

theorem comb_CE_le {p q N D n j : ℕ} (β : List (Fin 2)) (hn : n ≤ N) (hj : j ≤ N)
    (hk : β.length ≤ N) : (edgeCE D p q n j β : ℝ) ≤ srcKE p q N D := by
  have e : edgeCE D p q n j β = edgeCE D p q n j (List.replicate β.length 0) := by
    simp [edgeCE, edgeCm]
  rw [e]
  unfold srcKE
  exact comb_le_sum3 (fun n j k => (edgeCE D p q n j (List.replicate k 0) : ℝ))
    (fun _ _ _ => Nat.cast_nonneg _) hn hj hk

/-! The `ptJet` bounds of the parts of the quiet source of a centred monomial test field, from the
vector jet bounds of the parts. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {σ : ℝ}
  {hh p q N sX sZ : ℕ} {Γ : ℝ} {X : Vec 2} (H : CombHyp Q Cc σ hh p q N sX sZ Γ X)
  {n : ℕ} (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (v : ι) {p0 q0 : ℕ}
  (hp0 : p0 ≤ p) (hq0 : q0 ≤ q)

include H hx hp0 hq0

theorem comb_ptJetA (hnN : n ≤ N) :
    ptJet (combA Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (metricCA p q (n - 1) Γ β.length) *
        blkJ Cc hh (n - 1) σ v u (p + 1) (q + 1)) := by
  have := H.sX3; have := H.sZD; have := H.D2; have := H.N1
  refine comb_ptJet_le_vecJ (comb_boxA H β u x v) hp0 hq0 X fun l m hl hm => ?_
  exact metric_cellB1_le Q Cc hh (n - 1) σ (sX := sX) (sZ := sZ) (p := p) (q := q) v u l m
    (by omega) (by omega) (by omega) (by omega) H.η1 H.drift
    (fun i j => (H.Gs i j).of_le (by exact_mod_cast (by omega))) X
    (fun i j r hr => H.Gder i j r (by omega))
    (fun w m α u' => H.box hh le_rfl (n - 1) m α w u') β x hx

theorem comb_ptJetB (hnN : n ≤ N) :
    ptJet (combB Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (metricCB p q (n - 2) Γ β.length) *
        blkJ Cc hh (n - 2) σ v u (p + 2) q) := by
  have := H.sX3; have := H.sZD; have := H.D2; have := H.N1
  refine comb_ptJet_le_vecJ (comb_boxB H β u x v) hp0 hq0 X fun l m hl hm => ?_
  exact metric_cellB2_le Q Cc hh (n - 2) σ (sX := sX) (sZ := sZ) (p := p) (q := q) v u l m
    (by omega) (by omega) (by omega) (by omega) H.η0 H.η1
    (fun i j => (H.Gs i j).of_le (by exact_mod_cast (by omega))) X
    (fun i j r hr => H.Gder i j r (by omega))
    (fun w m α u' => H.box hh le_rfl (n - 2) m α w u') β x hx

theorem comb_ptJetD {j : ℕ} (hjD : j ≤ D) :
    ptJet (combD Q Cc σ hh n X β u x v j) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (edgeCD D p q n j β : ℝ) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
        blkJ Cc (hh - 1) (n - j) σ w u (p + j) (q + D)) := by
  have := H.sXD; have := H.sZD; have := H.D2; have := H.N1
  refine comb_ptJet_le_vecJ (comb_boxD H β u x v j) hp0 hq0 X fun l m hl hm => ?_
  exact edge_D_bound Q Cc σ H.η1 H.quiet hjD
    (fun v w d γ hγ α z => (H.edge v w d γ hγ α z).of_le (by exact_mod_cast (by omega)))
    (fun m α w u' => (H.box (hh - 1) (by omega) (n - j) m α w u').mono (by omega) (by omega))
    X β u x hx (by omega) (by omega) v

theorem comb_ptJetM0 {j : ℕ} (hjn : j < n) (hnN : n ≤ N) :
    ptJet (combM Q Cc σ n X β u x v j (hh, 0)) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (metricCC p j Γ β.length) * blkJ Cc hh j σ v u p q) := by
  have := H.sXD; have := H.sZD; have := H.D2; have := H.N1
  refine comb_ptJet_le_vecJ (comb_boxM H β u x v hjn hnN (hh, 0) le_rfl) hp0 hq0 X
    fun l m hl hm => ?_
  exact metric_mean_le Q Cc hh j n σ (sX := sX) (sZ := sZ) (p := p) (q := q) v u l m
    (by omega) (by omega) (by omega) (by omega) H.η0 H.η1
    (fun i k => (H.Gs i k).of_le (by exact_mod_cast (by omega))) X
    (fun i k r hr => H.Gder i k r (by omega))
    (fun m α u' => H.box hh le_rfl j m α v u') β x hx

theorem comb_ptJetM1 {j : ℕ} (hh1 : 1 ≤ hh) (hjn : j < n) (hnN : n ≤ N) :
    ptJet (combM Q Cc σ n X β u x v j (hh - 1, 1)) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
        blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n)) := by
  have := H.sXD; have := H.sZD; have := H.D2; have := H.N1
  refine comb_ptJet_le_vecJ (comb_boxM H β u x v hjn hnN (hh - 1, 1) (by simp)) hp0 hq0 X
    fun l m hl hm => ?_
  exact edge_E_bound Q Cc σ H.η1 H.quiet hjn
    (fun v w d γ hγ α z => (H.edge v w d γ hγ α z).of_le (by exact_mod_cast (by omega)))
    (fun m α w u' => (H.box (hh - 1) (by omega) j m α w u').mono (by omega) (by omega))
    X β u x hx (by omega) (by omega) v

omit H hx hp0 hq0 in
theorem comb_combM_zero {j : ℕ} (pr : ℕ × ℕ) (h2 : 2 ≤ pr.2) :
    combM Q Cc σ n X β u x v j pr = fun _ _ => 0 := by
  funext X' z
  have e : (fun X'' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) pr.2
      (n - j) σ X'') = fun _ => 0 := by
    funext X''; simp [quietMeanOp, show pr.2 ≠ 0 by omega, show pr.2 ≠ 1 by omega]
  simp only [combM, liftApply]
  rw [e]
  simp [orderedDerivative_eq_derivList, metric_derivList_zero]
end

/-! The `ptJet` bound of the quiet source of a centred monomial test field, termwise in the
five parts. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {σ : ℝ}
  {hh p q N sX sZ : ℕ} {Γ : ℝ} {X : Vec 2} (H : CombHyp Q Cc σ hh p q N sX sZ Γ X)
  {n : ℕ} (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (v : ι) {p0 q0 : ℕ}
  (hp0 : p0 ≤ p) (hq0 : q0 ≤ q)

include H hx hp0 hq0

theorem comb_ptJetGM (hnN : n ≤ N) :
    ptJet (combGM Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      ∑ j ∈ Finset.Icc 1 (n - 2), (ENNReal.ofReal (metricCC p j Γ β.length) *
          blkJ Cc hh j σ v u p q + (if hh = 0 then 0 else
        ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
          blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n))) := by
  unfold combGM
  rw [Finset.mul_sum]
  refine (ptJet_sum_le _ (fun j hj => IsBoxSmooth.sum _ fun pr hpr => ?_) hp0 hq0 X).trans
    (Finset.sum_le_sum fun j hj => ?_)
  · have hj' := Finset.mem_Icc.1 hj
    have hpr' := Finset.HasAntidiagonal.mem_antidiagonal.1 hpr
    exact comb_boxM H β u x v (by omega) hnN pr (by omega)
  have hj' := Finset.mem_Icc.1 hj
  refine (ptJet_sum_le _ (fun pr hpr => ?_) hp0 hq0 X).trans ?_
  · have hpr' := Finset.HasAntidiagonal.mem_antidiagonal.1 hpr
    exact comb_boxM H β u x v (by omega) hnN pr (by omega)
  set BC := 2 ^ (p0 + q0) * (ENNReal.ofReal (metricCC p j Γ β.length) *
    blkJ Cc hh j σ v u p q) with hBC
  set BE := 2 ^ (p0 + q0) * (ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
    blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n)) with hBE
  have key : ∀ pr ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ptJet (combM Q Cc σ n X β u x v j pr) X p0 q0 ≤
        (if pr = (hh, 0) then BC else 0) + (if 1 ≤ hh ∧ pr = (hh - 1, 1) then BE else 0) := by
    intro pr hpr
    have hpr' := Finset.HasAntidiagonal.mem_antidiagonal.1 hpr
    obtain ⟨a, b⟩ := pr
    simp only at hpr'
    by_cases hb0 : b = 0
    · subst hb0
      have : a = hh := by omega
      subst this
      simp only [ite_true, Prod.mk.injEq]
      refine (comb_ptJetM0 H β u x hx v hp0 hq0 (by omega) hnN).trans ?_
      exact le_self_add
    by_cases hb1 : b = 1
    · subst hb1
      have ha : a = hh - 1 := by omega
      subst ha
      have h1 : 1 ≤ hh := by omega
      have e1 : ¬ ((hh - 1, 1) = (hh, 0)) := by simp
      simp only [e1, ite_false, zero_add, h1, true_and, ite_true]
      exact comb_ptJetM1 H β u x hx v hp0 hq0 h1 (by omega) hnN
    · rw [comb_combM_zero β u x v (j := j) (n := n) (a, b) (by simp only; omega)]
      rw [comb_ptJet_zero]
      exact bot_le
  refine (Finset.sum_le_sum key).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ (hh, 0)]
  have hmem : (hh, 0) ∈ Finset.HasAntidiagonal.antidiagonal hh := by simp
  simp only [hmem, ite_true]
  have hR : 2 ^ (p0 + q0) * (ENNReal.ofReal (metricCC p j Γ β.length) *
      blkJ Cc hh j σ v u p q + (if hh = 0 then 0 else
        ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
          blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n))) =
      BC + (if hh = 0 then 0 else BE) := by
    by_cases hh0 : hh = 0
    · simp [hh0, hBC]
    · simp [hh0, hBC, hBE, mul_add]
  rw [hR]
  refine add_le_add le_rfl ?_
  by_cases hh0 : hh = 0
  · subst hh0
    simp
  · have hmem2 : (hh - 1, 1) ∈ Finset.HasAntidiagonal.antidiagonal hh := by
      simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    have h1 : 1 ≤ hh := by omega
    simp only [h1, true_and, hh0, ite_false]
    rw [Finset.sum_ite_eq' _ (hh - 1, 1)]
    simp only [hmem2, ite_true]
    exact le_rfl

theorem comb_ptJetGD :
    ptJet (combGD Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (if hh = 0 then 0 else
        ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
          ENNReal.ofReal (edgeCD D p q n j β : ℝ) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
            blkJ Cc (hh - 1) (n - j) σ w u (p + j) (q + D)) := by
  unfold combGD
  by_cases hh0 : hh = 0
  · simp [hh0, comb_ptJet_zero]
  · simp only [hh0, ↓reduceIte]
    rw [Finset.mul_sum]
    refine (ptJet_sum_le _ (fun j _ => comb_boxD H β u x v j) hp0 hq0 X).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' := Finset.mem_filter.1 hj
    have hjD : j ≤ D := by
      have := Finset.mem_range.1 hj'.1
      have h2 : min D n ≤ D := min_le_left _ _
      have h3 : j < min D n + 1 := this
      omega
    exact comb_ptJetD H β u x hx v hp0 hq0 hjD

theorem comb_ptJetF (hnN : n ≤ N) :
    ptJet (combF Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      ((if 2 ≤ n then ENNReal.ofReal (metricCA p q (n - 1) Γ β.length) *
          blkJ Cc hh (n - 1) σ v u (p + 1) (q + 1) else 0) +
        (if 3 ≤ n then ENNReal.ofReal (metricCB p q (n - 2) Γ β.length) *
          blkJ Cc hh (n - 2) σ v u (p + 2) q else 0) +
        (if hh = 0 then 0 else
          ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
            ENNReal.ofReal (edgeCD D p q n j β : ℝ) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
              blkJ Cc (hh - 1) (n - j) σ w u (p + j) (q + D)) +
        ∑ j ∈ Finset.Icc 1 (n - 2), (ENNReal.ofReal (metricCC p j Γ β.length) *
            blkJ Cc hh j σ v u p q + (if hh = 0 then 0 else
          ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
            blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n)))) := by
  have hbA := comb_boxGA H β u x v (n := n)
  have hbB := comb_boxGB H β u x v (n := n)
  have hbD := comb_boxGD H β u x v (n := n)
  have hbM := comb_boxGM H β u x v hnN
  have hA : ptJet (combGA Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (if 2 ≤ n then ENNReal.ofReal (metricCA p q (n - 1) Γ β.length) *
          blkJ Cc hh (n - 1) σ v u (p + 1) (q + 1) else 0) := by
    unfold combGA
    refine (comb_ptJet_ite _ _ X p0 q0).trans ?_
    by_cases h2 : 2 ≤ n
    · simp only [h2, ↓reduceIte]; exact comb_ptJetA H β u x hx v hp0 hq0 hnN
    · simp [h2]
  have hB : ptJet (combGB Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (if 3 ≤ n then ENNReal.ofReal (metricCB p q (n - 2) Γ β.length) *
          blkJ Cc hh (n - 2) σ v u (p + 2) q else 0) := by
    unfold combGB
    refine (comb_ptJet_ite _ _ X p0 q0).trans ?_
    by_cases h2 : 3 ≤ n
    · simp only [h2, ↓reduceIte]; exact comb_ptJetB H β u x hx v hp0 hq0 hnN
    · simp [h2]
  have hD := comb_ptJetGD H β u x hx v hp0 hq0 (n := n)
  have hM := comb_ptJetGM H β u x hx v hp0 hq0 hnN
  rw [combF_eq]
  refine (ptJet_add_le (((hbA.neg).sub hbB).add hbD) hbM hp0 hq0 X).trans ?_
  refine (add_le_add (ptJet_add_le ((hbA.neg).sub hbB) hbD hp0 hq0 X) le_rfl).trans ?_
  refine (add_le_add (add_le_add (ptJet_sub_le hbA.neg hbB hp0 hq0 X) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (ptJet_neg_le hbA hp0 hq0 X) le_rfl) le_rfl)
    le_rfl).trans ?_
  rw [mul_add, mul_add, mul_add]
  exact add_le_add (add_le_add (add_le_add hA hB) hD) hM
end

/-! The uniform `ptJet` bound of the quiet source of a centred monomial test field: all part terms
are placed in the common sums of block jets of the uniform orders `(p + D, q + D)`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The right side of the combined source bound (without the constant). -/
def combBsum (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ) (hh n N p q : ℕ)
    (X : Vec 2) (u v : ι) : ℝ≥0∞ :=
  ∑ n' ∈ Finset.Ico 1 n, blkJ Cc hh n' σ v u (p + D) (q + D)
    + (if hh = 0 then 0 else ∑ n' ∈ Finset.Icc 1 N,
        (∑ w, edgeEnv Q σ X v w (p + N) * blkJ Cc (hh - 1) n' σ w u (p + D) (q + D)
          + ∑ w, blkJ Cc (hh - 1) n' σ v w (p + D) (q + D) * edgeEnv Q σ X w u (p + N)))

theorem comb_sum_comp_le {D : ℕ} (n N : ℕ) (hnN : n ≤ N) (g : ℕ → ℝ≥0∞) :
    ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n), g (n - j) ≤
      ∑ n' ∈ Finset.Icc 1 N, g n' := by
  rw [← Finset.sum_image (f := g) (g := fun j => n - j)]
  · refine Finset.sum_le_sum_of_subset ?_
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
    have := (Finset.mem_filter.1 hj).2
    simp only [Finset.mem_Icc]; omega
  · intro a ha b hb hab
    have h1 := (Finset.mem_filter.1 ha).2
    have h2 := (Finset.mem_filter.1 hb).2
    simp only at hab
    omega

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {σ : ℝ}
  {hh p q N sX sZ : ℕ} {Γ : ℝ} {X : Vec 2} (H : CombHyp Q Cc σ hh p q N sX sZ Γ X)
  {n : ℕ} (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (v : ι) {p0 q0 : ℕ}
  (hp0 : p0 ≤ p) (hq0 : q0 ≤ q) (hΓ0 : 0 ≤ Γ) (hβ : β.length ≤ N) (hn1 : 1 ≤ n) (hnN : n ≤ N)

include H hx hp0 hq0 hΓ0 hβ hn1 hnN

theorem comb_ptJetF_unif :
    ptJet (combF Q Cc σ hh n X β u x v) X p0 q0 ≤ 2 ^ (p0 + q0) *
      (ENNReal.ofReal (srcK p q N D Γ) * combBsum Q Cc σ hh n N p q X u v) := by
  have hD2 := H.D2
  have hN1 := H.N1
  refine (comb_ptJetF H β u x hx v hp0 hq0 hnN).trans (mul_le_mul' le_rfl ?_)
  set S1 : ℝ≥0∞ := ∑ n' ∈ Finset.Ico 1 n, blkJ Cc hh n' σ v u (p + D) (q + D) with hS1
  set gD : ℕ → ℝ≥0∞ := fun n' => ∑ w, edgeEnv Q σ X v w (p + N) *
    blkJ Cc (hh - 1) n' σ w u (p + D) (q + D) with hgD
  set gE : ℕ → ℝ≥0∞ := fun n' => ∑ w, blkJ Cc (hh - 1) n' σ v w (p + D) (q + D) *
    edgeEnv Q σ X w u (p + N) with hgE
  set SD : ℝ≥0∞ := ∑ n' ∈ Finset.Icc 1 N, gD n' with hSD
  set SE : ℝ≥0∞ := ∑ n' ∈ Finset.Icc 1 N, gE n' with hSE
  have hB : combBsum Q Cc σ hh n N p q X u v = S1 + (if hh = 0 then 0 else SD + SE) := by
    unfold combBsum
    rw [Finset.sum_add_distrib]
  rw [hB]
  have hA : (if 2 ≤ n then ENNReal.ofReal (metricCA p q (n - 1) Γ β.length) *
      blkJ Cc hh (n - 1) σ v u (p + 1) (q + 1) else 0) ≤ ENNReal.ofReal (srcKA p q N Γ) * S1 := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ↓reduceIte]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (comb_CA_le hΓ0 (by omega) hβ)) ?_
      refine (blkJ_mono Cc hh (n - 1) σ v u (S := p + 1) (S' := p + D) (F := q + 1) (F' := q + D)
        (by omega) (by omega)).trans ?_
      exact Finset.single_le_sum (f := fun n' => blkJ Cc hh n' σ v u (p + D) (q + D))
        (fun _ _ => bot_le) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    · simp [h2]
  have hB2 : (if 3 ≤ n then ENNReal.ofReal (metricCB p q (n - 2) Γ β.length) *
      blkJ Cc hh (n - 2) σ v u (p + 2) q else 0) ≤ ENNReal.ofReal (srcKB p q N Γ) * S1 := by
    by_cases h2 : 3 ≤ n
    · simp only [h2, ↓reduceIte]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (comb_CB_le hΓ0 (by omega) hβ)) ?_
      refine (blkJ_mono Cc hh (n - 2) σ v u (S := p + 2) (S' := p + D) (F := q) (F' := q + D)
        (by omega) (by omega)).trans ?_
      exact Finset.single_le_sum (f := fun n' => blkJ Cc hh n' σ v u (p + D) (q + D))
        (fun _ _ => bot_le) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    · simp [h2]
  have hD : (if hh = 0 then 0 else
      ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
        ENNReal.ofReal (edgeCD D p q n j β : ℝ) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
          blkJ Cc (hh - 1) (n - j) σ w u (p + j) (q + D)) ≤
      ENNReal.ofReal (srcKD p q N D) * (if hh = 0 then 0 else SD) := by
    by_cases hh0 : hh = 0
    · simp [hh0]
    · simp only [hh0, ↓reduceIte]
      calc _ ≤ ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
            ENNReal.ofReal (srcKD p q N D) * gD (n - j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' := Finset.mem_filter.1 hj
            have hjD : j ≤ D := by
              have h3 : j < min D n + 1 := Finset.mem_range.1 hj'.1
              have h2 : min D n ≤ D := min_le_left _ _
              omega
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal (comb_CD_le β hnN (by omega) hβ)) ?_
            refine Finset.sum_le_sum fun w _ => mul_le_mul'
              (edgeEnv_mono Q σ X v w (by omega)) (blkJ_mono Cc (hh - 1) (n - j) σ w u (S := p + j) (S' := p + D) (F := q + D) (F' := q + D)
                (by omega) le_rfl)
        _ = ENNReal.ofReal (srcKD p q N D) * ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
              gD (n - j) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul' le_rfl (comb_sum_comp_le n N hnN gD)
  have hM : ∑ j ∈ Finset.Icc 1 (n - 2), (ENNReal.ofReal (metricCC p j Γ β.length) *
          blkJ Cc hh j σ v u p q + (if hh = 0 then 0 else
        ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
          blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n))) ≤
      ENNReal.ofReal (srcKC p N Γ) * S1 +
        ENNReal.ofReal (srcKE p q N D) * (if hh = 0 then 0 else SE) := by
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · calc _ ≤ ∑ j ∈ Finset.Icc 1 (n - 2), ENNReal.ofReal (srcKC p N Γ) *
            blkJ Cc hh j σ v u (p + D) (q + D) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' := Finset.mem_Icc.1 hj
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (comb_CC_le hΓ0 (by omega) hβ))
              (blkJ_mono Cc hh j σ v u (S := p) (S' := p + D) (F := q) (F' := q + D)
                (by omega) (by omega))
        _ = ENNReal.ofReal (srcKC p N Γ) * ∑ j ∈ Finset.Icc 1 (n - 2),
              blkJ Cc hh j σ v u (p + D) (q + D) := by rw [Finset.mul_sum]
        _ ≤ _ := by
            refine mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset ?_)
            intro j hj
            have hj' := Finset.mem_Icc.1 hj
            exact Finset.mem_Ico.2 ⟨hj'.1, by omega⟩
    · by_cases hh0 : hh = 0
      · simp [hh0]
      · simp only [hh0, ↓reduceIte]
        calc _ ≤ ∑ j ∈ Finset.Icc 1 (n - 2), ENNReal.ofReal (srcKE p q N D) * gE j := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj' := Finset.mem_Icc.1 hj
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal (comb_CE_le β hnN (by omega) hβ)) ?_
              exact Finset.sum_le_sum fun w _ => mul_le_mul'
                (blkJ_mono Cc (hh - 1) j σ v w (S := p) (S' := p + D) (F := q) (F' := q + D)
                  (by omega) (by omega)) (edgeEnv_mono Q σ X w u (by omega))
          _ = ENNReal.ofReal (srcKE p q N D) * ∑ j ∈ Finset.Icc 1 (n - 2), gE j := by
              rw [Finset.mul_sum]
          _ ≤ _ := by
              refine mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset ?_)
              intro j hj
              have hj' := Finset.mem_Icc.1 hj
              exact Finset.mem_Icc.2 ⟨hj'.1, by omega⟩
  -- assemble
  have hK : ENNReal.ofReal (srcKA p q N Γ) + ENNReal.ofReal (srcKB p q N Γ) +
      ENNReal.ofReal (srcKC p N Γ) ≤ ENNReal.ofReal (srcK p q N D Γ) := by
    rw [← ENNReal.ofReal_add (srcKA_nonneg p q N hΓ0) (srcKB_nonneg p q N hΓ0),
      ← ENNReal.ofReal_add (add_nonneg (srcKA_nonneg p q N hΓ0) (srcKB_nonneg p q N hΓ0))
        (srcKC_nonneg p N hΓ0)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold srcK
    have := srcKD_nonneg p q N D
    have := srcKE_nonneg p q N D
    linarith
  have hKD : ENNReal.ofReal (srcKD p q N D) ≤ ENNReal.ofReal (srcK p q N D Γ) := by
    refine ENNReal.ofReal_le_ofReal ?_
    unfold srcK
    have := srcKA_nonneg p q N hΓ0
    have := srcKB_nonneg p q N hΓ0
    have := srcKC_nonneg p N hΓ0
    have := srcKE_nonneg p q N D
    linarith
  have hKE : ENNReal.ofReal (srcKE p q N D) ≤ ENNReal.ofReal (srcK p q N D Γ) := by
    refine ENNReal.ofReal_le_ofReal ?_
    unfold srcK
    have := srcKA_nonneg p q N hΓ0
    have := srcKB_nonneg p q N hΓ0
    have := srcKC_nonneg p N hΓ0
    have := srcKD_nonneg p q N D
    linarith
  set K := ENNReal.ofReal (srcK p q N D Γ)
  calc _ ≤ (ENNReal.ofReal (srcKA p q N Γ) * S1 + ENNReal.ofReal (srcKB p q N Γ) * S1) +
        ENNReal.ofReal (srcKD p q N D) * (if hh = 0 then 0 else SD) +
        (ENNReal.ofReal (srcKC p N Γ) * S1 +
          ENNReal.ofReal (srcKE p q N D) * (if hh = 0 then 0 else SE)) :=
        add_le_add (add_le_add (add_le_add hA hB2) hD) hM
    _ = (ENNReal.ofReal (srcKA p q N Γ) + ENNReal.ofReal (srcKB p q N Γ) +
          ENNReal.ofReal (srcKC p N Γ)) * S1 +
        (ENNReal.ofReal (srcKD p q N D) * (if hh = 0 then 0 else SD) +
          ENNReal.ofReal (srcKE p q N D) * (if hh = 0 then 0 else SE)) := by ring
    _ ≤ K * S1 + (K * (if hh = 0 then 0 else SD) + K * (if hh = 0 then 0 else SE)) :=
        add_le_add (mul_le_mul' hK le_rfl) (add_le_add (mul_le_mul' hKD le_rfl)
          (mul_le_mul' hKE le_rfl))
    _ = K * (S1 + (if hh = 0 then 0 else SD + SE)) := by
        by_cases hh0 : hh = 0
        · simp [hh0]
        · simp only [hh0, ↓reduceIte]; ring
end

end AVRegularity.QuietDecay
end
