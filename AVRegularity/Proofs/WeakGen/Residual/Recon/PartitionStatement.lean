-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Definitions.Families.ActualFamily
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.EntryWeakAssembly.QuietMarginPlan
public import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
public import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionPassage
import AVRegularity.Applications.Global.CompactRangeMain

@[expose] public noncomputable section

section
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The six-summand count in abstract reals**. With `e = ε_M`, `a = ε_{i-1}`,
`b = ε_i` in `(0, 1]`, `a ≤ e`, `b ≤ 2 a^q`, the contrast `x = b/a`, the cleanup factor
`Z = √T/(b/√κ) · x`, a flux price `tt ≤ e^{P+S+1}` (`S = q^{J_w}`), a lower bound
`cL e^S ≤ a` and `N(q-1) > P + 2`: the first five summands of the bill are at most
`weakPriceConst N s cL · e^{P+1}`, with `s = √T₀ √2`.

The degenerate cases are included: `T = 0` gives `Z = 0`; `S = 0` is the case without the inverse
power; `N = 1` is allowed by the lemmas (the hypothesis `N(q-1) > P+2` then forces `q > 3`, which
no admissible `q` satisfies). -/

/-- The named constant of the six-summand count (the partition term is separate). -/
def weakPriceConst (N : ℕ) (s cL : ℝ) : ℝ := 2 ^ N + 1 + 1 + 2 ^ N * s + s / cL

/-- A power of a smaller base: `a^r ≤ e^r'` for `a ≤ e ≤ 1`, `0 ≤ r'`, `r' ≤ r`. -/
theorem weakPrice_rpow_le {a e r r' : ℝ} (ha : 0 < a) (hae : a ≤ e) (he1 : e ≤ 1)
    (hr' : r' ≤ r) (hr0 : 0 ≤ r) : a ^ r ≤ e ^ r' := by
  have he : 0 < e := lt_of_lt_of_le ha hae
  exact (Real.rpow_le_rpow ha.le hae hr0).trans
    (Real.rpow_le_rpow_of_exponent_ge he he1 hr')

/-- The contrast bound `x = b/a ≤ 2 a^{q-1}`. -/
theorem weakPrice_contrast_le {a b q : ℝ} (ha : 0 < a) (hbq : b ≤ 2 * a ^ q) :
    b / a ≤ 2 * a ^ (q - 1) := by
  rw [div_le_iff₀ ha, Real.rpow_sub_one ha.ne']
  have : a ^ q / a * a = a ^ q := div_mul_cancel₀ _ ha.ne'
  nlinarith [this]

/-- The contrast power: `x^N ≤ 2^N a^{N(q-1)}`. -/
theorem weakPrice_contrast_pow_le {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hbq : b ≤ 2 * a ^ q)
    (N : ℕ) : (b / a) ^ N ≤ 2 ^ N * a ^ ((q - 1) * N) := by
  have h := pow_le_pow_left₀ (div_pos hb ha).le (weakPrice_contrast_le ha hbq) N
  have e : (a ^ (q - 1)) ^ N = a ^ ((q - 1) * N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  rwa [mul_pow, e] at h

/-- The cleanup factor in closed form. -/
theorem weakPrice_Z_eq {a b T κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) :
    Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1 = Real.sqrt T * Real.sqrt κ / a := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  rw [pow_one]
  field_simp

/-- The cleanup factor is at most `s/a`. -/
theorem weakPrice_Z_le {a b T T₀ κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (hT : T ≤ T₀) :
    Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1 ≤ Real.sqrt T₀ * Real.sqrt 2 / a := by
  rw [weakPrice_Z_eq ha hb hκ]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (Real.sqrt_le_sqrt hT) (Real.sqrt_le_sqrt hκ2) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)) ha.le

theorem weakPrice_Z_nonneg {a b T κ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1 := by
  positivity

/-- **The first five summands of the bill are at most `weakPriceConst · e^{P+1}`.** -/
theorem weakPrice_five_le {e a b q P S T T₀ κ tt cL : ℝ} {N : ℕ}
    (he1 : e ≤ 1) (ha : 0 < a) (hae : a ≤ e) (hb : 0 < b) (hba : b ≤ a)
    (hbq : b ≤ 2 * a ^ q) (_hq : 1 < q) (hP : 0 ≤ P) (hS : 0 ≤ S)
    (hN : P + 2 < N * (q - 1)) (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hT : T ≤ T₀)
    (hcL : 0 < cL) (hlow : cL * e ^ S ≤ a) (htt0 : 0 ≤ tt) (htt : tt ≤ e ^ (P + S + 1)) :
    (b / a) ^ N + Real.sqrt (κ / κ) * tt + (b / a) ^ 2 * tt +
        (b / a) ^ N * (Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1) +
        (b / a) ^ 2 * (Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1) * tt ≤
      weakPriceConst N (Real.sqrt T₀ * Real.sqrt 2) cL * e ^ (P + 1) := by
  have he : 0 < e := lt_of_lt_of_le ha hae
  set s := Real.sqrt T₀ * Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hx0 : 0 ≤ b / a := (div_pos hb ha).le
  have hx1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N * (q - 1) := by linarith
    exact_mod_cast Nat.pos_of_ne_zero (by rintro rfl; simp at this)
  have hNq : P + 2 < (q - 1) * N := by linarith
  -- e^{P+1}
  have hE1 : 0 < e ^ (P + 1) := Real.rpow_pos_of_pos he _
  have hEle : ∀ r, P + 1 ≤ r → e ^ r ≤ e ^ (P + 1) := fun r hr =>
    Real.rpow_le_rpow_of_exponent_ge he he1 hr
  -- tt ≤ e^{P+1}
  have htt1 : tt ≤ e ^ (P + 1) := htt.trans (hEle _ (by linarith))
  -- summand 1
  have h1 : (b / a) ^ N ≤ 2 ^ N * e ^ (P + 1) := by
    refine (weakPrice_contrast_pow_le ha hb hbq N).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact weakPrice_rpow_le ha hae he1 (by linarith) (by linarith)
  -- summand 2
  have h2 : Real.sqrt (κ / κ) * tt ≤ e ^ (P + 1) := by
    rw [div_self hκ.ne', Real.sqrt_one, one_mul]; exact htt1
  -- summand 3
  have h3 : (b / a) ^ 2 * tt ≤ e ^ (P + 1) := by
    have : (b / a) ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
    nlinarith [mul_le_mul this htt1 htt0 zero_le_one]
  -- cleanup factor
  have hZ := weakPrice_Z_le ha hb hκ hκ2 hT
  have hZ0 := weakPrice_Z_nonneg (T := T) (κ := κ) ha hb
  set Z := Real.sqrt T / (b / Real.sqrt κ) * (b / a) ^ 1 with hZd
  -- summand 4
  have h4 : (b / a) ^ N * Z ≤ 2 ^ N * s * e ^ (P + 1) := by
    have hpow := weakPrice_contrast_pow_le ha hb hbq N
    have hA : a ^ ((q - 1) * N) / a ≤ e ^ (P + 1) := by
      rw [← Real.rpow_sub_one ha.ne']
      exact weakPrice_rpow_le ha hae he1 (by linarith) (by linarith)
    calc (b / a) ^ N * Z ≤ (2 ^ N * a ^ ((q - 1) * N)) * (s / a) :=
          mul_le_mul hpow hZ hZ0 (by positivity)
      _ = 2 ^ N * s * (a ^ ((q - 1) * N) / a) := by ring
      _ ≤ 2 ^ N * s * e ^ (P + 1) := mul_le_mul_of_nonneg_left hA (by positivity)
  -- summand 5
  have h5 : (b / a) ^ 2 * Z * tt ≤ s / cL * e ^ (P + 1) := by
    have hx2 : (b / a) ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
    have hES : 0 < e ^ S := Real.rpow_pos_of_pos he _
    have hZtt : Z * tt ≤ s / a * e ^ (P + S + 1) :=
      mul_le_mul hZ htt htt0 (by positivity)
    have hinv : s / a ≤ s / (cL * e ^ S) :=
      div_le_div_of_nonneg_left hs0 (by positivity) hlow
    have hsplit : e ^ (P + S + 1) = e ^ (P + 1) * e ^ S := by
      rw [← Real.rpow_add he]; congr 1; ring
    calc (b / a) ^ 2 * Z * tt = (b / a) ^ 2 * (Z * tt) := by ring
      _ ≤ 1 * (Z * tt) := mul_le_mul_of_nonneg_right hx2 (mul_nonneg hZ0 htt0)
      _ = Z * tt := one_mul _
      _ ≤ s / a * e ^ (P + S + 1) := hZtt
      _ ≤ s / (cL * e ^ S) * e ^ (P + S + 1) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = s / cL * e ^ (P + 1) := by rw [hsplit]; field_simp
  unfold weakPriceConst
  nlinarith [h1, h2, h3, h4, h5, hE1]

/-! **Scale facts for the price of the weak reconstruction bill**: the lower bound
`ε_{M+k} ≥ c_k ε_M^{q^k}` with the named constants `weakPriceLowerConst q k`, in plain `ocEpsilon`
terms. The degenerate cases are included: `k = 0` is the identity with constant `1`; the constants
lie in `(0, 1]` and decrease with `k`. -/

section
open AVRegularity

/-- The constants of the lower chain `ε_{M+k} ≥ c_k ε_M^{q^k}`: `c_0 = 1`, `c_{k+1} = c_k^q/2`. -/
def weakPriceLowerConst (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => weakPriceLowerConst q k ^ q / 2

theorem weakPriceLowerConst_pos (q : ℝ) (k : ℕ) : 0 < weakPriceLowerConst q k := by
  induction k with
  | zero => simp [weakPriceLowerConst]
  | succ k ih =>
    simp only [weakPriceLowerConst]
    exact div_pos (Real.rpow_pos_of_pos ih q) (by norm_num)

theorem weakPriceLowerConst_le_one {q : ℝ} (hq : 1 < q) (k : ℕ) :
    weakPriceLowerConst q k ≤ 1 := by
  induction k with
  | zero => simp [weakPriceLowerConst]
  | succ k ih =>
    simp only [weakPriceLowerConst]
    have := Real.rpow_le_one (weakPriceLowerConst_pos q k).le ih (by linarith : (0 : ℝ) ≤ q)
    linarith

theorem weakPriceLowerConst_antitone {q : ℝ} (hq : 1 < q) :
    Antitone (weakPriceLowerConst q) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h0 := weakPriceLowerConst_pos q k
  have h1 := weakPriceLowerConst_le_one hq k
  simp only [weakPriceLowerConst]
  have : weakPriceLowerConst q k ^ q ≤ weakPriceLowerConst q k ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge h0 h1 hq.le
  rw [Real.rpow_one] at this
  linarith

/-- **The lower chain of the scales**: `c_k ε_M^{q^k} ≤ ε_{M+k}` for `M ≥ 1`. -/
theorem weakPrice_eps_lower {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {M : ℕ} (hM : 1 ≤ M)
    (k : ℕ) :
    weakPriceLowerConst q k * ocEpsilon q Λ M ^ (q ^ k) ≤ ocEpsilon q Λ (M + k) := by
  have he := (Scales.epsilon_basic (m := M) hq hΛ).1
  induction k with
  | zero => simp [weakPriceLowerConst]
  | succ k ih =>
    have hge := Applications.ocEpsilon_succ_ge (q := q) (Λ := Λ) (m := M + k) hq hΛ (by omega)
    have hc := weakPriceLowerConst_pos q k
    have hnn : 0 ≤ weakPriceLowerConst q k * ocEpsilon q Λ M ^ (q ^ k) :=
      mul_nonneg hc.le (Real.rpow_nonneg he.le _)
    have h1 := Real.rpow_le_rpow hnn ih (by linarith : (0 : ℝ) ≤ q)
    have h2 : (weakPriceLowerConst q k * ocEpsilon q Λ M ^ (q ^ k)) ^ q =
        weakPriceLowerConst q k ^ q * ocEpsilon q Λ M ^ (q ^ (k + 1)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg he.le _), ← Real.rpow_mul he.le, pow_succ]
    have h3 : weakPriceLowerConst q (k + 1) * ocEpsilon q Λ M ^ (q ^ (k + 1)) ≤
        ocEpsilon q Λ (M + k) ^ q / 2 := by
      simp only [weakPriceLowerConst]
      rw [div_mul_eq_mul_div]
      have := h2 ▸ h1
      linarith
    rw [← add_assoc]
    exact h3.trans hge
end

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! The coefficient bounds: the qualitative boundedness inputs of the weak reconstruction window.
The drift bound is named from the base parameters. The edge bound is a literal finite sum of
zero-order seminorms, independent of the reserve vector. It is a qualitative witness: neither this
bound nor the drift bound occurs in `reconBillConst`. The degenerate cases are included: the empty
family or an edge-free root has edge bound zero; increasing the reserve vector changes only the
admissible orders, never the bound. No quiet-time assertion is needed. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The fixed OC velocity bound; it is chosen before the passage plan and the data. -/
def weakReconDriftBound (B : WeakCoefficientBase) (Λ : ℕ) : ℝ :=
  AVRegularity.Applications.velBound B.α B.q Λ

/-- A named qualitative edge bound on the closed comparison window. There is no choice
from an energy statement or from a statement about the plan. This bound may read the
actual family; it is not a uniform residual price or a constant in the statement. -/
def weakReconEdgeBound (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : ℝ :=
  ∑ v : CompIn (c.stage i).comps, ∑ u : CompIn (c.stage i).comps,
    ∑ d ∈ Finset.Icc 2 c.Dm, ∑ γ : (c.stage i).fam.Γ v u,
      (coefficientSeminorm (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
        ((c.stage i).physCoeff v u γ d)).toReal

/-- Exactly the drift and coefficient clauses consumed by `ReconPhysicalLiftStatement`,
at the weak diffusivity and at any requested reserve vector. -/
def WeakReconBoundsAt (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (K : CompIn (c.stage i).comps → ℕ) (Vb CA : ℝ) : Prop :=
  0 ≤ CA ∧
  (∀ t ∈ Set.Ioc (r.tq i) (r.a + A.T₀), ∀ j,
    AEStronglyMeasurable (fun x => streamVel (c.D.Φ i) t x j)
      (volume.restrict unitCube)) ∧
  (∀ t ∈ Set.Ioc (r.tq i) (r.a + A.T₀), ∀ x j,
    |streamVel (c.D.Φ i) t x j| ≤ Vb) ∧
  (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v u d x,
    ‖edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M) (c.D.eps i)
      (c.D.eps (i - 1)) (fun _ => ()) K v u d t x‖ ≤ CA) ∧
  ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v u d,
    AEStronglyMeasurable (edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M)
      (c.D.eps i) (c.D.eps (i - 1)) (fun _ => ()) K v u d t)
      (volume.restrict unitCube)

/-- Qualitative bounds at named constants, with no energy hypothesis. The finite
edge bound is an auxiliary witness only; all numerical prices remain chosen before Dm. -/
def WeakReconBoundsStatement (plan : WeakPassagePlan) : Prop :=
  WeakPassageCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ K : CompIn (c.stage i).comps → ℕ,
      WeakReconBoundsAt c r i K (weakReconDriftBound B A.Λ) (weakReconEdgeBound c r i)
end

/-! R6b_w. The common certificate gives finite seminorms at every finite order on
non-root stages; the root has no edge. Summing the zeroth seminorms supplies a
qualitative bound, without charging any instance-dependent price to the residual. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly
variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

private theorem weakReconPhysCoeff_regular (hok : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u) (d : ℕ) (a b : ℝ) :
    (∀ t, Continuous ((c.stage i).physCoeff v u γ d t)) ∧
    coefficientSeminorm (c.D.eps (i - 1)) 0 a b ((c.stage i).physCoeff v u γ d) ≠ ⊤ := by
  by_cases hroot : i = c.M + A.Jw
  · subst i
    exact False.elim ((c.construction.2.1.2.2.1 v u).false γ)
  have hall := Reduction.weakData_physCoeff_allOrder R ((hok.1 B).trans c.base_ge)
    ((plan.base_ge B).trans c.base_ge) c.j₀ c.carrier c.M ((hok.2 R c.j₀).trans c.level_ge)
    c.D c.alpha c.q_eq c.base_eq c.profile_eq c.streams c.band c.terminal c.Dm c.order_ge
    c.P c.stage c.construction i hi.le (lt_of_le_of_ne hiJ hroot) v u γ 0 d a b
  have heps : 0 < c.D.eps (i - 1) := by
    simpa only [OCData.eps, c.q_eq, c.base_eq] using
      Applications.eps_pos B.hq.1 ((plan.base_ge B).trans c.base_ge) (m := i - 1)
  exact ⟨fun t => (hall.2.1 t).continuous, hall.2.2.2 _ heps le_rfl⟩

private theorem weakReconEdge_eq_sum (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw)
    (K : CompIn (c.stage i).comps → ℕ) (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders K c.Dm v u) (t : ℝ) (x : Vec 2) :
    edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M) (c.D.eps i)
      (c.D.eps (i - 1)) (fun _ => ()) K v u d t x =
      ∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 t x := by
  rw [(c.stage i).edgeCoefficient_actualFamily]
  have hl := EntryWeakProofs.weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage
    c.construction i hi.le hiJ
  simp only [edgeCoefficient, physicalCoefficient, GenStage.physCoeff, hl,
    weak_passage_kap_eq c i hi.le]

/-- The weak-window drift and edge clauses at their named constants. -/
theorem weakReconBounds (plan : WeakPassagePlan) : WeakReconBoundsStatement plan := by
  intro hok B A R c r i hi hiJ K
  classical
  have hsum0 : ∀ v u d, 0 ≤ ∑ γ : (c.stage i).fam.Γ v u,
      (coefficientSeminorm (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
        ((c.stage i).physCoeff v u γ d)).toReal := fun _ _ _ =>
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  refine ⟨by unfold weakReconEdgeBound; positivity, ?_, ?_, ?_, ?_⟩
  · intro t _ j
    exact ((continuous_apply j).comp ((c.D.hΦ i).vel_continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro t _ x j
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (streamVel (c.D.Φ i) t x) j).trans
      (Applications.streamVel_norm_le B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ
        A.Λ ((plan.base_ge B).trans c.base_ge) c.D.Φ c.streams i t x)
  · intro t ht v u d x
    rw [weakReconEdge_eq_sum c i hi hiJ]
    calc
      ‖∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 t x‖ ≤
          ∑ γ : (c.stage i).fam.Γ v u, ‖(c.stage i).physCoeff v u γ d.1 t x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ γ : (c.stage i).fam.Γ v u,
          (coefficientSeminorm (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
            ((c.stage i).physCoeff v u γ d.1)).toReal := by
        apply Finset.sum_le_sum
        intro γ _
        have hf := (weakReconPhysCoeff_regular hok c i hi hiJ v u γ d.1
          (r.tq i) (r.a + A.T₀)).2
        have h := ENNReal.toReal_mono hf (CycleJointProofs.coefficient_value_le_seminorm
          (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
          ((c.stage i).physCoeff v u γ d.1) t ht x)
        simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using h
      _ ≤ ∑ d' ∈ Finset.Icc 2 c.Dm, ∑ γ : (c.stage i).fam.Γ v u,
          (coefficientSeminorm (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
            ((c.stage i).physCoeff v u γ d')).toReal :=
        Finset.single_le_sum (fun d' _ => hsum0 v u d') (by
          exact (Finset.mem_filter.mp d.2).1)
      _ ≤ ∑ u', ∑ d' ∈ Finset.Icc 2 c.Dm, ∑ γ : (c.stage i).fam.Γ v u',
          (coefficientSeminorm (c.D.eps (i - 1)) 0 (r.tq i) (r.a + A.T₀)
            ((c.stage i).physCoeff v u' γ d')).toReal :=
        Finset.single_le_sum (fun u' _ => Finset.sum_nonneg fun d' _ => hsum0 v u' d')
          (Finset.mem_univ u)
      _ ≤ weakReconEdgeBound c r i :=
        Finset.single_le_sum (fun v' _ => Finset.sum_nonneg fun u' _ =>
          Finset.sum_nonneg fun d' _ => hsum0 v' u' d') (Finset.mem_univ v)
  · intro t _ v u d
    have heq : edgeCoefficient (c.stage i).actualFamily (c.D.κ c.M) (c.D.eps i)
        (c.D.eps (i - 1)) (fun _ => ()) K v u d t =
        fun x => ∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 t x :=
      funext fun x => weakReconEdge_eq_sum c i hi hiJ K v u d t x
    rw [heq]
    exact (continuous_finsetSum _ fun γ _ =>
      (weakReconPhysCoeff_regular hok c i hi hiJ v u γ d.1 (r.tq i) (r.a + A.T₀)).1 t
      ).aestronglyMeasurable
end

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! The partition input of the weak reconstruction window. The lift length is E = epsilon_(i-1),
independently of the coarse radius. Constants come from the existing original-slot partition
factory, before the plan and the ambient cap. The statement is for any finitely smooth coarse field
on the closed window, hence for every Galerkin approximant of the readout. Its left side is the
literal partition field of the window, not a classical time derivative of a lifted weak solution.
The degenerate cases are included: an empty family, no observed pulse, or the zero datum gives zero;
for Jw = 1 only the root passage is used. Original quiet gaps are trimmed; no hypothesis on the
untrimmed quiet set is introduced. -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift CycleComparison.Reconstruction
open Construction.Preservation.FullLift
open EntryWeakProofs AVRegularity.ChartTransport

/-- The partition's consumer orders, fixed from the menu before any plan or instance. -/
structure WeakReconPartitionOrders {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) where
  Acl : ℕ
  Kmax : ℕ
  Lr : ℕ
  Acl_pos : 1 ≤ Acl
  reserve : weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) Acl Kmax ≤ Lr

/-- The finite energy order required by `cycle_residual_partition_differentiated`. -/
def weakReconPartitionOrder {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) : ℕ :=
  4 * (A.Nw + max 2 (1 + A.Jw * A.Nw)) + 2 * O.Acl + 16 + O.Kmax

/-- The native chart budget at the required finite order. -/
def weakReconPartitionChartBound {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) : ℝ :=
  weakChartJetBudget (weakReconPartitionOrder O + 2) 0

/-- Constants from the already proved factory and sum, chosen before the plan. -/
def weakReconPartitionConstants {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) : ℝ × ℝ :=
  let P := weakSlotLiftParams A O.Lr R.sX R.sZ
  let hp := weak_gluing_slot_lift_factory_orders A O.Lr
    ((le_max_left _ _).trans O.reserve) R.sX R.sZ
  let g := weak_gluing_time_transition_sum P hp O.reserve O.Acl_pos
    (weakReconPartitionChartBound O) (weakChartJetBudget_ge_one _ _)
  ⟨g.choose, g.choose_spec.choose⟩

/-- Native flow floor; the only further numerical condition besides the slot-lift floor. -/
def weakReconPartitionFlowFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    (uniform_native_physical_flow_jets B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
      A.Λ hΛ B.ζ B.hζ (weakReconPartitionOrder O + 2)).choose else 0

/-- Floors only: neither a bound selected from the plan nor an energy constant is read. -/
def WeakReconPartitionPlanOK (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) : Prop :=
  WeakPassageCommonOK plan ∧ WeakSlotLiftPlanOK plan (fun R => (orders R).Lr) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakReconPartitionFlowFloor (orders R) ≤ plan.levelFloor R j₀

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The named coefficient Xp in hPB, with the original pulse count and quiet exponential.
It can be inserted as a summand of the common bill; hPM then holds with Cpx = 1. -/
def weakReconPartitionFactor (O : WeakReconPartitionOrders A)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : ℝ :=
  sliceConst (A.Jw * A.Rw) O.Kmax (weakReconPartitionChartBound O) ^ (1 / 2 : ℝ) *
    ((ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀)).card * 2 *
      ∑ j ∈ Finset.range (O.Kmax + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) *
    ((weakReconPartitionConstants O R).1 * (c.D.eps i / Real.sqrt (c.D.κ c.M)) *
      Real.sqrt (1 / ocTau c.D.α c.D.q c.D.Λ i) *
      Real.exp (-((weakReconPartitionConstants O R).2 * ocTau c.D.α c.D.q c.D.Λ i /
        (c.D.eps i / Real.sqrt (c.D.κ c.M)) ^ 2)))

/-- The literal partition sum in the free-length reconstruction window. -/
def weakReconPartitionField (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root))
    (f : WeakField (c.stage i)) : WeakField (c.stage i) :=
  fun t x => ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀),
    deriv (ocCutoff c.D.α c.D.q c.D.Λ i k) t •
      pulsePhysicalLift (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (c.D.eps (i - 1))
        (c.D.eps i) (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / c.D.eps (i - 1))
        A.Nw (A.Jw * A.Rw) (Cc k)
        (ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)) f t x

/-- `hPB` on the weak window at the named raw partition price. The field outside
the closed window is arbitrary; finite regularity and measurability are window-local. -/
def WeakReconPartitionStatement (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) : Prop :=
  WeakReconPartitionPlanOK plan orders →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ sX sZ : ℕ,
  ∀ Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root),
    IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) sX sZ (c.stage i) Cc →
  ∀ rs : ℝ, 0 < rs → rs ≤ c.D.eps i → ∀ f : WeakField (c.stage i),
    (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ContDiff ℝ ((weakReconPartitionOrder (orders R) + 1 : ℕ) : ℕ∞) (f t)) →
    (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), IsZ2Periodic (f t)) →
    Measurable (fun z : ℝ × Vec 2 => if z.1 ∈ Set.Icc (r.tq i) (r.a + A.T₀)
      then f z.1 z.2 else 0) →
    ∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
      (∑ j ∈ Finset.range ((orders R).Kmax + 1), ∑ w : DerivativeWord2 j,
        scalInt (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun x => rs ^ j • orderedDerivative w (weakReconPartitionField c r i Cc f t) x)) ^
            (1 / 2 : ℝ) ≤
      ENNReal.ofReal (weakReconPartitionFactor (orders R) c r i) *
        classicalStrongEnergy (c.D.eps (i - 1)) (c.D.κ c.M)
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (Set.Icc (r.tq i) (r.a + A.T₀)) (weakReconPartitionOrder (orders R)) f

end AVRegularity.Providers.WeakGen.Residual
end
