-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
public import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainComponentTest

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The finite derivative maps are independent of the carrier order and obey word composition. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Changing the bookkeeping order of the carrier does not change the derivative coefficients. -/
theorem plainDerivativeCoefficients_order_independent (N L M : ℕ) {r : ℕ}
    (w : DerivativeWord2 r) (c : CoupledPlainCoefficients (h := h) N) :
    plainDerivativeCoefficients N L w c = plainDerivativeCoefficients N M w c := by
  funext a
  rw [plainDerivativeCoefficients_apply, plainDerivativeCoefficients_apply,
    plainInitialCoefficients_component, plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
    ((derivativeTorusHk w (coupledPlainSynthesis N a.1 (L + r) c)).val (valueIndex2 L)) =
    inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
      ((derivativeTorusHk w (coupledPlainSynthesis N a.1 (M + r) c)).val (valueIndex2 M))
  rw [derivativeTorusHk_value_slot, derivativeTorusHk_value_slot]
  congr 1
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N a.1 (L + r) c ⟨⟨r, by omega⟩, w⟩).trans
    (coupledPlainSynthesis_jet_ae N a.1 (M + r) c ⟨⟨r, by omega⟩, w⟩).symm

/-- Appending one derivative direction composes the finite coefficient maps. -/
theorem plainDerivativeCoefficients_snoc (N : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (k : Fin 2) (c : CoupledPlainCoefficients (h := h) N) :
    plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k)
      (plainDerivativeCoefficients N 0 w c) =
      plainDerivativeCoefficients N 0 (Fin.snoc w k) c := by
  rw [plainDerivativeCoefficients_order_independent N 0 1 w c]
  funext a
  rw [plainDerivativeCoefficients_apply N 0 (Fin.snoc w k) c,
    plainDerivativeCoefficients_apply N 0 (fun _ : Fin 1 => k)
      (plainDerivativeCoefficients N 1 w c),
    plainInitialCoefficients_component, plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
    ((derivativeTorusHk (fun _ : Fin 1 => k)
      (coupledPlainSynthesis N a.1 1 (plainDerivativeCoefficients N 1 w c))).val (valueIndex2 0)) =
    inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
      ((derivativeTorusHk (Fin.snoc w k)
        (coupledPlainSynthesis N a.1 (0 + (r + 1)) c)).val (valueIndex2 0))
  rw [derivativeTorusHk_value_slot, plainDerivativeCoefficients_synthesis,
    derivativeTorusHk_apply, derivativeTorusHk_value_slot]
  have hi : prefixJetIndex w (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1) =
      (⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩ : JetIndex2 (1 + r)) := by
    simp [prefixJetIndex, Fin.append_right_eq_snoc]
  rw [hi]
  congr 1
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N a.1 (1 + r) c ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩).trans
    (coupledPlainSynthesis_jet_ae N a.1 (0 + (r + 1)) c
      ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩).symm

/-- The empty derivative word acts as the identity on the finite coefficients. -/
theorem plainDerivativeCoefficients_zero (N : ℕ)
    (w : DerivativeWord2 0) (c : CoupledPlainCoefficients (h := h) N) :
    plainDerivativeCoefficients N 0 w c = c := by
  funext a
  rw [plainDerivativeCoefficients_apply, plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
    ((derivativeTorusHk w (coupledPlainSynthesis N a.1 0 c)).val (valueIndex2 0)) = c a
  rw [derivativeTorusHk_value_slot]
  have hw : w = Fin.elim0 := Subsingleton.elim _ _
  subst w
  have hm := plainSynthesis_mass_coordinate N (fun _ => 0) c a
  change plainInitialCoefficients N (fun _ => 0) (fun i => coupledPlainSynthesis N i 0 c) a = c a at hm
  rw [plainInitialCoefficients_component] at hm
  exact hm

/-- A single derivative commutes through every finite ordered derivative map. -/
theorem plainDerivativeCoefficients_direction_word (N : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (k : Fin 2) (c : CoupledPlainCoefficients (h := h) N) :
    plainDerivativeCoefficients N 0 w
      (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) c) =
      plainDerivativeCoefficients N 0 (Fin.snoc w k) c := by
  rw [plainDerivativeCoefficients_order_independent N 0 (0 + r) (fun _ : Fin 1 => k) c]
  funext a
  rw [plainDerivativeCoefficients_apply N 0 (Fin.snoc w k) c,
    plainDerivativeCoefficients_apply N 0 w
      (plainDerivativeCoefficients N (0 + r) (fun _ : Fin 1 => k) c),
    plainInitialCoefficients_component, plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
    ((derivativeTorusHk w
      (coupledPlainSynthesis N a.1 (0 + r) (plainDerivativeCoefficients N (0 + r) (fun _ : Fin 1 => k) c))).val
        (valueIndex2 0)) =
    inner ℝ (plainModeCellLp N a a.1 0 Fin.elim0)
      ((derivativeTorusHk (Fin.snoc w k)
        (coupledPlainSynthesis N a.1 (0 + (r + 1)) c)).val (valueIndex2 0))
  rw [derivativeTorusHk_value_slot, plainDerivativeCoefficients_synthesis,
    derivativeTorusHk_apply, derivativeTorusHk_value_slot]
  have hi : prefixJetIndex (fun _ : Fin 1 => k) (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (0 + r)) =
      (⟨⟨r + 1, by omega⟩, Fin.cons k w⟩ : JetIndex2 ((0 + r) + 1)) := by
    unfold prefixJetIndex
    apply Sigma.ext
    · apply Fin.ext
      change 1 + r = r + 1
      omega
    · change HEq (Fin.append (fun _ : Fin 1 => k) w) (Fin.cons k w : DerivativeWord2 (r + 1))
      rw [Fin.append_left_eq_cons]
      apply (Fin.heq_fun_iff (by omega)).mpr
      intro t
      change (Fin.cons k w : DerivativeWord2 (r + 1)) (Fin.cast _ t) =
        (Fin.cons k w : DerivativeWord2 (r + 1)) ⟨t.val, _⟩
      congr 1
  rw [hi]
  congr 1
  apply Lp.ext
  have hraw : coupledPlainRawJet N c a.1 (r + 1) (Fin.cons k w) =
      coupledPlainRawJet N c a.1 (r + 1) (Fin.snoc w k) :=
    funext (coupledPlainRawJet_cons_eq_snoc N c a.1 r w k)
  exact (coupledPlainSynthesis_jet_ae N a.1 ((0 + r) + 1) c ⟨⟨r + 1, by omega⟩, Fin.cons k w⟩).trans
    ((Filter.EventuallyEq.of_eq hraw).trans
      (coupledPlainSynthesis_jet_ae N a.1 (0 + (r + 1)) c
        ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩).symm)

/-- Every ordered derivative has its exact parity adjoint in the scalar finite mass pairing. -/
theorem plainDerivativeCoefficients_word_adjoint (N : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (c d : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainDerivativeCoefficients N 0 w c a * d a) =
      (-1 : ℝ) ^ r * ∑ a, c a * plainDerivativeCoefficients N 0 w d a := by
  induction r generalizing d with
  | zero => simp only [plainDerivativeCoefficients_zero, pow_zero, one_mul]
  | succ r ih =>
    rw [← Fin.snoc_init_self w, ← plainDerivativeCoefficients_snoc,
      plainDerivativeCoefficients_direction_skew, ih,
      plainDerivativeCoefficients_direction_word]
    rw [pow_succ]
    ring

/-- A derivative coefficient's value is the chosen jet of the original finite field at any order. -/
theorem plainDerivativeCoefficients_value_eq_jet {K r : ℕ} (hr : r ≤ K)
    (N : ℕ) (w : DerivativeWord2 r) (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    (coupledPlainSynthesis N i 0 (plainDerivativeCoefficients N 0 w c)).val (valueIndex2 0) =
      (coupledPlainSynthesis N i K c).val ⟨⟨r, by omega⟩, w⟩ := by
  apply Lp.ext
  exact (plainDerivativeCoefficients_value_ae N 0 w c i).trans
    (coupledPlainSynthesis_jet_ae N i K c ⟨⟨r, by omega⟩, w⟩).symm

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual transport term bundled in the periodic weak Sobolev carrier. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Spatial periodicity passes from the velocity to its fiber contraction. -/
theorem driftFiberCoefficient_periodic (v : Vec 2 → Vec 2)
    (hp : AVenhance.IsZ2Periodic v) (i : ι) :
    AVenhance.IsZ2Periodic (driftFiberCoefficient (E := h i) v) := by
  intro n x
  unfold driftFiberCoefficient driftCoefficient
  rw [hp n x]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Each actual transport derivative is cell L², using the finite smooth mask expansion. -/
theorem plainDrift_product_memLp (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (a : JetIndex2 K) :
    MemLp (multiplicationRawJet (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K) a)
      2 (volume.restrict AVenhance.unitCube) := by
  unfold multiplicationRawJet
  apply memLp_finsetSum
  intro m _
  have heq := funext (plainDrift_multiplicationTerm_eq (Nat.le_of_lt_succ a.1.isLt) N c i v hv m a.2)
  rw [heq]
  exact driftMaskTerm_memLp (Nat.le_of_lt_succ a.1.isLt) v hv
    (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2)
    (fun z => (coupledPlainRawJet_contDiff N c i z.1.val z.2).continuous) m a.2

/-- The literal transport term, with its genuine derivative mask jet. -/
def coupledPlainDriftHk (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v) : TorusHk K (h i) :=
  TorusHkFunction.toHk
    { jet := multiplicationRawJet (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K)
      hasPeriodicWeakJet := ⟨multiplicationRawJet_isZ2Periodic
        ((driftFiberCoefficient_contDiff v hv).of_le (by simp)) (driftFiberCoefficient_periodic v hp i)
        (fun a => coupledPlainGradientJet_periodic N c i a.1.val a.2),
        plainDrift_product_memLp N c i K v hv, plainDrift_product_hasWeakJet N c i K v hv⟩ }

/-- Every derivative of the bundled transport is its literal mask expansion. -/
theorem coupledPlainDriftHk_jet_ae (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v) (a : JetIndex2 K) :
    (coupledPlainDriftHk N c i K v hv hp).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ m : PositionMask a.1.val,
        driftMaskTerm (Nat.le_of_lt_succ a.1.isLt) v
          (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m a.2 x := by
  have heq : multiplicationRawJet (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K) a =
      fun x => ∑ m : PositionMask a.1.val,
        driftMaskTerm (Nat.le_of_lt_succ a.1.isLt) v
          (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m a.2 x := by
    funext x
    apply Finset.sum_congr rfl
    intro m _
    exact plainDrift_multiplicationTerm_eq _ N c i v hv m a.2 x
  exact (torusJetToL2_ae _ _ a).trans (Filter.EventuallyEq.of_eq heq)

/-- The order-zero class is precisely velocity contracted with the synthesized gradient. -/
theorem coupledPlainDriftHk_value_ae (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v) :
    (coupledPlainDriftHk N c i K v hv hp).val (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
      ∑ k : Fin 2, v x k • coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x := by
  have heq := funext (plainDrift_product_value N c i K v)
  exact (torusJetToL2_ae _ _ (valueIndex2 K)).trans (Filter.EventuallyEq.of_eq heq)

/-- The synthesized graph is exactly the promoted explicit raw Fourier jet. -/
theorem coupledPlainSynthesis_val_eq_rawJetToL2 (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) :
    (coupledPlainSynthesis N i K c).val = jetToL2
      (fun a : JetIndex2 K => coupledPlainRawJet N c i a.1.val a.2)
      (fun a => coupledPlainRawJet_memLp N c i a.1.val a.2) := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N i K c a).trans
    (coupledPlainRawJet_memLp N c i a.1.val a.2).coeFn_toLp.symm

/-- The genuine drift-carrier jet pairing is the sum of its literal spatial mask pairings. -/
theorem coupledPlainDriftHk_jet_pairing (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v) (a : JetIndex2 K) :
    inner ℝ ((coupledPlainDriftHk N c i K v hv hp).val a)
      ((coupledPlainSynthesis N i K c).val a) =
      ∑ m : PositionMask a.1.val, ∫ x in AVenhance.unitCube,
        inner ℝ (driftMaskTerm (Nat.le_of_lt_succ a.1.isLt) v
          (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m a.2 x)
          (coupledPlainRawJet N c i a.1.val a.2 x) := by
  rw [L2.inner_def]
  have heq : (∫ x in AVenhance.unitCube, inner ℝ ((coupledPlainDriftHk N c i K v hv hp).val a x)
      ((coupledPlainSynthesis N i K c).val a x)) =
      ∫ x in AVenhance.unitCube, ∑ m : PositionMask a.1.val,
        inner ℝ (driftMaskTerm (Nat.le_of_lt_succ a.1.isLt) v
          (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m a.2 x)
          (coupledPlainRawJet N c i a.1.val a.2 x) := by
    apply integral_congr_ae
    filter_upwards [coupledPlainDriftHk_jet_ae N c i K v hv hp a,
      coupledPlainSynthesis_jet_ae N i K c a] with x hx hy
    rw [hx, hy, sum_inner]
  rw [heq]
  apply integral_finsetSum
  intro m _
  have hm := driftMaskTerm_memLp (Nat.le_of_lt_succ a.1.isLt) v hv
    (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2)
    (fun z => (coupledPlainRawJet_contDiff N c i z.1.val z.2).continuous) m a.2
  have hD := coupledPlainRawJet_memLp N c i a.1.val a.2
  apply (L2.integrable_inner (𝕜 := ℝ) (hm.toLp _) (hD.toLp _)).congr
  filter_upwards [hm.coeFn_toLp, hD.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- The full actual transport carrier absorbs in absolute value into ν/4 of the factorial gradient
energy. -/
theorem coupledPlainDriftHk_energy_abs_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    |∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
      inner ℝ ((coupledPlainDriftHk N c i K v hv hp).val ⟨j, w⟩)
        ((coupledPlainSynthesis N i K c).val ⟨j, w⟩)| ≤
      (ν / 4) * gradFactorialNormSq ρ (coupledPlainSynthesis N i (K + 1) c).val := by
  simp_rw [coupledPlainDriftHk_jet_pairing]
  have hs (j : Fin (K + 1)) : (∑ w : DerivativeWord2 j.val, ∑ m : PositionMask j.val,
      ∫ x in AVenhance.unitCube, inner ℝ
        (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v
          (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m w x)
        (coupledPlainRawJet N c i j.val w x)) =
      ∑ m : PositionMask j.val, ∑ w : DerivativeWord2 j.val,
        ∫ x in AVenhance.unitCube, inner ℝ
          (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v
            (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m w x)
          (coupledPlainRawJet N c i j.val w x) := Finset.sum_comm
  simp_rw [hs]
  rw [coupledPlainSynthesis_val_eq_rawJetToL2]
  exact plainDrift_full_energy_abs_le hK N c i ρ a B lam ν hρ ha hB hlam hν hsmall hstrain
    v hv hp hd hjets

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The finite ODE gives the literal spatial equation against every projected H¹ test. -/
theorem plainODE_projected_test_spatial_equation (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, Continuous (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b y)
    (hint : IntervalIntegrable (linearRhs
      (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s)) y) volume a b)
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (y t)))
      (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∫ s in a..t, ∑ r, plainInitialCoefficients N (fun _ => 1) φ r *
      ((∫ x in AVenhance.unitCube, plainSpatialRowIntegrand N D ν K (v s)
        (fun i i' d => A i i' d s) r (y s) x) +
        plainFourierForcing N (fun i => torusHkValueCLM (F i s))
          (fun i => torusHkValueCLM (g i s)) r) := by
  have hid := plainODE_tested_integral_equation N K (fun _ => 1) hab
    (fun s => plainFourierMatrix N D ν K v A s)
    (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s)) y f hy hint
    (plainInitialCoefficients N (fun _ => 1) φ) t ht
  simp_rw [plainInitialCoefficients_synthesis N (fun _ => 1) φ] at hid
  rw [hid]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  have hs' : s ∈ Icc a b := by
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  apply Finset.sum_congr rfl
  intro r _
  rw [plainFourierMatrix_action_eq_spatial_integral N D ν K v A s (hv s hs') (hA s hs'),
    plainSourceCoefficients_eq_fourierForcing]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Directional derivatives of synthesized coefficient vectors at arbitrary
ordered jets. The finite coefficient commutation proof is reused unchanged. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainDerivativeCoefficients_direction_jet {K r : ℕ} (hr : r ≤ K)
    (N : ℕ) (i : ι) (w : DerivativeWord2 r) (k : Fin 2)
    (c : CoupledPlainCoefficients (h := h) N) :
    (coupledPlainSynthesis N i K (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) c)).val
      ⟨⟨r, by omega⟩, w⟩ =
      (coupledPlainSynthesis N i (K + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩ := by
  rw [← plainDerivativeCoefficients_value_eq_jet hr N w,
    plainDerivativeCoefficients_direction_word,
    plainDerivativeCoefficients_value_eq_jet (K := K + 1) (by omega)]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify an actual lower-order trace with the truncation of the recovered
higher-order graph using the countable concrete Fourier observables. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Truncating the Sobolev graph preserves its value readout. -/
theorem torusHkValue_truncate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) :
    torusHkValueCLM (truncateTorusHk hKL f) = torusHkValueCLM f := by
  rfl

/-- Concrete Fourier observable identification recovers all lower Sobolev jets almost everywhere. -/
theorem plainTrace_eq_highGraph_ae (K : ι → ℕ) (a b : ℝ)
    (U : CoupledHighTime (h := h) K a b) (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hgraph : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (coupledHighGraphReadout K i (U t)).val = U t i)
    (hpair : ∀ N, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r : CoupledFourierModeIndex (h := h) N,
      inner ℝ (torusHkValueCLM (u r.1 t)) (torusHkValueCLM (coupledModeHk N r r.1 1)) =
      inner ℝ (U t r.1 (valueIndex2 (K r.1 + 1)))
        (torusHkValueCLM (coupledModeHk N r r.1 1))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t)) := by
  apply plainTrace_eq_ae_of_mode_pairings (volume.restrict (Set.Icc a b)) K u
    (fun i t => truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t)))
  intro N
  filter_upwards [hpair N, hgraph] with t ht hg
  intro r
  rw [torusHkValue_truncate]
  change _ = inner ℝ ((coupledHighGraphReadout K r.1 (U t)).val (valueIndex2 (K r.1 + 1))) _
  rw [hg r.1]
  exact ht r

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Exact finite coefficient tests for a single component's differentiated energy. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The coefficient test for the square of one ordered derivative in one component. -/
def plainEnergyTest (N : ℕ) (i : ι) {r : ℕ} (w : DerivativeWord2 r) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] CoupledPlainCoefficients (h := h) N :=
  (-1 : ℝ) ^ r • (plainDerivativeCoefficients N 0 w).comp
    ((plainDerivativeCoefficients N 0 w).comp (plainComponentCoefficients N i))

/-- Testing the coefficient equation with this finite vector is exactly the jet energy pairing. -/
theorem plainEnergyTest_pairing {K r : ℕ} (hr : r ≤ K) (N : ℕ) (i : ι)
    (w : DerivativeWord2 r) (c q : CoupledPlainCoefficients (h := h) N) :
    (∑ a, q a * plainEnergyTest N i w c a) =
      inner ℝ ((coupledPlainSynthesis N i K q).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i K c).val ⟨⟨r, by omega⟩, w⟩) := by
  have ha := plainDerivativeCoefficients_word_adjoint N w q
    (plainDerivativeCoefficients N 0 w (plainComponentCoefficients N i c))
  rw [← plainSynthesis_mass_pairing N (fun _ => 0)] at ha
  have hs : (∑ j, inner ℝ
      ((coupledPlainSynthesis N j 0 (plainDerivativeCoefficients N 0 w q)).val (valueIndex2 0))
      ((coupledPlainSynthesis N j 0
        (plainDerivativeCoefficients N 0 w (plainComponentCoefficients N i c))).val (valueIndex2 0))) =
      inner ℝ ((coupledPlainSynthesis N i K q).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i K c).val ⟨⟨r, by omega⟩, w⟩) := by
    rw [Finset.sum_eq_single i]
    · rw [plainComponentDerivative_synthesis_self,
        plainDerivativeCoefficients_value_eq_jet hr, plainDerivativeCoefficients_value_eq_jet hr]
    · intro j _ hji
      rw [plainComponentDerivative_synthesis_other N i j hji]
      change inner ℝ _ (0 : ComponentL2 (volume.restrict AVenhance.unitCube) (h j)) = 0
      exact inner_zero_right _
    · simp
  have hnew := hs.symm.trans ha
  clear ha
  have ha := hnew
  rw [ha]
  simp only [plainEnergyTest, smul_apply, ContinuousLinearMap.comp_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The energy test vanishes outside its chosen component. -/
theorem plainEnergyTest_synthesis_other (N : ℕ) (i j : ι) (hji : j ≠ i)
    {r : ℕ} (w : DerivativeWord2 r) (c : CoupledPlainCoefficients (h := h) N) (L : ℕ) :
    coupledPlainSynthesis N j L (plainEnergyTest N i w c) = 0 := by
  simp only [plainEnergyTest, smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  rw [plainDerivativeCoefficients_order_independent N 0 L,
    plainDerivativeCoefficients_synthesis,
    plainDerivativeCoefficients_order_independent N 0 (L + r),
    plainComponentDerivative_synthesis_other N i j hji, map_zero, smul_zero]

/-- On its own component the energy test is the parity-weighted double derivative test. -/
theorem plainEnergyTest_synthesis_self (N : ℕ) (i : ι)
    {r : ℕ} (w : DerivativeWord2 r) (c : CoupledPlainCoefficients (h := h) N) (L : ℕ) :
    coupledPlainSynthesis N i L (plainEnergyTest N i w c) =
      (-1 : ℝ) ^ r • coupledPlainSynthesis N i L
        (plainDerivativeCoefficients N 0 w (plainDerivativeCoefficients N 0 w c)) := by
  simp only [plainEnergyTest, smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  rw [plainDerivativeCoefficients_order_independent N 0 L,
    plainDerivativeCoefficients_synthesis,
    plainDerivativeCoefficients_order_independent N 0 (L + r),
    plainComponentDerivative_synthesis_self]
  rw [← plainDerivativeCoefficients_synthesis,
    plainDerivativeCoefficients_order_independent N (L + r) 0,
    plainDerivativeCoefficients_order_independent N L 0]
end

/-! Periodic weak integration by parts against actual finite Fourier tests.
Projection is moved onto the weak factor by self-adjointness; its smooth lift then
allows the classical periodic argument, without strengthening the weak carrier. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Move one weak partial onto a finite synthesized test by exact periodic integration by parts. -/
theorem plainWeakJet_test_partial_ibp {K : ℕ} (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (f : TorusHk K (h i))
    (j : Fin K) (w : DerivativeWord2 j.val) (k : Fin 2) :
    inner ℝ (f.val (nextIndex2 j w k))
      ((coupledPlainSynthesis N i 1 c).val (valueIndex2 1)) =
      -inner ℝ (f.val (lowerIndex2 j w))
        ((coupledPlainSynthesis N i 1 c).val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) := by
  have hf := plainSynthesis_galerkin_fixed N (fun _ => 1) c i
  have h0 := galerkinProj_jet_fixed N _ hf (valueIndex2 1)
  have h1 := galerkinProj_jet_fixed N _ hf
    (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1)
  rw [← galerkinProj_jet_pairing_of_fixed N f (nextIndex2 j w k) _ h0,
    ← galerkinProj_jet_pairing_of_fixed N f (lowerIndex2 j w) _ h1,
    L2.inner_def, L2.inner_def]
  have hibp := Variational.periodic_hilbert_partial_ibp
    (smoothFourierJet (L := K) N f (lowerIndex2 j w))
    (coupledPlainRawJet N c i 0 Fin.elim0)
    ((smoothFourierJet_contDiff N f _).of_le (by simp))
    ((coupledPlainRawJet_contDiff N c i 0 Fin.elim0).of_le (by simp))
    (smoothFourierJet_periodic N f _) (coupledPlainRawJet_periodic N c i 0 Fin.elim0) k
  simp only [smoothFourierJet_fderiv, coupledPlainRawJet_fderiv] at hibp
  calc
    _ = ∫ x in AVenhance.unitCube, inner ℝ
        (smoothFourierJet N f (nextIndex2 j w k) x) (coupledPlainRawJet N c i 0 Fin.elim0 x) := by
      apply integral_congr_ae
      filter_upwards [galerkinProj_jet_ae_smooth N f (nextIndex2 j w k),
        coupledPlainSynthesis_jet_ae N i 1 c (valueIndex2 1)] with x hx ht
      rw [hx, ht]
      rfl
    _ = -∫ x in AVenhance.unitCube, inner ℝ
        (smoothFourierJet N f (lowerIndex2 j w) x)
        (coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x) := hibp
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [galerkinProj_jet_ae_smooth N f (lowerIndex2 j w),
        coupledPlainSynthesis_jet_ae N i 1 c ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩] with x hx ht
      rw [hx, ht]

/-- One weak partial can be moved onto the explicit finite coefficient derivative. -/
theorem plainWeakJet_test_partial_ibp_coeff {K : ℕ} (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (f : TorusHk K (h i))
    (j : Fin K) (w : DerivativeWord2 j.val) (k : Fin 2) :
    inner ℝ (f.val (nextIndex2 j w k))
      ((coupledPlainSynthesis N i 0 c).val (valueIndex2 0)) =
      -inner ℝ (f.val (lowerIndex2 j w))
        ((coupledPlainSynthesis N i 0
          (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) c)).val (valueIndex2 0)) := by
  have h0 : (coupledPlainSynthesis N i 1 c).val (valueIndex2 1) =
      (coupledPlainSynthesis N i 0 c).val (valueIndex2 0) := by
    apply Lp.ext
    exact (coupledPlainSynthesis_jet_ae N i 1 c (valueIndex2 1)).trans
      (coupledPlainSynthesis_jet_ae N i 0 c (valueIndex2 0)).symm
  have h1 : (coupledPlainSynthesis N i 1 c).val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ =
      (coupledPlainSynthesis N i 0
        (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) c)).val (valueIndex2 0) := by
    apply Lp.ext
    exact (coupledPlainSynthesis_jet_ae N i 1 c ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩).trans
      (plainDerivativeCoefficients_value_ae N 0 (fun _ : Fin 1 => k) c i).symm
  simpa only [h0, h1] using plainWeakJet_test_partial_ibp N c i f j w k

/-- Move an entire weak derivative word onto the finite test, with the exact parity sign. -/
theorem plainWeakJet_test_word_ibp {K r : ℕ} (hr : r ≤ K) (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (f : TorusHk K (h i))
    (w : DerivativeWord2 r) :
    inner ℝ (f.val ⟨⟨r, by omega⟩, w⟩)
      ((coupledPlainSynthesis N i 0 c).val (valueIndex2 0)) =
      (-1 : ℝ) ^ r * inner ℝ (f.val (valueIndex2 K))
        ((coupledPlainSynthesis N i 0 (plainDerivativeCoefficients N 0 w c)).val (valueIndex2 0)) := by
  induction r generalizing c with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    simp only [plainDerivativeCoefficients_zero, pow_zero, one_mul]
    rfl
  | succ r ih =>
    have hpartial := plainWeakJet_test_partial_ibp_coeff N c i f
      ⟨r, by omega⟩ (Fin.init w) (w (Fin.last r))
    have hi : nextIndex2 (⟨r, by omega⟩ : Fin K) (Fin.init w) (w (Fin.last r)) =
        (⟨⟨r + 1, by omega⟩, w⟩ : JetIndex2 K) := by
      simp [nextIndex2, nextIndex, Fin.snoc_init_self]
    rw [hi] at hpartial
    rw [hpartial]
    have hrec := ih (by omega)
      (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => w (Fin.last r)) c) (Fin.init w)
    change inner ℝ (f.val (lowerIndex2 (⟨r, by omega⟩ : Fin K) (Fin.init w))) _ = _ at hrec
    rw [hrec, plainDerivativeCoefficients_direction_word, Fin.snoc_init_self, pow_succ]
    ring
end

/-! The derivative of a smooth cutoff of a weak flux pairs with any finite
Fourier test through exact periodic integration by parts. Cutoffs may differ. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [DecidableEq ι] in
/-- A smooth lift retains every jet below the input Sobolev order. -/
theorem smoothFourierLift_jet_projection (N : ℕ) (i : ι) {K L : ℕ} (hKL : K ≤ L)
    (f : TorusHk K (h i)) (j : JetIndex2 K) :
    (smoothFourierLift (K := K) (L := L) N f).val (truncateJetIndex hKL j) =
      (galerkinProj N f).val j := by
  exact congrArg (fun v : TorusHk K (h i) => v.val j) (smoothFourierLift_truncate_eq hKL N f)

/-- Different spectral cutoffs can be used on the weak flux and finite test. -/
theorem plainSmoothFlux_jet_partial_ibp {K r : ℕ} (hr : r ≤ K) (N M : ℕ) (i : ι)
    (w : DerivativeWord2 r) (k : Fin 2) (f : TorusHk K (h i))
    (c : CoupledPlainCoefficients (h := h) M) :
    inner ℝ ((smoothFourierLift (K := K) (L := K + 1) N f).val
      ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩)
      ((coupledPlainSynthesis M i K c).val ⟨⟨r, by omega⟩, w⟩) =
      -inner ℝ ((galerkinProj N f).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis M i (K + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  have he := plainWeakJet_test_partial_ibp M (plainDerivativeCoefficients M 0 w c) i
    (smoothFourierLift (K := K) (L := K + 1) N f) (⟨r, by omega⟩ : Fin (K + 1)) w k
  change inner ℝ ((smoothFourierLift (K := K) (L := K + 1) N f).val
      ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩)
      ((coupledPlainSynthesis M i 1 (plainDerivativeCoefficients M 0 w c)).val (valueIndex2 1)) =
    -inner ℝ ((smoothFourierLift (K := K) (L := K + 1) N f).val ⟨⟨r, by omega⟩, w⟩)
      ((coupledPlainSynthesis M i 1 (plainDerivativeCoefficients M 0 w c)).val
        ⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => k⟩) at he
  have hlo := smoothFourierLift_jet_projection N i (Nat.le_succ K) f
    (⟨⟨r, by omega⟩, w⟩ : JetIndex2 K)
  change (smoothFourierLift (K := K) (L := K + 1) N f).val ⟨⟨r, by omega⟩, w⟩ = _ at hlo
  rw [hlo, coupledPlainSynthesis_value_order_independent M i 1 0,
    plainDerivativeCoefficients_value_eq_jet hr] at he
  have hgrad : (coupledPlainSynthesis M i 1 (plainDerivativeCoefficients M 0 w c)).val
      ⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => k⟩ =
      (coupledPlainSynthesis M i (K + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩ := by
    rw [← plainDerivativeCoefficients_value_eq_jet (K := 1) (by omega) M (fun _ : Fin 1 => k),
      plainDerivativeCoefficients_snoc, plainDerivativeCoefficients_value_eq_jet (K := K + 1) (by omega)]
  rw [hgrad] at he
  exact he
end

end AVRegularity.CoupledEnergy.Galerkin
end
