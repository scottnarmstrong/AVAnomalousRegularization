-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import Mathlib.Algebra.Order.Star.Real

section
section
/-! The finite Sobolev readout realizes exactly the selected raw flux and preserves L² time
integrability. No coefficient estimate is used in this algebraic passage.

Special cases: an empty sum is zero, a singleton is its scalar root transport, and the zero
flux stays zero. Order zero and identity metric need no derivatives or division by norms. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

private theorem zero_carrier_jet_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) :
    (0 : TorusHk k E).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube]
      (fun _ => 0) := by
  filter_upwards [KernelEnergy.torusHk_toFunction_jet_ae (0 : TorusHk k E) (valueIndex2 k),
    (Lp.coeFn_zero (E := E) (p := 2) (μ := volume.restrict unitCube))] with x hx hz
  exact hx.trans hz

private theorem root_cast_value_ae {r r' k : ℕ} (heq : r = r')
    (W : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr r)))
    (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => hr r))
    (hf : W.toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube] f) :
    (cast (congrArg (fun n => TorusHk k (PiLp 2 (fun _ : Fin 2 => hr n))) heq) W).toFunction.jet
      (valueIndex2 k) =ᵐ[volume.restrict unitCube]
        (fun x => cast (congrArg (fun n => PiLp 2 (fun _ : Fin 2 => hr n)) heq) (f x)) := by
  subst r'
  exact hf

/-- A realized selected row is the zero Sobolev carrier off its selected layer. -/
theorem realized_row_zero (F : Frame D hr Dm bw j₀) (grade : Bool) (OF : F.RowFlux)
    (hOF : F.RealizesRows grade OF) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf)
    (v : CompIn F.G'.comps) (hv : ¬F.select grade v.1) : OF v t = 0 := by
  apply KernelEnergy.torusCarrier_eq_of_value_ae
  have he : (OF v t).toFunction.jet (valueIndex2 F.k) =ᵐ[volume.restrict unitCube]
      (fun _ => 0) := by simpa only [hv, ite_false] using hOF v t ht
  exact he.trans (zero_carrier_jet_ae F.k).symm

/-- The literal finite Sobolev sum has the raw selected readout as its value representative. -/
theorem realized_rows_readout (F : Frame D hr Dm bw j₀) (grade : Bool) (OF : F.RowFlux)
    (hOF : F.RealizesRows grade OF) :
    F.RealizesReadout grade
      (fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) F.m (D.eps (F.m - 1)) F.η F.k (fun c => OF c t) v) := by
  classical
  intro v t ht
  unfold succReadout readoutFlux
  apply KernelEnergy.torusJet_sum_ae_of_eq
  intro c
  by_cases hp : compParent F.m c.1 = v.1
  · simp only [hp, ↓reduceDIte]
    let hroot := (compParent_root F.m c.1).symm.trans (congrArg Comp.root hp)
    have hc := root_cast_value_ae hroot (OF c t)
      (fun x => if F.select grade c.1 then
        omittedFlux F.G' F.k (IsRetained F.m F.H F.J) F.yom c t x else 0) (hOF c t ht)
    have hs := (KernelEnergy.torusJet_smul_ae
      ((D.eps (F.m - 1)) ^ (F.η * (compWord F.m c.1).length))
      (cast (congrArg (fun n => TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr n))) hroot) (OF c t))
      (valueIndex2 F.k)).trans (hc.mono fun _ h => congrArg _ h)
    by_cases hsel : F.select grade c.1
    · simpa only [hsel, and_self, ↓reduceDIte, ite_true] using hs
    · have hz : cast (congrArg (fun n => PiLp 2 (fun _ : Fin 2 => hr n)) hroot)
          (0 : PiLp 2 (fun _ : Fin 2 => hr c.1.root)) = 0 := by
        have hzcast {r r' : ℕ} (h : r = r') :
            cast (congrArg (fun n => PiLp 2 (fun _ : Fin 2 => hr n)) h)
              (0 : PiLp 2 (fun _ : Fin 2 => hr r)) = 0 := by
          subst r'
          rfl
        exact hzcast hroot
      simpa only [hsel, and_false, ↓reduceDIte, ite_false, hz, smul_zero] using hs
  · simp only [hp, false_and, ↓reduceDIte]
    exact zero_carrier_jet_ae F.k

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! Actual cascade histories have distinct, increasing birth scales. This is the geometric
input to the grade marker gain, independent of the coefficients and their time regularity.

Special cases: the empty history, an empty family and seed components give the empty ordered
list; appending the first birth preserves strict order, including passage at level one. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Frontier

private theorem successor_births_pairwise {m : ℕ} (hm : 1 ≤ m) {A : Finset WordLetter}
    {J : ℕ} {S : Finset Comp}
    (hold : ∀ c ∈ S, ∀ e ∈ c.births, m ≤ e.scale)
    (hpair : ∀ c ∈ S, c.births.Pairwise (fun e f => e.scale < f.scale))
    {c : Comp} (hc : c ∈ succExtComps m A J S) :
    c.births.Pairwise (fun e f => e.scale < f.scale) := by
  rcases InitialValue.mem_succExtComps hc with hc | ⟨v, hv, t, rfl⟩
  · exact hpair c hc
  · by_cases ht : t = []
    · simpa only [succComp, ht, ↓reduceDIte] using hpair v hv
    · simp only [succComp, ht, ↓reduceDIte]
      apply List.pairwise_cons.mpr
      refine ⟨?_, hpair v hv⟩
      intro e he
      have := hold v hv e he
      change m - 1 < e.scale
      omega

/-- Strict birth-scale order is preserved by every actual cascade passage. -/
theorem cascade_births_pairwise {D : OCData} {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
    {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
    {seed G : GenStage D hr Dm bw j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) :
    ∀ c ∈ G.comps, c.births.Pairwise (fun e f => e.scale < f.scale) := by
  induction hc with
  | seed =>
    intro c hc
    rw [hseed ⟨c, hc⟩]
    exact List.Pairwise.nil
  | @step G G' hc hactual ih =>
    intro c hc'
    have hcG' := (Finset.mem_filter.mp hc').1
    rw [hactual.2.2.1] at hcG'
    exact successor_births_pairwise hactual.1
      (fun v hv => (InitialValue.cascade_invariant hseed hc v hv).1) ih hcG'

/-- The extended successor, before retention, has the same strict birth-scale order. -/
theorem extended_births_pairwise {D : OCData} {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
    {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
    {seed G G' : GenStage D hr Dm bw j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) (ha : IsActualSuccessor D P Mn G G') :
    ∀ c ∈ G'.comps, c.births.Pairwise (fun e f => e.scale < f.scale) := by
  intro c hc'
  rw [ha.2.2.1] at hc'
  exact successor_births_pairwise ha.1
    (fun v hv => (InitialValue.cascade_invariant hseed hc v hv).1)
    (cascade_births_pairwise hseed hc) hc'

/-- In an actual history the set of birth scales loses no multiplicity. -/
theorem ordered_birth_scales_nodup {c : Comp}
    (hc : c.births.Pairwise (fun e f => e.scale < f.scale)) :
    (c.births.map BirthEvent.scale).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact hc.imp (fun h => Nat.ne_of_lt h)

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The inverse marker of a grade-g component is bounded by the g-term geometric
power at the youngest possible scale. Rounded scales satisfy the required q-bar separation
beyond one uniform floor; no bound depends on the component or the number of stages.

Special cases: grade zero gives one, one birth gives its own scale factor, and empty families
require no estimate. This uses neither the metric nor a nonzero initial datum. -/
@[expose] public noncomputable section
open Filter Topology
namespace AVRegularity.Construction.Preservation.Frontier

/-- Rounded wavelengths eventually separate by the intermediate exponent `(1+q)/2`. -/
theorem marker_scale_separation_threshold {q : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hq16 : q < 17 / 16) (hΛ : 128 ≤ Λ) :
    ∃ n : ℕ, ∀ k, n ≤ k →
      ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k ^ ((1 + q) / 2) := by
  have hgap : 0 < (q - 1) / 2 := div_pos (sub_pos.mpr hq) (by norm_num)
  have ht := (EntryScales.epsilon_rpow_tendsto_zero hq hΛ hgap).const_mul 2
  rw [mul_zero] at ht
  obtain ⟨n, hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨n, ?_⟩
  intro k hk
  have he := (Scales.epsilon_basic (m := k) hq hΛ).1
  have hsplit : ocEpsilon q Λ k ^ q =
      ocEpsilon q Λ k ^ ((q - 1) / 2) * ocEpsilon q Λ k ^ ((1 + q) / 2) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  calc
    _ ≤ 2 * ocEpsilon q Λ k ^ q := by
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        Scales.epsilon_q_step (m := k + 1) hq hq16 hΛ (by omega)
    _ = (2 * ocEpsilon q Λ k ^ ((q - 1) / 2)) *
        ocEpsilon q Λ k ^ ((1 + q) / 2) := by rw [hsplit, mul_assoc]
    _ ≤ 1 * ocEpsilon q Λ k ^ ((1 + q) / 2) :=
      mul_le_mul_of_nonneg_right (hn k hk).le (Real.rpow_nonneg he.le _)
    _ = _ := one_mul _

private theorem geometric_sum_cons (r : ℝ) (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), r ^ l) = 1 + r * ∑ l ∈ Finset.range n, r ^ l := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ', ← Finset.mul_sum]
  ring

private theorem birth_scale_product_bound {q : ℝ} {Λ n : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) {ι : ℝ} (hι : 0 ≤ ι)
    (hstep : ∀ k, n ≤ k → ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k ^ ((1 + q) / 2))
    (l : List BirthEvent) (hp : l.Pairwise (fun e f => e.scale < f.scale)) :
    ∀ k, n ≤ k → (∀ e ∈ l, k ≤ e.scale) →
      (l.map (fun e => ocEpsilon q Λ e.scale ^ ι)).prod ≤
        ocEpsilon q Λ k ^ (ι * ∑ i ∈ Finset.range l.length, ((1 + q) / 2) ^ i) := by
  induction l with
  | nil =>
    intro k _ _
    simp only [List.map_nil, List.prod_nil, List.length_nil, Finset.range_zero,
      Finset.sum_empty, mul_zero, Real.rpow_zero, le_refl]
  | cons e l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    intro k hk hall
    have ht := ih htail (k + 1) (by omega) (fun f hf => by
      have := hhead f hf
      have := hall e List.mem_cons_self
      omega)
    have hs : 0 ≤ ι * ∑ i ∈ Finset.range l.length, ((1 + q) / 2) ^ i :=
      mul_nonneg hι (Finset.sum_nonneg fun _ _ => pow_nonneg (by linarith only [hq]) _)
    have ha := Real.rpow_le_rpow
      (Scales.epsilon_basic (m := e.scale) hq hΛ).1.le
      (EntryScales.epsilon_antitone hq hΛ (hall e List.mem_cons_self)) hι
    have hb := Real.rpow_le_rpow (Scales.epsilon_basic (m := k + 1) hq hΛ).1.le
      (hstep k hk) hs
    rw [← Real.rpow_mul (Scales.epsilon_basic (m := k) hq hΛ).1.le] at hb
    calc
      _ = ocEpsilon q Λ e.scale ^ ι * (l.map (fun e => ocEpsilon q Λ e.scale ^ ι)).prod := rfl
      _ ≤ ocEpsilon q Λ k ^ ι *
          ocEpsilon q Λ k ^ (((1 + q) / 2) *
            (ι * ∑ i ∈ Finset.range l.length, ((1 + q) / 2) ^ i)) :=
        mul_le_mul ha (ht.trans hb) (List.prod_nonneg (fun x hx => by
          obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
          exact Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _))
          (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _)
      _ = _ := by
        rw [← Real.rpow_add (Scales.epsilon_basic (m := k) hq hΛ).1,
          List.length_cons, geometric_sum_cons]
        congr 1
        ring

/-- The marker contains one factor for every birth, since actual birth scales are distinct. -/
theorem inverse_marker_grade_bound {q : ℝ} {Λ n k : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (law : BirthLaw) (hι : 0 ≤ law.iota)
    (hstep : ∀ k, n ≤ k → ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k ^ ((1 + q) / 2))
    (hk : n ≤ k) (c : Comp) (hp : c.births.Pairwise (fun e f => e.scale < f.scale))
    (hall : ∀ e ∈ c.births, k ≤ e.scale) :
    (compMarker q Λ law c)⁻¹ ≤
      ocEpsilon q Λ k ^ (law.iota * ∑ i ∈ Finset.range (compGrade c), ((1 + q) / 2) ^ i) := by
  have he : (compMarker q Λ law c)⁻¹ =
      (c.births.map (fun e => ocEpsilon q Λ e.scale ^ law.iota)).prod := by
    unfold compMarker
    rw [← Finset.prod_inv_distrib]
    have hprod : (∏ b ∈ compBirthSet c, (ocEpsilon q Λ b ^ (-law.iota))⁻¹) =
        ∏ b ∈ compBirthSet c, ocEpsilon q Λ b ^ law.iota := by
      apply Finset.prod_congr rfl
      intro b _
      rw [Real.rpow_neg (Scales.epsilon_basic (m := b) hq hΛ).1.le, inv_inv]
    rw [hprod, compBirthSet, List.prod_toFinset _ (ordered_birth_scales_nodup hp), List.map_map]
    rfl
  rw [he]
  exact birth_scale_product_bound hq hΛ hι hstep c.births hp k hk hall

end AVRegularity.Construction.Preservation.Frontier
end
end
end

section
section
/-! A selected readout gains the inverse marker of its selected rows. The parent fibres
are disjoint, so its norm depends on the finite word menu, never on the number of roots.

Special cases: empty sums and zero input give zero; a singleton is a weighted scalar map.
The constant also covers an identity metric, order zero and the first word prefix. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
open FullLift RetainedEnergy
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

private theorem marker_normalized_entry {π σ d a : ℝ} (hσ : 0 ≤ σ) (hd : 0 ≤ d) :
    (Real.sqrt π)⁻¹ / (Real.sqrt (σ / d ^ 2))⁻¹ * a =
      ((Real.sqrt π)⁻¹ / (Real.sqrt σ)⁻¹ * a) * d⁻¹ := by
  rw [inverse_sqrt_effective_mass hσ hd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem row_multiplicity_square {B g : ℝ} (hB : 1 ≤ B) :
    B * g ^ 2 ≤ (B * g) ^ 2 := by
  have hBB : B ≤ B ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hB (zero_le_one.trans hB)
  calc
    _ ≤ B ^ 2 * g ^ 2 := mul_le_mul_of_nonneg_right hBB (sq_nonneg g)
    _ = _ := (mul_pow B g 2).symm

/-- The selected marked-to-ordinary readout estimate at a single time. -/
theorem selected_readout_mass_square {q η : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) (law : BirthLaw)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη : 0 ≤ η)
    {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    (hsub : S' ⊆ succExtComps m A J S) (sel : CompIn S' → Prop) [DecidablePred sel]
    (g : ℝ) (hg : 0 ≤ g)
    (hmarker : ∀ c : CompIn S', sel c → (compMarker q Λ law c.1)⁻¹ ≤ g)
    {K : ℕ} (ρ : ℝ) (X : ∀ c : CompIn S', TorusHk K (hr c.1.root))
    (hzero : ∀ c, ¬sel c → X c = 0) :
    massNormSq ρ (fun v : CompIn S => compMass q Λ law v.1)
      (fun v => (succReadout m (ocEpsilon q Λ (m - 1)) η K X v).val) ≤
      (((wordsUpTo A (J + 1)).card + 1 : ℝ) * g) ^ 2 *
        massNormSq ρ
          (fun c : CompIn S' => compMass q Λ law c.1 / compMarker q Λ law c.1 ^ 2)
          (fun c => (X c).val) := by
  classical
  let B : ℝ := (wordsUpTo A (J + 1)).card + 1
  have hB : 1 ≤ B := le_add_of_nonneg_left (Nat.cast_nonneg _)
  let π : CompIn S → ℝ := fun v => compMass q Λ law v.1
  let σ : CompIn S' → ℝ := fun c => compMass q Λ law c.1 / compMarker q Λ law c.1 ^ 2
  have hπ : ∀ v, 0 < π v := fun v => Buffer.birth_compMass_pos hq hΛ law v.1
  have hσ : ∀ c, 0 < σ c := fun c => div_pos (Buffer.birth_compMass_pos hq hΛ law c.1)
    (sq_pos_of_pos (Buffer.birth_compMarker_pos hq hΛ law c.1))
  have hrow (v : CompIn S) : ∑ c : CompIn S',
      (if compParent m c.1 = v.1 ∧ sel c then
        (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
          ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) else 0) ^ 2 ≤ (B * g) ^ 2 := by
    have he (c : CompIn S') (hp : compParent m c.1 = v.1) (hs : sel c) :
        (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
          ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) ≤ g := by
      dsimp only [π, σ]
      rw [marker_normalized_entry (Buffer.birth_compMass_pos hq hΛ law c.1).le
        (Buffer.birth_compMarker_pos hq hΛ law c.1).le, ← hp]
      simpa only [one_mul] using mul_le_mul
        (readout_ordinary_entry_le_one hq hΛ law hcH hηB hη m c.1) (hmarker c hs)
        (inv_nonneg.mpr (Buffer.birth_compMarker_pos hq hΛ law c.1).le) zero_le_one
    calc
      _ ≤ ∑ c : CompIn S', if compParent m c.1 = v.1 then g ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hp : compParent m c.1 = v.1
        · by_cases hs : sel c
          · simp only [hp, hs, and_self, ite_true]
            exact (sq_le_sq₀ (mul_nonneg (div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
              (inv_nonneg.mpr (Real.sqrt_nonneg _))) (Real.rpow_nonneg
                (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _)) hg).mpr (he c hp hs)
          · simp only [hp, hs, and_false, ite_false, ite_true, zero_pow (by decide : 2 ≠ 0)]
            exact sq_nonneg g
        · simp only [hp, false_and, ite_false, zero_pow (by decide : 2 ≠ 0), le_refl]
      _ = (((Finset.univ : Finset (CompIn S')).filter
          (fun c => compParent m c.1 = v.1)).card : ℝ) * g ^ 2 := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ B * g ^ 2 := mul_le_mul_of_nonneg_right
        (by dsimp only [B]; exact_mod_cast readout_indexed_fiber_card_le hm hold hsub v.1) (sq_nonneg g)
      _ ≤ _ := row_multiplicity_square hB
  have hn := readout_norm_of_supported_square_rows m (ocEpsilon q Λ (m - 1)) η ρ (B * g)
    (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le
    (mul_nonneg (zero_le_one.trans hB) hg) π σ hπ hσ
    (fun c => readout_parent_mem hm hold (hsub c.2)) sel hrow X hzero
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hB) hg) (Real.sqrt_nonneg _))).mpr hn
  simp only [one_pow, div_one] at hs
  change Real.sqrt (massNormSq ρ π
      (fun v => (succReadout m (ocEpsilon q Λ (m - 1)) η K X v).val)) ^ 2 ≤
    (B * g * Real.sqrt (massNormSq ρ σ (fun c => (X c).val))) ^ 2 at hs
  rw [mul_pow, Real.sq_sqrt (CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _),
    Real.sq_sqrt (CoupledEnergy.Variational.massNormSq_nonneg ρ σ hσ _)] at hs
  exact hs

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The marker-profile input supplies the complete pointwise readout ingredient, including
the exact raw realization and preservation of time integrability.

Special cases: empty and singleton families, identity metric, k=0, zero flux, J=0 and an
edgeless seed use the same finite-menu constant. No component norm is divided out. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Marker readout at fixed data from an inverse-marker profile on the selected rows. -/
theorem marker_readout_of_profile (F : Frame D hr Dm bw j₀)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hm : 1 ≤ F.m)
    (hcH : F.law.cH ≤ 1) (hηB : 0 ≤ F.law.etaB) (hη : 0 ≤ F.η)
    (A : Finset WordLetter)
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.m ≤ e.scale)
    (hsub : F.G'.comps ⊆ succExtComps F.m A F.J F.G.comps)
    (grade : Bool)
    (hmarker : ∀ c : CompIn F.G'.comps, F.select grade c.1 →
      (compMarker D.q D.Λ F.law c.1)⁻¹ ≤ F.markerGain grade) :
    MarkerReadoutStatement F grade ((wordsUpTo A (F.J + 1)).card + 1) := by
  classical
  intro OF hOF hOFlp
  let RF : F.ReadoutFlux := fun v t =>
    succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r))
      F.m (D.eps (F.m - 1)) F.η F.k (fun c => OF c t) v
  refine ⟨RF, realized_rows_readout F grade OF hOF, ?_, ?_⟩
  · intro v
    exact FullLift.memLp_succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) F.m (D.eps (F.m - 1)) F.η OF hOFlp v
  · intro t ht
    have hg : 0 ≤ F.markerGain grade := by
      cases grade <;> simp only [Frame.markerGain, Bool.false_eq_true, ite_false, ite_true]
      · exact zero_le_one
      · exact Real.rpow_nonneg (Scales.epsilon_basic (m := F.m - 1) hq hΛ).1.le _
    exact selected_readout_mass_square
      (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hq hΛ hm F.law hcH hηB hη
      hold hsub (fun c => F.select grade c.1) (F.markerGain grade) hg hmarker
      (rhoEnh D F.cr F.m) (fun c => OF c t)
      (fun c hc => realized_row_zero F grade OF hOF t ht c hc)

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! Uniform marker readout production, separately for either frontier. The finite-menu
constant and separation floor precede all stage, law, component and flux data.

Special cases: an edgeless seed has ordered empty histories; the first birth supplies its own
marker. EMPTY and singleton families, H=0, J=0, k=0, identity metric and zero flux use the
same constant. No coefficient estimate or time integrability is assumed outside the row input. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open FullLift

/-- The pointwise marker-readout estimate under the literal uniform frontier prefix. -/
theorem marker_readout_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (grade : Bool) :
    FrontierAnalyticProductionStatement α s q ζ grade (fun _rows readout _source => readout) := by
  classical
  have hη := successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  obtain ⟨ns, hsep⟩ := marker_scale_separation_threshold hq.1 hq.2.1 hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφpos _hφint _hφsupport bw _hbw _hbwupper Q T₀ _hQ _hT₀
    Ce τe kS r₀ D₀ _hCe _hτe _hc₀ _hc₀upper _hcr _hcrupper _hσf _hlamC
    H J N p nk _Lc _Lf _Lpr _Acl Naux Nout Kres npad sX sZ σ₀ _a _σ _hsched
    _hNaux _hNout _halloc _hsX _hsZ
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI _hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _hledger _hstart CQ Cpr
  refine ⟨(wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card + 1, ns + 2, ?_⟩
  intro D hDα hDq hDΛ _hDζ _hseq M _hband _hterm Mnat _hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK _hfresh seed _n _tS _tf hseed m hm _hn _hnM
    _tA _s₀ _htA _hdelay _hwindow _hT G G' hcascade hlevel _hG hactual
    tp _Preg _hprep _f _Ain _hf k _hk Y0 _Y Yw _Yk _htrace _hsol yom _hyom
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := _tf, Y0 := Y0, Yw := Yw, yom := yom }
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ
  have hm1 : 1 ≤ m := by omega
  have hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale := by
    intro v hv
    simpa only [hlevel] using (InitialValue.cascade_invariant hseed.2.1 hcascade v hv).1
  have hsub : G'.comps ⊆ succExtComps m (succAlphabetOf r₀ D₀ H J N p npad) J G.comps := by
    rw [hactual.2.2.1, hlevel]
    exact Finset.Subset.refl _
  have hpairs := extended_births_pairwise hseed.2.1 hcascade hactual
  obtain ⟨hcH, hηB, _hη0, hι⟩ := successor_readout_law_facts hη hlaw
  apply marker_readout_of_profile F hqD hΛD hm1 hcH hηB hη.le
    (succAlphabetOf r₀ D₀ H J N p npad) hold hsub grade
  intro c hsel
  cases grade with
  | false =>
    change (compMarker D.q D.Λ law c.1)⁻¹ ≤ 1
    exact (inv_le_one₀ (Buffer.birth_compMarker_pos hqD hΛD law c.1)).mpr
      (compMarker_one_le hqD hΛD law hι c.1)
  | true =>
    have hgrade : compGrade c.1 = H + 1 := hsel
    have hall : ∀ e ∈ c.1.births, m - 1 ≤ e.scale := by
      rcases InitialValue.mem_succExtComps (hsub c.2) with hc | ⟨v, hv, t, heq⟩
      · intro e he
        exact (Nat.sub_le _ _).trans (hold c.1 hc e he)
      · rw [heq]
        unfold succComp
        split_ifs
        · intro e he
          exact (Nat.sub_le _ _).trans (hold v hv e he)
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact le_rfl
          · exact (Nat.sub_le _ _).trans (hold v hv e he)
    have hsD : ∀ k, ns ≤ k → ocEpsilon D.q D.Λ (k + 1) ≤
        ocEpsilon D.q D.Λ k ^ ((1 + D.q) / 2) := by
      simpa only [hDq, hDΛ] using hsep
    have hg := inverse_marker_grade_bound hqD hΛD law hι hsD (by omega : ns ≤ m - 1)
      c.1 (hpairs c.1 c.2) hall
    simpa only [F, Frame.markerGain, Frame.exponent, ite_true, hgrade, hlaw.2.2.1,
      OCData.eps, succSigmaH, hDq] using hg

end AVRegularity.Construction.Preservation.Frontier
end
end
end
