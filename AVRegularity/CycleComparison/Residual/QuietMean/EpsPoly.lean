-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.QuietMean.CellMean

@[expose] public section

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity

/-! Jointly smooth periodic two-scale fields (`GoodField`) and the subclass with vanishing cell
mean (`CoefField True`), with closure under linear operations and partial derivatives. -/

/-- A two-scale field that is jointly `C^r` and `ℤ²`-periodic in the fast variable. -/
def GoodField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (Φ : Vec 2 → Vec 2 → E) : Prop :=
  ContDiff ℝ (r : ℕ∞) (Function.uncurry Φ) ∧ ∀ X, AVenhance.IsZ2Periodic (Φ X)

/-- A good field which, when `c` holds, has vanishing fast cell mean at every slow point. With
`c = True` this is a centred field; with `c = False` it is just a good field. -/
def CoefField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : Prop) (r : ℕ)
    (Φ : Vec 2 → Vec 2 → E) : Prop :=
  GoodField r Φ ∧ (c → ∀ X, fieldCellMean (Φ X) = 0)

section Good
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ} {Φ Ψ : Vec 2 → Vec 2 → E}

theorem GoodField.continuous (hΦ : GoodField r Φ) : Continuous (Function.uncurry Φ) :=
  hΦ.1.continuous

theorem GoodField.continuous_slice (hΦ : GoodField r Φ) (X : Vec 2) : Continuous (Φ X) :=
  hΦ.continuous.comp (continuous_const.prodMk continuous_id)

theorem GoodField.contDiff_slice (hΦ : GoodField r Φ) (X : Vec 2) : ContDiff ℝ (r : ℕ∞) (Φ X) :=
  hΦ.1.comp (contDiff_const.prodMk contDiff_id)

theorem GoodField.mono (hΦ : GoodField r Φ) {r' : ℕ} (h : r' ≤ r) : GoodField r' Φ :=
  ⟨hΦ.1.of_le (by exact_mod_cast h), hΦ.2⟩

theorem GoodField.zero : GoodField r (fun _ _ : Vec 2 => (0 : E)) :=
  ⟨contDiff_const, fun _ _ _ => rfl⟩

theorem GoodField.add (hΦ : GoodField r Φ) (hΨ : GoodField r Ψ) :
    GoodField r (fun X z => Φ X z + Ψ X z) :=
  ⟨hΦ.1.add hΨ.1, fun X n x => by simp [hΦ.2 X n x, hΨ.2 X n x]⟩

theorem GoodField.neg (hΦ : GoodField r Φ) : GoodField r (fun X z => -Φ X z) :=
  ⟨hΦ.1.neg, fun X n x => by simp [hΦ.2 X n x]⟩

theorem GoodField.smul (c : ℝ) (hΦ : GoodField r Φ) : GoodField r (fun X z => c • Φ X z) :=
  ⟨contDiff_const.smul hΦ.1, fun X n x => by simp [hΦ.2 X n x]⟩

theorem GoodField.mulX {g : Vec 2 → ℝ} (hg : ContDiff ℝ (r : ℕ∞) g) (hΦ : GoodField r Φ) :
    GoodField r (fun X z => g X • Φ X z) :=
  ⟨(hg.comp contDiff_fst).smul hΦ.1, fun X n x => by simp [hΦ.2 X n x]⟩

theorem GoodField.clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (hΦ : GoodField r Φ) : GoodField r (fun X z => L (Φ X z)) :=
  ⟨L.contDiff.comp hΦ.1, fun X n x => by simp [hΦ.2 X n x]⟩

theorem GoodField.sum {κ : Type*} (s : Finset κ) {Φ : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, GoodField r (Φ i)) : GoodField r (fun X z => ∑ i ∈ s, Φ i X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GoodField.zero (r := r) (E := E))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem GoodField.list_sum {κ : Type*} (l : List κ) {Φ : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, GoodField r (Φ i)) :
    GoodField r (fun X z => (l.map fun i => Φ i X z).sum) := by
  induction l with
  | nil => simpa using (GoodField.zero (r := r) (E := E))
  | cons a l ih =>
    have := (h a (List.mem_cons_self)).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

theorem GoodField.of_forall_apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : ∀ v, GoodField r (fun X z => Φ X z v)) : GoodField r Φ :=
  ⟨contDiff_pi.mpr fun v => (hΦ v).1, fun X n x => funext fun v => (hΦ v).2 X n x⟩

theorem GoodField.apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : GoodField r Φ) (v : ι) : GoodField r (fun X z => Φ X z v) :=
  hΦ.clm (ContinuousLinearMap.proj v)

theorem fderiv_fast_eq_comp {Φ : Vec 2 → Vec 2 → E} (hΦ : ContDiff ℝ 1 (Function.uncurry Φ))
    (X z : Vec 2) :
    fderiv ℝ (Φ X) z =
      (fderiv ℝ (Function.uncurry Φ) (X, z)).comp (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)) := by
  have h1 : HasFDerivAt (fun z' : Vec 2 => (X, z')) (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)) z :=
    ((hasFDerivAt_const X z).prodMk (hasFDerivAt_id z)).congr_fderiv (by ext <;> simp)
  have h2 := (hΦ.differentiable one_ne_zero (X, z)).hasFDerivAt.comp z h1
  exact h2.fderiv

theorem GoodField.slowPartial (hΦ : GoodField (r + 1) Φ) (i : Fin 2) :
    GoodField r (AVRegularity.slowPartial i Φ) := by
  refine ⟨?_, fun X n x => ?_⟩
  · have hc := hΦ.1.of_le (show (1 : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) by norm_cast; omega)
    have : Function.uncurry (AVRegularity.slowPartial i Φ) = fun u =>
        fderiv ℝ (Function.uncurry Φ) u (basisVec i, 0) := by
      funext u
      simp only [Function.uncurry, AVRegularity.slowPartial]
      rw [fderiv_slow_eq_comp hc u.1 u.2]
      simp
    rw [this]
    exact (hΦ.1.fderiv_right (m := (r : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  · simp only [AVRegularity.slowPartial]
    have : (fun X' => Φ X' (x + AVenhance.latticeShift n)) = fun X' => Φ X' x :=
      funext fun X' => hΦ.2 X' n x
    rw [this]

theorem GoodField.fastPartial (hΦ : GoodField (r + 1) Φ) (i : Fin 2) :
    GoodField r (AVRegularity.fastPartial i Φ) := by
  refine ⟨?_, fun X n x => ?_⟩
  · have hc := hΦ.1.of_le (show (1 : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) by norm_cast; omega)
    have : Function.uncurry (AVRegularity.fastPartial i Φ) = fun u =>
        fderiv ℝ (Function.uncurry Φ) u (0, basisVec i) := by
      funext u
      simp only [Function.uncurry, AVRegularity.fastPartial]
      rw [fderiv_fast_eq_comp hc u.1 u.2]
      simp
    rw [this]
    exact (hΦ.1.fderiv_right (m := (r : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  · simp only [AVRegularity.fastPartial]
    have e : (fun y => Φ X (y + AVenhance.latticeShift n)) = Φ X := funext (hΦ.2 X n)
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ X) (x := x) (AVenhance.latticeShift n)
    rw [e] at h
    rw [← h]

end Good

section Cent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop} {r : ℕ}
  {Φ Ψ : Vec 2 → Vec 2 → E}

theorem CoefField.zero : CoefField c r (fun _ _ : Vec 2 => (0 : E)) :=
  ⟨GoodField.zero, fun _ _ => fieldCellMean_zero⟩

theorem CoefField.mono (hΦ : CoefField c r Φ) {r' : ℕ} (h : r' ≤ r) : CoefField c r' Φ :=
  ⟨hΦ.1.mono h, hΦ.2⟩

theorem CoefField.add (hΦ : CoefField c r Φ) (hΨ : CoefField c r Ψ) :
    CoefField c r (fun X z => Φ X z + Ψ X z) :=
  ⟨hΦ.1.add hΨ.1, fun hc X => by
    rw [fieldCellMean_add (hΦ.1.continuous_slice X) (hΨ.1.continuous_slice X), hΦ.2 hc X,
      hΨ.2 hc X, add_zero]⟩

theorem CoefField.neg (hΦ : CoefField c r Φ) : CoefField c r (fun X z => -Φ X z) :=
  ⟨hΦ.1.neg, fun hc X => by rw [fieldCellMean_neg, hΦ.2 hc X, neg_zero]⟩

theorem CoefField.smul (a : ℝ) (hΦ : CoefField c r Φ) : CoefField c r (fun X z => a • Φ X z) :=
  ⟨hΦ.1.smul a, fun hc X => by rw [fieldCellMean_smul, hΦ.2 hc X, smul_zero]⟩

theorem CoefField.mulX {g : Vec 2 → ℝ} (hg : ContDiff ℝ (r : ℕ∞) g) (hΦ : CoefField c r Φ) :
    CoefField c r (fun X z => g X • Φ X z) :=
  ⟨hΦ.1.mulX hg, fun hc X => by rw [fieldCellMean_smul, hΦ.2 hc X, smul_zero]⟩

theorem CoefField.clm [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (L : E →L[ℝ] F) (hΦ : CoefField c r Φ) :
    CoefField c r (fun X z => L (Φ X z)) :=
  ⟨hΦ.1.clm L, fun hc X => by
    rw [fieldCellMean_clm L (hΦ.1.continuous_slice X), hΦ.2 hc X, map_zero]⟩

theorem CoefField.sum {κ : Type*} (s : Finset κ) {Φ : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, CoefField c r (Φ i)) : CoefField c r (fun X z => ∑ i ∈ s, Φ i X z) :=
  ⟨GoodField.sum s fun i hi => (h i hi).1, fun hc X => by
    rw [fieldCellMean_sum s fun i hi => (h i hi).1.continuous_slice X]
    exact Finset.sum_eq_zero fun i hi => (h i hi).2 hc X⟩

theorem CoefField.list_sum {κ : Type*} (l : List κ) {Φ : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, CoefField c r (Φ i)) :
    CoefField c r (fun X z => (l.map fun i => Φ i X z).sum) := by
  induction l with
  | nil => simpa using (CoefField.zero (c := c) (r := r) (E := E))
  | cons a l ih =>
    have := (h a (List.mem_cons_self)).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

theorem CoefField.fastPartial [CompleteSpace E] [FiniteDimensional ℝ E]
    (hΦ : CoefField c (r + 1) Φ) (i : Fin 2) : CoefField c r (AVRegularity.fastPartial i Φ) :=
  ⟨hΦ.1.fastPartial i, fun _ X => by
    have hd : ContDiff ℝ 1 (Φ X) := (hΦ.1.contDiff_slice X).of_le (by norm_cast; omega)
    exact fieldCellMean_fastPartial_eq_zero (Φ X) hd (hΦ.1.2 X) i⟩

theorem CoefField.slowPartial [CompleteSpace E] (hΦ : CoefField c (r + 1) Φ) (i : Fin 2) :
    CoefField c r (AVRegularity.slowPartial i Φ) :=
  ⟨hΦ.1.slowPartial i, fun hc X => by
    have hd : ContDiff ℝ 1 (Function.uncurry Φ) := hΦ.1.1.of_le (by norm_cast; omega)
    rw [fieldCellMean_slowPartial hd X i]
    have : (fun X' => fieldCellMean (Φ X')) = fun _ => (0 : E) := funext (hΦ.2 hc)
    rw [this]; simp⟩

end Cent

theorem CoefField.of_forall_apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]
    {c : Prop} {r : ℕ} {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : ∀ v, CoefField c r (fun X z => Φ X z v)) : CoefField c r Φ :=
  ⟨GoodField.of_forall_apply fun v => (hΦ v).1, fun hc X => by
    funext v
    have := fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (((GoodField.of_forall_apply fun v => (hΦ v).1 : GoodField r Φ)).continuous_slice X)
    simpa [(hΦ v).2 hc X, eq_comm] using this⟩

end AVRegularity
end

section
open MeasureTheory Homogenization
namespace AVRegularity

/-! At a quiet time (`√η v = 0`) the cell operators `ℬ₁`, `ℬ₂` map good fields to centred fields
(`ℬ₂` needs a centred input). -/

section CellB
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {Φ : Vec 2 → Vec 2 → E}

theorem GoodField.cent_fastPartial [FiniteDimensional ℝ E] {r : ℕ} {c : Prop}
    (hΦ : GoodField (r + 1) Φ) (i : Fin 2) :
    CoefField c r (AVRegularity.fastPartial i Φ) :=
  ⟨hΦ.fastPartial i, fun _ X => by
    have hd : ContDiff ℝ 1 (Φ X) := (hΦ.contDiff_slice X).of_le (by norm_cast; omega)
    exact fieldCellMean_fastPartial_eq_zero (Φ X) hd (hΦ.2 X) i⟩

theorem cellB1_centField [FiniteDimensional ℝ E] (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (hquiet : ∀ z k, Real.sqrt η * v t z k = 0) (hΦ : GoodField 2 Φ) :
    CoefField True 0 (cellB1 η G v t Φ) := by
  have hs : ∀ j, GoodField 1 (slowPartial j Φ) := fun j => hΦ.slowPartial j
  have hF1 : ∀ i j : Fin 2, CoefField True 0
      (fun X z => G t X i j • fastPartial i (slowPartial j Φ) X z) := fun i j =>
    (GoodField.cent_fastPartial (c := True) (hs j) i).mulX ((hG i j).of_le (by norm_num))
  have hF2 : ∀ i j : Fin 2, CoefField True 0
      (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z')) := fun i j =>
    CoefField.slowPartial (r := 0) ((GoodField.cent_fastPartial (c := True) (r := 1) hΦ j).mulX
      (hG i j)) i
  have hall := ((CoefField.sum (Finset.univ : Finset (Fin 2)) fun i _ =>
    CoefField.sum (Finset.univ : Finset (Fin 2)) fun j _ => (hF1 i j).add (hF2 i j))).smul
      (Real.sqrt η) |>.neg
  have e : cellB1 η G v t Φ = fun X z => -(Real.sqrt η • ∑ i : Fin 2, ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X z +
        slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)) := by
    funext X z
    simp only [cellB1, hquiet, zero_smul, Finset.sum_const_zero, zero_sub]
  rw [e]
  exact hall

theorem cellB2_centField (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j)) (hΦ : CoefField True 2 Φ) :
    CoefField True 0 (cellB2 η G t Φ) := by
  have hF : ∀ i j : Fin 2, CoefField True 0
      (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z')) := fun i j =>
    CoefField.slowPartial (r := 0) (((hΦ.slowPartial (r := 1) j)).mulX (hG i j)) i
  have hall := ((CoefField.sum (Finset.univ : Finset (Fin 2)) fun i _ =>
    CoefField.sum (Finset.univ : Finset (Fin 2)) fun j _ => hF i j)).smul η |>.neg
  exact hall

end CellB

end AVRegularity
end

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity

/-! Polynomials in the parameter `ε` with coefficients in `CoefField c r`: closure under the
linear operations and under `D_ε`, and the Taylor coefficients at `ε = 0`. -/

/-- A family `ε ↦ Ψ ε` of fields that is a polynomial of degree `≤ q` in `ε` whose coefficients are
centred good fields of regularity `r`. -/
def EpsPoly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : Prop) (q r : ℕ)
    (Ψ : ℝ → Vec 2 → Vec 2 → E) : Prop :=
  ∃ P : ℕ → Vec 2 → Vec 2 → E, (∀ i, CoefField c r (P i)) ∧ (∀ i, q < i → ∀ X z, P i X z = 0) ∧
    ∀ ε X z, Ψ ε X z = ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z

section EpsPoly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop} {q r : ℕ}
  {Ψ Ψ' : ℝ → Vec 2 → Vec 2 → E}

theorem EpsPoly.zero : EpsPoly c q r (fun _ _ _ => (0 : E)) :=
  ⟨fun _ _ _ => 0, fun _ => CoefField.zero, fun _ _ _ _ => rfl, fun ε X z => by simp⟩

theorem EpsPoly.mono_deg (h : EpsPoly c q r Ψ) {q' : ℕ} (hq : q ≤ q') : EpsPoly c q' r Ψ := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨P, hP, fun i hi => hz i (by omega), fun ε X z => ?_⟩
  rw [he]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hn => ?_
  simp only [Finset.mem_range] at hi hn
  rw [hz i (by omega), smul_zero]

theorem EpsPoly.mono_reg (h : EpsPoly c q r Ψ) {r' : ℕ} (hr : r' ≤ r) : EpsPoly c q r' Ψ := by
  obtain ⟨P, hP, hz, he⟩ := h
  exact ⟨P, fun i => ⟨(hP i).1.mono hr, (hP i).2⟩, hz, he⟩

theorem EpsPoly.add (h : EpsPoly c q r Ψ) (h' : EpsPoly c q r Ψ') :
    EpsPoly c q r (fun ε X z => Ψ ε X z + Ψ' ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := h
  obtain ⟨P', hP', hz', he'⟩ := h'
  refine ⟨fun i X z => P i X z + P' i X z, fun i => (hP i).add (hP' i),
    fun i hi X z => by simp [hz i hi, hz' i hi], fun ε X z => ?_⟩
  simp [he, he', Finset.sum_add_distrib]

theorem EpsPoly.neg (h : EpsPoly c q r Ψ) : EpsPoly c q r (fun ε X z => -Ψ ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨fun i X z => -P i X z, fun i => (hP i).neg, fun i hi X z => by simp [hz i hi], ?_⟩
  intro ε X z
  simp [he]

theorem EpsPoly.smul (a : ℝ) (h : EpsPoly c q r Ψ) : EpsPoly c q r (fun ε X z => a • Ψ ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨fun i X z => a • P i X z, fun i => (hP i).smul a, fun i hi X z => by simp [hz i hi], ?_⟩
  intro ε X z
  simp only [he, Finset.smul_sum, smul_comm a]

theorem EpsPoly.mulX {g : Vec 2 → ℝ} (hg : ContDiff ℝ (r : ℕ∞) g) (h : EpsPoly c q r Ψ) :
    EpsPoly c q r (fun ε X z => g X • Ψ ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨fun i X z => g X • P i X z, fun i => (hP i).mulX hg, fun i hi X z => by simp [hz i hi], ?_⟩
  intro ε X z
  simp only [he, Finset.smul_sum, smul_comm (g X)]

theorem EpsPoly.clm [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (L : E →L[ℝ] F) (h : EpsPoly c q r Ψ) :
    EpsPoly c q r (fun ε X z => L (Ψ ε X z)) := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨fun i X z => L (P i X z), fun i => (hP i).clm L, fun i hi X z => by simp [hz i hi], ?_⟩
  intro ε X z
  simp [he, map_sum, map_smul]

theorem EpsPoly.sum {κ : Type*} (s : Finset κ) {Ψ : κ → ℝ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, EpsPoly c q r (Ψ i)) : EpsPoly c q r (fun ε X z => ∑ i ∈ s, Ψ i ε X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (EpsPoly.zero (q := q) (r := r) (E := E))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem EpsPoly.list_sum {κ : Type*} (l : List κ) {Ψ : κ → ℝ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, EpsPoly c q r (Ψ i)) :
    EpsPoly c q r (fun ε X z => (l.map fun i => Ψ i ε X z).sum) := by
  induction l with
  | nil => simpa using (EpsPoly.zero (q := q) (r := r) (E := E))
  | cons a l ih =>
    have := (h a (List.mem_cons_self)).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

theorem EpsPoly.const {Φ : Vec 2 → Vec 2 → E} (hΦ : CoefField c r Φ) : EpsPoly c 0 r (fun _ => Φ) :=
  ⟨fun i => if i = 0 then Φ else fun _ _ => 0,
    fun i => by by_cases hi : i = 0 <;> simp [hi, hΦ, CoefField.zero],
    fun i hi X z => by simp [Nat.pos_iff_ne_zero.mp hi],
    fun ε X z => by simp⟩

end EpsPoly

theorem EpsPoly.of_forall_apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]
    {c : Prop} {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → ∀ i, h i}
    (hΨ : ∀ v, EpsPoly c q r (fun ε X z => Ψ ε X z v)) : EpsPoly c q r Ψ := by
  choose P hP hz he using hΨ
  refine ⟨fun i X z v => P v i X z, fun i => CoefField.of_forall_apply fun v => hP v i,
    fun i hi X z => funext fun v => hz v i hi X z, fun ε X z => funext fun v => ?_⟩
  simp [he v]


section DEpsPoly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop} {q r : ℕ}
  {Ψ : ℝ → Vec 2 → Vec 2 → E}

theorem fastPartial_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℝ) (P : κ → Vec 2 → Vec 2 → E)
    (hP : ∀ i ∈ s, GoodField 1 (P i)) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun X z => ∑ i ∈ s, c i • P i X z) X z =
      ∑ i ∈ s, c i • fastPartial k (P i) X z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => c i • P i X z') z := fun i hi =>
    (((hP i hi).contDiff_slice X).differentiable one_ne_zero z).const_smul (c i)
  simp only [fastPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_const_smul (((hP i hi).contDiff_slice X).differentiable one_ne_zero z)]
  rfl

theorem slowPartial_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℝ) (P : κ → Vec 2 → Vec 2 → E)
    (hP : ∀ i ∈ s, GoodField 1 (P i)) (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun X z => ∑ i ∈ s, c i • P i X z) X z =
      ∑ i ∈ s, c i • slowPartial k (P i) X z := by
  have hdd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => P i X' z) X := fun i hi =>
    ((((hP i hi).1.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero) X)
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => c i • P i X' z) X := fun i hi =>
    (hdd i hi).const_smul (c i)
  simp only [slowPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_const_smul (hdd i hi)]
  rfl

theorem fastPartial_zero (k : Fin 2) : fastPartial k (fun _ _ : Vec 2 => (0 : E)) = fun _ _ => 0 := by
  funext X z; simp [fastPartial]

theorem slowPartial_zero (k : Fin 2) : slowPartial k (fun _ _ : Vec 2 => (0 : E)) = fun _ _ => 0 := by
  funext X z; simp [slowPartial]

theorem EpsPoly.dEps [CompleteSpace E] [FiniteDimensional ℝ E] (η : ℝ) (k : Fin 2)
    (h : EpsPoly c q (r + 1) Ψ) : EpsPoly c (q + 1) r (fun ε => dEps η ε k (Ψ ε)) := by
  obtain ⟨P, hP, hz, he⟩ := h
  have hPz : ∀ i, q < i → P i = fun _ _ => 0 := fun i hi =>
    funext fun X => funext fun z => hz i hi X z
  refine ⟨fun i X z => fastPartial k (P i) X z +
      (if i = 0 then 0 else Real.sqrt η • slowPartial k (P (i - 1)) X z), fun i => ?_, ?_, ?_⟩
  · by_cases hi : i = 0
    · simpa [hi] using (hP i).fastPartial k
    · simpa [hi] using ((hP i).fastPartial k).add (((hP (i - 1)).slowPartial k).smul (Real.sqrt η))
  · intro i hi X z
    have h1 : fastPartial k (P i) X z = 0 := by
      rw [hPz i (by omega)]; simp [fastPartial]
    have h2 : slowPartial k (P (i - 1)) X z = 0 := by
      rw [hPz (i - 1) (by omega)]; simp [slowPartial]
    simp [h1, h2]
  · intro ε X z
    have hΨ : Ψ ε = fun X z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
      funext fun X => funext fun z => he ε X z
    have hg : ∀ i ∈ Finset.range (q + 1), GoodField 1 (P i) := fun i _ =>
      ((hP i).1.mono (by omega))
    simp only [AVRegularity.dEps, hΨ]
    rw [fastPartial_sum_smul _ _ _ hg, slowPartial_sum_smul _ _ _ hg]
    have hA : ∑ x ∈ Finset.range (q + 1 + 1), ε ^ x • fastPartial k (P x) X z =
        ∑ x ∈ Finset.range (q + 1), ε ^ x • fastPartial k (P x) X z := by
      rw [Finset.sum_range_succ _ (q + 1), hPz (q + 1) (by omega)]
      simp [fastPartial]
    have hB : ∑ x ∈ Finset.range (q + 1 + 1),
        ε ^ x • (if x = 0 then (0 : E) else Real.sqrt η • slowPartial k (P (x - 1)) X z) =
        (Real.sqrt η * ε) • ∑ x ∈ Finset.range (q + 1), ε ^ x • slowPartial k (P x) X z := by
      rw [Finset.sum_range_succ', Finset.smul_sum]
      simp only [Nat.add_one_ne_zero, ite_false, ite_true, smul_zero, add_zero, Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul]
      congr 1
      ring
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hA, hB]


theorem EpsPoly.foldl [CompleteSpace E] [FiniteDimensional ℝ E] (η : ℝ) (l : List (Fin 2)) :
    ∀ {q r : ℕ} (Ψ : ℝ → Vec 2 → Vec 2 → E), EpsPoly c q (r + l.length) Ψ →
      EpsPoly c (q + l.length) r
        (fun ε => l.foldl (fun Ψ' i => AVRegularity.dEps η ε i Ψ') (Ψ ε)) := by
  induction l with
  | nil => intro q r Ψ h; simpa using h
  | cons i l ih =>
    intro q r Ψ h
    have h' : EpsPoly c q ((r + l.length) + 1) Ψ := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h
    have h1 := h'.dEps η i
    have := ih (q := q + 1) (r := r) _ h1
    exact this.mono_deg (by simp; omega)

theorem EpsPoly.dEpsWord [CompleteSpace E] [FiniteDimensional ℝ E] (η : ℝ) {m : ℕ}
    (α : AVRegularity.Sobolev.DerivativeWord2 m) (h : EpsPoly c q (r + m) Ψ) :
    EpsPoly c (q + m) r (fun ε => AVRegularity.dEpsWord η ε α (Ψ ε)) := by
  have := EpsPoly.foldl η (List.ofFn α) Ψ (by simpa using h)
  simp only [List.length_ofFn] at this
  exact this

end DEpsPoly

theorem iteratedDeriv_epsPoly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q j : ℕ)
    (c : ℕ → E) :
    iteratedDeriv j (fun ε : ℝ => ∑ i ∈ Finset.range (q + 1), ε ^ i • c i) 0 =
      if j ≤ q then (j.factorial : ℝ) • c j else 0 := by
  have hcd : ∀ i ∈ Finset.range (q + 1),
      ContDiffAt ℝ (j : WithTop ℕ∞) (fun ε : ℝ => ε ^ i • c i) 0 := fun i _ =>
    ((contDiff_id.pow i).smul contDiff_const).contDiffAt
  rw [iteratedDeriv_fun_sum hcd]
  have : ∀ i ∈ Finset.range (q + 1), iteratedDeriv j (fun ε : ℝ => ε ^ i • c i) 0 =
      if j = i then (i.factorial : ℝ) • c i else 0 := by
    intro i _
    rw [iteratedDeriv_smul_const (contDiff_id.pow i).contDiffAt (c i), iteratedDeriv_fun_pow_zero]
    by_cases h : j = i <;> simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  simp

end AVRegularity
end
