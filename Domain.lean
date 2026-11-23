import Sectors
import Envelope

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology ENNReal
namespace O71

def admiss (q : ℝ) : Set Param := {w | (∀ i, 0 < w.1 i) ∧ 0 < w.2.2.2.1 ∧
  w.2.2.2.2.1 ∈ Ioo 0 1 ∧ -(1/2) ≤ w.2.2.1 ∧ w.2.2.1+q^2*w.2.2.2.1 ≤ 1/2 ∧
  radiusSq (regular q w) ≤ 1/9 ∧ normalizedLoss q w ≤ 1}

theorem admiss_measurable (q : ℝ) : MeasurableSet (admiss q) := by
  have hA : MeasurableSet {w : Param | ∀ i, 0 < w.1 i} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i : Fin 3 => measurableSet_lt (measurable_const (a := (0:ℝ)))
      (show Measurable (fun w : Param => w.1 i) by fun_prop))
  have ht : Measurable (fun w : Param => w.2.2.1) := by fun_prop
  have hd : Measurable (fun w : Param => w.2.2.2.1) := by fun_prop
  have hp : Measurable (fun w : Param => w.2.2.2.2.1) := by fun_prop
  have hr : Measurable (regular q) := by unfold regular regularChart; fun_prop
  have hk : Measurable (normalizedLoss q) :=
    normalizedLoss_cont.measurable.comp (measurable_const.prodMk measurable_id)
  exact hA.inter ((measurableSet_lt measurable_const hd).inter ((measurableSet_Ioo.preimage hp).inter
    ((measurableSet_le measurable_const ht).inter ((measurableSet_le (ht.add (measurable_const.mul hd)) measurable_const).inter
    ((measurableSet_le (radiusSq_continuous.measurable.comp hr) measurable_const).inter
    (measurableSet_le hk measurable_const))))))

private theorem chart_knots (q : ℝ) (a : Triple) (c t D p : ℝ) (v : Triple)
    (ha : ∀ i, 0 < a i) :
    knots (scaledChart q (a,c,t,D,p,v)) = ![t,t+p*(q^2*D),t+q^2*D] := by
  funext i; fin_cases i <;> simp [knots,scaledChart,cMap,tMap,dMap,pMap, (ha _).ne', mul_div_cancel_left₀]

private theorem knot_range (w : Param) (h : radiusSq w ≤ 1/9) : ∀ i, |knots w i| ≤ 1/2 := by
  obtain ⟨ha,_,hb,he,hf,_⟩ := coordinate_bounds w h
  have aux (u b : ℝ) (hu : |u-1| ≤ 1/3) (hb : |b| ≤ 1/3) : |-b/u| ≤ 1/2 := by
    have H := abs_le.mp hu
    have hp : 0 < u := by linarith
    rw [abs_div,abs_neg,abs_of_pos hp,div_le_iff₀ hp]; linarith
  intro i; fin_cases i
  · exact aux _ _ (ha 0) hb
  · exact aux _ _ (ha 1) hf
  · exact aux _ _ (ha 2) he

theorem mem_admiss_iff (q : ℝ) (hq : 0 < q) (s : Bool) (w : Param)
    (hD₀ : w.2.2.2.1 ≠ 0) (hp₀ : w.2.2.2.2.1 ≠ 0) (hp₁ : w.2.2.2.2.1 ≠ 1) :
    scaledChart q w ∈ sector s (q^6) ↔ w ∈ admiss q := by
  rcases w with ⟨a,c,t,D,p,v⟩
  let w : Param := (a,c,t,D,p,v)
  change D ≠ 0 at hD₀
  change p ≠ 0 at hp₀
  change p ≠ 1 at hp₁
  have eqR : scaledChart q w = regular q w := scaled_regular q w hq.ne' hD₀
  have q2 := sq_pos_of_pos hq
  constructor
  · rintro ⟨⟨hb,hk⟩,hs⟩
    have hA (i : Fin 3) : 0 < a i := by
      have H : |a i-1| ≤ 1/3 := (coordinate_bounds _ hb).1 i
      linarith [(abs_le.mp H).1]
    have hh := chart_knots q a c t D p v hA
    have he : t ≤ t+p*(q^2*D) ∧ t+p*(q^2*D) ≤ t+q^2*D := by
      cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, hh] at hs
      · exact hs
      · exact ⟨hs.1.le,hs.2.le⟩
    have hD : 0 < D := by
      have hd : 0 ≤ q^2*D := by linarith [he.1,he.2]
      exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right hd q2) hD₀.symm
    have hd := mul_pos q2 hD
    have hp : 0 < p := lt_of_le_of_ne (nonneg_of_mul_nonneg_left (by linarith [he.1] : 0 ≤ p*(q^2*D)) hd) hp₀.symm
    have hp' : p < 1 := lt_of_le_of_ne ((mul_le_mul_iff_left₀ hd).mp
      (by linarith [he.2] : p*(q^2*D) ≤ 1*(q^2*D))) hp₁
    have ht := knot_range _ hb 0
    have hr := knot_range _ hb 2
    rw [hh] at ht hr
    have ht' : -(1/2) ≤ t := (abs_le.mp ht).1
    have hr' : t+q^2*D ≤ 1/2 := (abs_le.mp hr).2
    refine ⟨hA,hD,⟨hp,hp'⟩,ht',hr',eqR ▸ hb,?_⟩
    change loss (scaledChart q w) ≤ q^6 at hk
    rw [eqR,loss_scale q w hq hA (by change -1 ≤ t; linarith) hD ⟨hp.le,hp'.le⟩
      (by change t+q^2*D ≤ 1; linarith)] at hk
    exact le_of_mul_le_mul_left (by simpa using hk : q^6 * normalizedLoss q w ≤ q^6*1) (pow_pos hq _)
  · rintro ⟨hA,hD,⟨hp,hp'⟩,ht,hr,hb,hk⟩
    change -(1/2) ≤ t at ht
    change t+q^2*D ≤ 1/2 at hr
    change 0 < D at hD
    change 0 < p at hp
    change p < 1 at hp'
    constructor
    · change radiusSq (scaledChart q w) ≤ 1/9 ∧ loss (scaledChart q w) ≤ q^6
      rw [eqR,loss_scale q w hq hA (by change -1 ≤ t; linarith) hD ⟨hp.le,hp'.le⟩
        (by change t+q^2*D ≤ 1; linarith)]
      exact ⟨hb,mul_le_of_le_one_right (pow_pos hq _).le hk⟩
    · have he : t < t+p*(q^2*D) ∧ t+p*(q^2*D) < t+q^2*D := by
        have hd := mul_pos q2 hD
        constructor <;> nlinarith only [mul_pos hp hd,mul_pos (sub_pos.mpr hp') hd]
      cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true,chart_knots _ _ _ _ _ _ _ hA]
      · exact ⟨he.1.le,he.2.le⟩
      · exact he

private theorem aeTail {X Y : Type*} [MeasureSpace X] [MeasureSpace Y] [SFinite (volume : Measure Y)]
    {P : Y → Prop} (h : ∀ᵐ y, P y) : ∀ᵐ w : X × Y, P w.2 := quasiMeasurePreserving_snd.ae h
private theorem aeHead {X Y : Type*} [MeasureSpace X] [MeasureSpace Y] [SFinite (volume : Measure Y)]
    {P : X → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ w : X × Y, P w.1 := quasiMeasurePreserving_fst.ae h

theorem sublevel_volume_identity (q : ℝ) (hq : 0 < q) :
    volume (sublevel (q^6)) = 6 * (ENNReal.ofReal (q^11) * volume (admiss q)) := by
  have h (s : Bool) : volume (sector s (q^6)) = ENNReal.ofReal (q^11) * volume (admiss q) := by
    rw [volume_scale q hq _ (sector_measurable _ _)]
    congr 1
    apply measure_congr
    have hD : ∀ᵐ w : Param, w.2.2.2.1 ≠ 0 := aeTail (aeTail (aeTail (aeHead (volume.ae_ne 0))))
    have hp (k : ℝ) : ∀ᵐ w : Param, w.2.2.2.2.1 ≠ k := aeTail (aeTail (aeTail (aeTail (aeHead (volume.ae_ne k)))))
    filter_upwards [hD,hp 0,hp 1] with w hD hp₀ hp₁ using propext (mem_admiss_iff q hq s w hD hp₀ hp₁)
  have H := sector_sandwich (q^6)
  rw [h true,h false] at H
  exact le_antisymm H.2 H.1

def envelope : Set Param := Metric.closedBall (0:Triple) 2 ×ˢ (Icc (-4:ℝ) 4 ×ˢ (Icc (-1:ℝ) 1 ×ˢ tip))

theorem envelope_measurable : MeasurableSet envelope :=
  measurableSet_closedBall.prod (measurableSet_Icc.prod (measurableSet_Icc.prod tip_measurable))

theorem envelope_finite : volume envelope ≠ ∞ := by
  unfold envelope
  simp only [volume_eq_prod _ _, prod_prod]
  exact ENNReal.mul_ne_top (isCompact_closedBall _ _).measure_ne_top
    (ENNReal.mul_ne_top isCompact_Icc.measure_ne_top (ENNReal.mul_ne_top isCompact_Icc.measure_ne_top tip_finite))

theorem admiss_subset (q : ℝ) (hq : 0 < q) : admiss q ⊆ envelope := by
  rintro ⟨a,c,t,D,p,v⟩ ⟨ha,hD,hp,ht,hr,hb,hk⟩
  obtain ⟨ha',_,_,_,_,hv⟩ := coordinate_bounds _ hb
  have hA (i : Fin 3) : |a i - 1| ≤ 1/3 := ha' i
  have hZ : |v 0/a 1| ≤ 1/3 := hv 1
  have hA' (i : Fin 3) : |a i| ≤ 4/3 := by
    rw [abs_of_pos (ha i)]
    linarith [(abs_le.mp (hA i)).2]
  have hz : |v 0| < 1 := by
    rw [abs_div,div_le_iff₀ (abs_pos.mpr (ha 1).ne')] at hZ
    linarith [hA' 1]
  have H := coercive q c t D p (v 0) (v 1) (v 2) hD hp.1.le hp.2.le ht hr hk
  refine ⟨?_,abs_le.mp H.1,?_,?_⟩
  · simp only [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonempty,Real.norm_eq_abs]
    intro i; linarith [hA' i]
  · change -(1/2) ≤ t at ht
    change t+q^2*D ≤ 1/2 at hr
    have hd : 0 ≤ q^2*D := mul_nonneg (sq_nonneg _) hD.le
    exact ⟨by linarith,by linarith⟩
  · have he : v = ![v 0,v 1,v 2] := by funext i; fin_cases i <;> rfl
    change (D,p,v) ∈ tip
    rw [he]
    exact mem_tip hD hp.1 hp.2 hz (H.2.1.trans (by norm_num)) H.2.2.1 H.2.2.2

end O71
