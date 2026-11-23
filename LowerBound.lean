import Transport
import Scaling

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace O71
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

instance paramFiniteCompacts : IsFiniteMeasureOnCompacts (volume : Measure Param) := by
  let : IsFiniteMeasureOnCompacts (volume : Measure (ℝ × Triple)) := inferInstance
  let : IsFiniteMeasureOnCompacts (volume : Measure (ℝ × ℝ × Triple)) := inferInstance
  let : IsFiniteMeasureOnCompacts (volume : Measure (ℝ × ℝ × ℝ × Triple)) := inferInstance
  let : IsFiniteMeasureOnCompacts (volume : Measure (ℝ × ℝ × ℝ × ℝ × Triple)) := inferInstance
  infer_instance

instance paramOpenPos : Measure.IsOpenPosMeasure (volume : Measure Param) := by
  let : Measure.IsOpenPosMeasure (volume : Measure (ℝ × Triple)) := inferInstance
  let : Measure.IsOpenPosMeasure (volume : Measure (ℝ × ℝ × Triple)) := inferInstance
  let : Measure.IsOpenPosMeasure (volume : Measure (ℝ × ℝ × ℝ × Triple)) := inferInstance
  let : Measure.IsOpenPosMeasure (volume : Measure (ℝ × ℝ × ℝ × ℝ × Triple)) := inferInstance
  infer_instance

theorem chart_measurable (q : ℝ) : Measurable (scaledChart q) := by
  unfold scaledChart cMap tMap dMap pMap sMap rightJump leftJump
  fun_prop

theorem volume_scale (q : ℝ) (hq : 0 < q) (E : Set Param) (hE : MeasurableSet E) :
    volume E = ENNReal.ofReal (q^11) * volume (scaledChart q ⁻¹' E) := by
  have he := scaledChart_factor q hq (E.indicator 1) (measurable_const.indicator hE)
  rw [lintegral_indicator_one hE, abs_of_pos (pow_pos hq _)] at he
  rw [he, ← lintegral_indicator_one (hE.preimage (chart_measurable q))]
  rfl

theorem scaled_regular (q : ℝ) (w : Param) (hq : q ≠ 0) (hd : w.2.2.2.1 ≠ 0) :
    scaledChart q w = regular q w := by
  rcases w with ⟨a,c,t,D,p,v⟩
  exact chart_regular q a c t D p (v 0) (v 1) (v 2) hq hd

def anchor : Param := (fun _ => 1,0,0,1,1/2,fun _ => 0)

private theorem anchor_good :
    ∀ᶠ u : ℝ × Param in 𝓝 ((0:ℝ),anchor),
      0 < u.1 → scaledChart u.1 u.2 ∈ sublevel (u.1^6) := by
  let x : ℝ × Param := (0,anchor)
  have hd : x.2.2.2.2.1 ≠ 0 := by norm_num [x,anchor]
  have ha (i : Fin 3) : x.2.1 i ≠ 0 := by norm_num [x,anchor]
  have hb : ∀ᶠ u : ℝ × Param in 𝓝 x, radiusSq (regular u.1 u.2) < 1/9 :=
    (radiusSq_continuous.continuousAt.comp (regular_cont x ha hd)).eventually_lt continuousAt_const
      (by norm_num [Function.comp_def,x,anchor,radiusSq,regular,regularChart,Fin.sum_univ_three])
  have hK : ∀ᶠ u : ℝ × Param in 𝓝 x, normalizedLoss u.1 u.2 < 1 :=
    normalizedLoss_cont.continuousAt.eventually_lt continuousAt_const
      (by norm_num [x,anchor,normalizedLoss,scaledEnergy,mass])
  have hcoord {f : ℝ × Param → ℝ} (hf : Continuous f) (h : 0 < f x) :
      ∀ᶠ u in 𝓝 x, 0 < f u := continuousAt_const.eventually_lt hf.continuousAt h
  have hA : ∀ᶠ u : ℝ × Param in 𝓝 x, ∀ i, 0 < u.2.1 i := by
    apply (Filter.eventually_all).2
    intro i
    exact hcoord (f := fun u => u.2.1 i) (by fun_prop) (by norm_num [x,anchor])
  filter_upwards [hb,hK,hA,
    hcoord (f := fun u => u.2.2.2.2.1) (by fun_prop) (by norm_num [x,anchor]),
    hcoord (f := fun u => 1+u.2.2.2.1) (by fun_prop) (by norm_num [x,anchor]),
    hcoord (f := fun u => 1-(u.2.2.2.1+u.1^2*u.2.2.2.2.1)) (by fun_prop) (by norm_num [x,anchor]),
    hcoord (f := fun u => u.2.2.2.2.2.1) (by fun_prop) (by norm_num [x,anchor]),
    hcoord (f := fun u => 1-u.2.2.2.2.2.1) (by fun_prop) (by norm_num [x,anchor])]
    with u hb hK hA hD hl hr hp hp'
  intro hq
  rw [scaled_regular _ _ hq.ne' hD.ne']
  refine ⟨hb.le, ?_⟩
  rw [loss_scale _ _ hq hA (by linarith) hD ⟨hp.le,by linarith⟩ (by linarith)]
  exact mul_le_of_le_one_right (by positivity) hK.le

theorem coordinate_bounds (w : Param) (hw : radiusSq w ≤ 1/9) :
    (∀ i, |w.1 i-1| ≤ 1/3) ∧ |w.2.1| ≤ 1/3 ∧ |w.2.2.1| ≤ 1/3 ∧
    |w.2.2.2.1| ≤ 1/3 ∧ |w.2.2.2.2.1| ≤ 1/3 ∧ ∀ i, |w.2.2.2.2.2 i| ≤ 1/3 := by
  rcases w with ⟨a,c,b,e,f,v⟩
  simp only [radiusSq,Fin.sum_univ_three] at hw
  dsimp only
  have h (x : ℝ) (hx : x^2 ≤ 1/9) : |x| ≤ 1/3 := by nlinarith [sq_abs x,abs_nonneg x]
  have h₀ := sq_nonneg (a 0-1)
  have h₁ := sq_nonneg (a 1-1)
  have h₂ := sq_nonneg (a 2-1)
  have h₃ := sq_nonneg (v 0)
  have h₄ := sq_nonneg (v 1)
  have h₅ := sq_nonneg (v 2)
  have h₆ := sq_nonneg c
  have h₇ := sq_nonneg b
  have h₈ := sq_nonneg e
  have h₉ := sq_nonneg f
  refine ⟨?_,h _ ?_,h _ ?_,h _ ?_,h _ ?_,?_⟩ <;> try linarith
  all_goals intro i; fin_cases i <;> apply h <;> linarith!

theorem sublevel_finite (e : ℝ) : volume (sublevel e) ≠ ∞ := by
  apply ne_top_of_le_ne_top (isCompact_closedBall (0:Param) 2).measure_ne_top (measure_mono _)
  intro w hw
  obtain ⟨ha,hc,hb,he,hf,hv⟩ := coordinate_bounds w hw.1
  simp only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,
    pi_norm_le_iff_of_nonempty,Real.norm_eq_abs]
  refine ⟨?_,by linarith,by linarith,by linarith,by linarith,fun i => (hv i).trans (by norm_num)⟩
  intro i
  have H := abs_le.mp (ha i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem volume_lower : ∃ C : ℝ, 0 < C ∧ ∀ᶠ e : ℝ in 𝓝[>] 0,
    C * e^(11/6 : ℝ) ≤ (volume (sublevel e)).toReal := by
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp anchor_good
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hV
  let A := Metric.ball anchor r
  have hA : 0 < volume A := Metric.measure_ball_pos volume _ hr
  have hAf : volume A ≠ ∞ := (measure_ball_lt_top : volume A < ∞).ne
  refine ⟨(volume A).toReal,ENNReal.toReal_pos hA.ne' hAf,?_⟩
  have hroot : Tendsto (fun e : ℝ => e^(1/6 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1/6:ℝ))).continuousAt (x := (0:ℝ))
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  filter_upwards [hroot hU, self_mem_nhdsWithin] with e hqU he
  have he' : 0 < e := he
  let q := e^(1/6 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos he' _
  have h6 : q^6 = e := by
    dsimp [q]; rw [← Real.rpow_mul_natCast he'.le]; norm_num
  have h11 : q^11 = e^(11/6 : ℝ) := by
    dsimp [q]; rw [← Real.rpow_mul_natCast he'.le]; norm_num
  have hsub : A ⊆ scaledChart q ⁻¹' sublevel e := by
    intro w hw
    rw [← h6]
    apply hUV (show (q,w) ∈ U ×ˢ V from ⟨hqU,hball hw⟩)
    exact hq
  have hb : ENNReal.ofReal (q^11) * volume A ≤ volume (sublevel e) := by
    rw [volume_scale q hq _ (sublevel_measurable e)]
    exact mul_le_mul_right (measure_mono hsub) _
  have H := ENNReal.toReal_mono (sublevel_finite e) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hq 11).le,h11,mul_comm] at H
  exact H

end O71
