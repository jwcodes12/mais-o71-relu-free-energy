import Domain

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace O71

private def Stable (P : ℝ → Prop) :=
  (∀ᶠ q in 𝓝[>] 0, P q) ∨ (∀ᶠ q in 𝓝[>] 0, ¬ P q)

private theorem stable_const (p : Prop) : Stable (fun _ => p) := by
  by_cases h : p
  · exact Or.inl (Eventually.of_forall (fun _ => h))
  · exact Or.inr (Eventually.of_forall (fun _ => h))

private theorem stable_and {P Q : ℝ → Prop} (h : Stable P) (k : Stable Q) :
    Stable (fun q => P q ∧ Q q) := by
  rcases h with h|h
  · rcases k with k|k
    · exact Or.inl (h.and k)
    · exact Or.inr (k.mono (fun _ hk H => hk H.2))
  · exact Or.inr (h.mono (fun _ hp H => hp H.1))

/-- Along a positive ray, a real analytic inequality has an eventually constant truth value,
including when the limiting value is on the boundary. -/
private theorem analytic_le {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) : Stable (fun q => f q ≤ 0) := by
  by_cases hz : ∀ᶠ q in 𝓝 0, f q = 0
  · exact Or.inl ((hz.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le)
  obtain ⟨n,g,hg,h₀,he⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
  have hpos : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 < q := self_mem_nhdsWithin
  rcases lt_or_gt_of_ne h₀ with h|h
  · left
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,hpos,
      (hg.continuousAt.eventually_lt continuousAt_const h).filter_mono nhdsWithin_le_nhds] with q he hq hg
    simpa [he] using (mul_nonpos_of_nonneg_of_nonpos (pow_pos hq n).le hg.le : q^n*g q ≤ 0)
  · right
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,hpos,
      (continuousAt_const.eventually_lt hg.continuousAt h).filter_mono nhdsWithin_le_nhds] with q he hq hg
    simpa [he] using (mul_pos (pow_pos hq n) hg : 0 < q^n*g q)

private theorem stable_le_const {f : ℝ → ℝ} (c : ℝ) (hf : AnalyticAt ℝ f 0) :
    Stable (fun q => f q ≤ c) := by simpa only [Pi.sub_apply,sub_nonpos] using analytic_le (hf.sub (analyticAt_const (v := c)))

private theorem admiss_stable (w : Param) : Stable (fun q => w ∈ admiss q) := by
  rcases w with ⟨a,c,t,D,p,v⟩
  apply stable_and (stable_const _)
  apply stable_and (stable_const _)
  apply stable_and (stable_const _)
  apply stable_and (stable_const _)
  apply stable_and (stable_le_const _ (by fun_prop))
  apply stable_and (stable_le_const _ ?_) (stable_le_const _ ?_)
  · simp [regular,regularChart,radiusSq,Fin.sum_univ_three,div_eq_mul_inv]; fun_prop
  · unfold normalizedLoss scaledEnergy mass; dsimp only; fun_prop

private def sample (n : ℕ) : ℝ := (n : ℝ)⁻¹
private theorem sample_tendsto : Tendsto sample atTop (𝓝[>] 0) :=
  tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop

/-- The limiting constant is obtained by integrating the pointwise limiting indicator. -/
def limitSet : Set Param := liminf (fun n => admiss (sample n)) atTop

theorem admiss_limit : Tendsto (fun q => volume (admiss q)) (𝓝[>] 0) (𝓝 (volume limitSet)) := by
  have hq : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 < q := self_mem_nhdsWithin
  apply tendsto_measure_of_ae_tendsto_indicator _ (MeasurableSet.measurableSet_liminf (fun _ => admiss_measurable _))
    admiss_measurable envelope_measurable envelope_finite
    (hq.mono admiss_subset)
  apply ae_of_all; intro w
  rcases admiss_stable w with h|h
  · have H : w ∈ limitSet := mem_liminf_iff_eventually_mem.mpr (sample_tendsto.eventually h)
    exact h.mono (fun _ hq => iff_of_true hq H)
  · have H : w ∉ limitSet := by
      intro hmem
      obtain ⟨n,hn,hn'⟩ := ((mem_liminf_iff_eventually_mem.mp hmem).and (sample_tendsto.eventually h)).exists
      exact hn' hn
    exact h.mono (fun _ hq => iff_of_false hq H)

theorem limitSet_finite : volume limitSet ≠ ∞ := by
  apply ne_top_of_le_ne_top envelope_finite (measure_mono _)
  intro w hw
  obtain ⟨n, hn, hw⟩ := ((mem_liminf_iff_eventually_mem.mp hw).and
    (sample_tendsto.eventually (self_mem_nhdsWithin : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 < q))).exists
  exact admiss_subset _ hw hn

theorem volume_asymptotic : volumeLaw := by
  have hroot : Tendsto (fun e : ℝ => e^(1/6 : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1/6:ℝ))).continuousAt (x := (0:ℝ))
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with e he using Real.rpow_pos_of_pos he _
  let C := 6*(volume limitSet).toReal
  have hlim : Tendsto (fun e : ℝ => (volume (sublevel e)).toReal / e^(11/6:ℝ)) (𝓝[>] 0) (𝓝 C) := by
    apply ((ENNReal.tendsto_toReal limitSet_finite |>.comp (admiss_limit.comp hroot)).const_mul 6).congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : 0 < e := he
    let q := e^(1/6 : ℝ)
    have hq : 0 < q := Real.rpow_pos_of_pos he' _
    have h6 : q^6 = e := by dsimp [q]; rw [← Real.rpow_mul_natCast he'.le]; norm_num
    have h11 : q^11 = e^(11/6:ℝ) := by dsimp [q]; rw [← Real.rpow_mul_natCast he'.le]; norm_num
    have H := congrArg ENNReal.toReal (sublevel_volume_identity q hq)
    rw [h6,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_pos hq 11).le] at H
    change 6*(volume (admiss q)).toReal = _
    rw [H,← h11]
    norm_num
    field_simp
  obtain ⟨L,hL,hb⟩ := volume_lower
  have hLC : L ≤ C := ge_of_tendsto hlim (by
    filter_upwards [hb,(self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e)] with e h he
    exact (le_div_iff₀ (Real.rpow_pos_of_pos he _)).mpr h)
  exact ⟨C,lt_of_lt_of_le hL hLC,hlim⟩

#print axioms volume_asymptotic
end O71
