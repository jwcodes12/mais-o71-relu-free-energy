import Geometry
import Likelihood

noncomputable section
open MeasureTheory Real Set Filter ProbabilityTheory
open scoped ENNReal Topology
namespace O71
abbrev small : ℝ := 1/100
abbrev coordT (w : Param) := w.2.2.1
abbrev chartNet (q : ℝ) (w : Param) := net (scaledChart q w)

def box (L : ℝ) : Set Param :=
  Icc (fun _ : Fin 3 => (1:ℝ)) (fun _ => 1+small) ×ˢ Icc 0 small ×ˢ Icc 0 small ×ˢ
  Icc 1 (1+L) ×ˢ Icc 0 1 ×ˢ Icc (fun _ => 0) (fun _ => small)

theorem box_meas (L : ℝ) : MeasurableSet (box L) := by unfold box; measurability

theorem box_volume (L : ℝ) : volume (box L) = ENNReal.ofReal (small^8) * ENNReal.ofReal L := by
  simp only [box,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc_pi,Real.volume_Icc,
    Fin.prod_univ_three,add_sub_cancel_left,add_sub_cancel_right,sub_zero]
  rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ small)]
  simp only [ENNReal.ofReal_one]
  ring

theorem box_pos {L : ℝ} (h : 0 < L) : 0 < volume (box L) := by rw [box_volume]; positivity
abbrev boxLaw (L : ℝ) := ProbabilityTheory.cond volume (box L)
instance {L : ℝ} [Fact (0 < L)] : IsProbabilityMeasure (boxLaw L) :=
  cond_isProbabilityMeasure_of_finite (box_pos Fact.out).ne' (by rw [box_volume]; finiteness)

theorem scaled_chart_eq (q : ℝ) (a : Triple) (c t D p : ℝ) (v : Triple) :
    scaledChart q (a,c,t,D,p,v) = chart a (q^3*c) t (q^2*D) p (v 0) (q^3*v 1) (q^3*v 2) := rfl

theorem box_geometry {q L : ℝ} (hq : 0 < q) (hq' : q ≤ 1) (hdmax : q^2*(1+L) ≤ small)
    {w : Param} (hw : w ∈ box L) :
    radiusSq (scaledChart q w) ≤ 1/9 ∧
    ∀ x ∈ Icc (-1:ℝ) 1, |chartNet q w x| ≤ (7+2*(1+L))*q^2 ∧
      (x ∉ Icc (coordT w) (coordT w+q^2*(1+L)) → |chartNet q w x| ≤ 7*q^3) := by
  have hsm : small = 1/100 := rfl
  rcases w with ⟨a,c,t,D,p,v⟩
  obtain ⟨ha,hc,ht,hD,hp,hv⟩ := hw
  change a ∈ Icc (fun _ => (1:ℝ)) (fun _ => 1+small) at ha
  change v ∈ Icc (fun _ => (0:ℝ)) (fun _ => small) at hv
  change c ∈ Icc 0 small at hc
  change t ∈ Icc 0 small at ht
  change D ∈ Icc 1 (1+L) at hD
  change p ∈ Icc (0:ℝ) 1 at hp
  let d := q^2*D
  have hd : 0 < d := mul_pos (by positivity) (by linarith [hD.1])
  have hd₁ : d ≤ q^2*(1+L) := mul_le_mul_of_nonneg_left hD.2 (sq_nonneg _)
  have hd₂ : d ≤ small := hd₁.trans hdmax
  have hq3 : q^3 ≤ 1 := pow_le_one₀ hq.le hq'
  have hq32 : q^3 ≤ q^2 := by simpa [pow_succ] using mul_le_of_le_one_right (sq_nonneg q) hq'
  have hdq : q^3 ≤ d := hq32.trans (le_mul_of_one_le_right (sq_nonneg q) hD.1)
  have hs (i : Fin 3) : |q^3*v i| ≤ q^3 := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (hv.1 i))]
    exact mul_le_of_le_one_right (by positivity) ((hv.2 i).trans (by norm_num))
  have ha' (i : Fin 3) : 0 < a i := lt_of_lt_of_le zero_lt_one (ha.1 i)
  let l := leftJump t d p (v 0) (q^3*v 1) (q^3*v 2)
  have hn : 0 ≤ (q^3*v 2 + q^3*v 1*(t+d))/d := by
    apply div_nonneg _ hd.le
    positivity [hv.1 (1:Fin 3),hv.1 (2:Fin 3),ht.1]
  have htop : q^3*v 2 + q^3*v 1*(t+d) ≤ d*(2*small) := by
    have h1 : q^3*v 2 ≤ d*small := mul_le_mul hdq (hv.2 _) (hv.1 _) (by positivity)
    have h2 : q^3*v 1 ≤ d*small := mul_le_mul hdq (hv.2 _) (hv.1 _) (by positivity)
    have h3 : q^3*v 1*(t+d) ≤ q^3*v 1 := mul_le_of_le_one_right
      (mul_nonneg (by positivity) (hv.1 _)) ((add_le_add ht.2 hd₂).trans (by norm_num : small+small ≤ 1))
    linarith
  have hvp : v 0*(1-p) ∈ Icc 0 small :=
    ⟨mul_nonneg (hv.1 _) (by linarith [hp.2]),(mul_le_of_le_one_right (hv.1 _) (by linarith [hp.1])).trans (hv.2 _)⟩
  have hl : |l| ≤ 2*small := by
    have hh := (div_le_iff₀ hd).mpr (by linarith only [htop] :
      q^3*v 2+q^3*v 1*(t+d) ≤ 2*small*d)
    change |(q^3*v 2+q^3*v 1*(t+d))/d-v 0*(1-p)| ≤ _; apply abs_le.mpr; constructor
    · exact (show -(2*small) ≤ 0-small by norm_num [small]).trans (sub_le_sub hn hvp.2)
    · linarith only [hh,hvp.1]
  have hS := mul_le_mul hq3 (hv.2 (1:Fin 3)) (hv.1 _) zero_le_one
  have hr : |rightJump t d p (v 0) (q^3*v 1) (q^3*v 2)| ≤ 4*small := by
    change |q^3*v 1-l-v 0| ≤ _
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hl).1,(abs_le.mp hl).2,hv.1 (0:Fin 3),hv.2 (0:Fin 3),
      mul_nonneg (pow_nonneg hq.le 3) (hv.1 (1:Fin 3))]
  constructor
  · have haSq (i : Fin 3) : (a i-1)^2 ≤ small^2 := by
      apply pow_le_pow_left₀ (by linarith [ha.1 i]) (by linarith [ha.2 i])
    have htime : t+d ≤ 2*small := by linarith [ht.2]
    have ht0 := add_nonneg ht.1 hd.le
    have hpd : 0 ≤ p*d := mul_nonneg hp.1 hd.le
    have hpd' : p*d ≤ d := mul_le_of_le_one_left hd.le hp.2
    have hbi (i : Fin 3) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 2*small) :
        (-a i*u)^2 ≤ (3*small)^2 := by
      rw [neg_mul,neg_sq]
      apply pow_le_pow_left₀ (mul_nonneg (ha' i).le hu)
      have H := mul_le_mul (ha.2 i) hu' hu (by norm_num : 0 ≤ 1+small)
      norm_num [small] at H ⊢
      exact H.trans (by norm_num)
    have hvv (i : Fin 3) (u : ℝ) (hu : |u| ≤ 4*small) : (u/a i)^2 ≤ (4*small)^2 := by
      rw [← sq_abs, abs_div,abs_of_pos (ha' i)]
      exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (ha' i).le) ((div_le_iff₀ (ha' i)).mpr <|
        hu.trans (le_mul_of_one_le_right (by norm_num) (ha.1 i))) _
    have hcc : (q^3*c)^2 ≤ small^2 := by
      apply pow_le_pow_left₀ (mul_nonneg (by positivity) hc.1)
      simpa using mul_le_mul hq3 hc.2 hc.1 zero_le_one
    rw [scaled_chart_eq]
    change radiusSq (chart a (q^3*c) t d p (v 0) (q^3*v 1) (q^3*v 2)) ≤ _
    simp [radiusSq,chart,Fin.sum_univ_three]
    simp only [neg_mul,neg_sq] at hbi
    have ha3 := add_le_add (add_le_add (haSq 0) (haSq 1)) (haSq 2)
    have hb0 := hbi 0 t ht.1 (ht.2.trans (by norm_num))
    have hb2 := hbi 2 (t+d) ht0 htime
    have hb1 := hbi 1 (t+p*d) (add_nonneg ht.1 hpd) ((add_le_add_right hpd' t).trans htime)
    have hw0 := hvv 0 l (hl.trans (by norm_num))
    have hw1 := hvv 1 (v 0) (by rw [abs_of_nonneg (hv.1 _)]; exact (hv.2 _).trans (by norm_num))
    have hw2 := hvv 2 _ hr
    have H := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ha3 hcc) hb0) hb2) hb1)
      (add_le_add (add_le_add hw0 hw1) hw2)
    exact H.trans (by norm_num [small])
  · intro x hx
    change |net (chart a (q^3*c) t d p (v 0) (q^3*v 1) (q^3*v 2)) x| ≤ _ ∧ _
    have hc3 : |q^3*c| ≤ q^3 := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) hc.1)]
      exact mul_le_of_le_one_right (by positivity) (hc.2.trans (by norm_num))
    have hm := macro_bound hq.le hd (hd₂.trans (by norm_num))
      (t := t) (x := x) (by rw [abs_of_nonneg ht.1]; exact ht.2.trans (by norm_num)) (abs_le.mpr hx)
      (c := q^3*c) hc3
      (hs 1) (hs 2)
    have hb : |v 0*bump t d p x| ≤ 2*d := by
      rw [abs_mul,abs_of_nonneg (hv.1 _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) ((hv.2 _).trans (by norm_num))).trans (bump_bound hd.le hp)
    have he := chart_split a ha' (q^3*c) t d p (v 0) (q^3*v 1) (q^3*v 2) x hd.ne'
    constructor
    · rw [he]
      linarith [abs_add_le (q^3*c + (q^3*v 2+q^3*v 1*(t+d))*ramp t d x +
        q^3*v 1*max (x-(t+d)) 0) (v 0*bump t d p x)]
    · intro h
      change x ∉ Icc t (t+q^2*(1+L)) at h
      change |net (chart a (q^3*c) t d p (v 0) (q^3*v 1) (q^3*v 2)) x| ≤ _
      rwa [he,bump_off hd.le hp (fun hx' => h ⟨hx'.1,by linarith [hx'.2]⟩),mul_zero,add_zero]
end O71
